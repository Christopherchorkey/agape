"""
spin_swarm_harness.py
========================
Spin-based swarm simulation harness -- sparse-kernel, checkpointed, memory-conscious.
Designed to run comfortably on a 4GB RAM laptop at N in the hundreds-to-low-thousands.

Continues the brackish_meta lineage but uses spin-based naming:
  - Kuramoto-Sakaguchi phase coupling (bare sinusoid, shift by continuous polarity)
  - Mobility (Stage 1): spin nodes drift toward resonant neighbors, away from dissonant ones
  - Productivity-weighted resource sharing: flow is biased by each node's own EMA of |driver|
  - Protected consolidation variable: once a frustrated node's consolidation is high,
    its identity resists homeostatic erosion (glassy state)

MEMORY STRATEGY:
  - Every per-node array is float32, not float64.
  - No N x N dense matrices anywhere. All coupling/resource exchange goes
    through scipy.cKDTree ball-queries -> sparse pair lists.
  - NOTHING per-step is retained across the whole run. Only scalar summaries
    are logged (downsampled, every `log_every` steps).
  - Checkpoint/resume: state is a flat dict of small arrays + scalars, pickled.

USAGE
  python spin_swarm_harness.py --n 500 --steps 20000 --out run1
  python spin_swarm_harness.py --resume run1/checkpoint.pkl --steps 20000 --out run1
"""

import numpy as np
from scipy.spatial import cKDTree
import pickle, json, os, time, argparse

# ============================================================================
# PART 1: physics primitives (float32 throughout)
# ============================================================================

def smooth_attenuation(x):
    return 1.0 / (1.0 + np.exp(np.clip(x, -60, 60)))

def resonance_field(phase_diff):
    """Reused verbatim (shape) from Core.txt -- used only for the alpha growth
    driver and observables, not for the phase-coupling force itself (that's the
    bare Sakaguchi sinusoid)."""
    c = np.cos(phase_diff)
    return (1 + c) / 2.0 * (1.0 / (1.0 + np.exp(np.clip(-8 * c, -60, 60))))

# ============================================================================
# PART 2: state -- flat, float32, O(N) only
# ============================================================================

def init_state(n, L=40.0, seed=0, K=5.0, alpha_min=0.05):
    rng = np.random.default_rng(seed)
    dtype = np.float32

    # Exponential-tail spatial seeding: spin-up clustered near 0, spin-down near L
    side = rng.choice([0, 1], size=n)  # 0=spin-up-leaning, 1=spin-down-leaning
    pos = np.where(
        side == 0,
        np.abs(rng.exponential(scale=L * 0.15, size=n)),
        L - np.abs(rng.exponential(scale=L * 0.15, size=n)),
    ).astype(dtype)
    pos = np.clip(pos, 0, L)

    # Continuous polarity, RANDOM init
    pol = rng.choice([-1.0, 1.0], size=n).astype(dtype)

    phase = rng.uniform(0, 2 * np.pi, size=n).astype(dtype)
    alpha = np.full(n, 1.0, dtype=dtype)
    resource = np.full(n, 0.5, dtype=dtype)
    productivity_ema = np.full(n, 0.1, dtype=dtype)

    # Spin layer state -- starts empty, populated by classify_layers()
    consolidation = np.zeros(n, dtype=dtype)   # protected-memory variable
    overlap_ema = np.zeros(n, dtype=dtype)     # tracks sustained spin-up/spin-down tension
    is_frustrated = np.zeros(n, dtype=bool)    # spin boundary nodes
    is_glassy = np.zeros(n, dtype=bool)        # stable, memory-protected nodes

    return dict(
        n=n, L=np.float32(L), K=np.float32(K), alpha_min=np.float32(alpha_min),
        pos=pos, pol=pol, phase=phase, alpha=alpha, resource=resource,
        productivity_ema=productivity_ema, consolidation=consolidation,
        overlap_ema=overlap_ema, is_frustrated=is_frustrated, is_glassy=is_glassy,
        step=0, seed=seed,
    )

# ============================================================================
# PART 3: sparse neighbor structure -- rebuilt periodically, never dense
# ============================================================================

def build_neighbors(pos, radius, max_neighbors=24):
    """Returns a ragged list of neighbor-index arrays via cKDTree ball query."""
    tree = cKDTree(pos[:, None])
    pairs = tree.query_ball_point(pos[:, None], r=radius)
    n = len(pos)
    rng = np.random.default_rng(0)
    neigh = []
    for i in range(n):
        cand = [j for j in pairs[i] if j != i]
        if len(cand) > max_neighbors:
            cand = list(rng.choice(cand, size=max_neighbors, replace=False))
        neigh.append(np.array(cand, dtype=np.int32))
    return neigh

# ============================================================================
# PART 4: one integration step
# ============================================================================

def step(state, neigh, dt=0.05, coupling_gain=1.0, D_share=0.02,
         mobility_gain=0.02, mobility_on=True,
         shore_pull=0.01, alpha_decay=0.01, alpha_eta=0.01,
         consolidation_rate=0.0008, consolidation_protect=0.9):
    n = state["n"]
    pos, pol, phase, alpha = state["pos"], state["pol"], state["phase"], state["alpha"]
    resource, prod_ema = state["resource"], state["productivity_ema"]
    consolidation, overlap_ema = state["consolidation"], state["overlap_ema"]
    K, L = state["K"], state["L"]

    dphase = np.zeros(n, dtype=np.float32)
    dpos = np.zeros(n, dtype=np.float32)
    driver = np.zeros(n, dtype=np.float32)
    tension = np.zeros(n, dtype=np.float32)

    # Sakaguchi shift: continuous function of polarity, 0 at pol=+1, pi at pol=-1
    shift = np.pi * (1.0 - pol) / 2.0

    for i in range(n):
        js = neigh[i]
        if len(js) == 0:
            continue
        dx = np.abs(pos[js] - pos[i])
        w = np.exp(-dx / 4.0)

        dphi = phase[js] - phase[i]
        force = alpha[js] * w * np.sin(dphi - shift[i])
        net_force = force.sum()
        dphase[i] = coupling_gain * net_force

        driver[i] = np.abs(net_force)

        # local tension: spin-up/spin-down disagreement weighted by resonance
        res = resonance_field(dphi)
        opp_mask = (np.sign(pol[js]) != np.sign(pol[i])) & (np.abs(pol[js]) > 0.3)
        if opp_mask.any():
            tension[i] = (res[opp_mask] * w[opp_mask]).mean()

        if mobility_on:
            # drift toward resonant neighbors, away from dissonant ones
            sign_dx = np.sign(pos[js] - pos[i])
            dpos[i] = mobility_gain * (res * sign_dx).mean()

    # --- resource: productivity-weighted diffusion + boundary replenishment ---
    dres = np.zeros(n, dtype=np.float32)
    for i in range(n):
        js = neigh[i]
        if len(js) == 0:
            continue
        dx = np.abs(pos[js] - pos[i])
        w = np.exp(-dx / 4.0)
        flow = D_share * (prod_ema[i] * (w * resource[js]).sum()
                           - resource[i] * (w * prod_ema[js]).sum())
        dres[i] = flow

    # Spin-up source at x=0, spin-down source at x=L
    spin_up_src = shore_pull * np.clip(1 - pos / (0.15 * L), 0, 1)
    spin_down_src = shore_pull * np.clip(1 - (L - pos) / (0.15 * L), 0, 1)
    dres += spin_up_src + spin_down_src - 0.01 * resource

    # --- alpha: logistic-capped growth driven by (resource-gated) driver ---
    g = driver / (driver.mean() + 1e-6)
    dalpha = alpha_eta * alpha * (resource * g - alpha_decay) * (1 - alpha / K)

    # --- productivity EMA (drives resource sharing) ---
    dprod = 0.05 * (driver - prod_ema)

    # --- frustrated/glassy consolidation ---
    doverlap = 0.02 * (tension - overlap_ema)
    dconsol = consolidation_rate * (overlap_ema - consolidation)

    # --- apply ---
    state["phase"] = (phase + dt * dphase) % (2 * np.float32(np.pi))
    state["pos"] = np.clip(pos + dt * dpos, 0, L)
    state["resource"] = np.clip(resource + dt * dres, 0, None)
    state["alpha"] = np.clip(alpha + dt * dalpha, state["alpha_min"], K)
    state["productivity_ema"] = np.clip(prod_ema + dt * dprod, 0, None)
    state["overlap_ema"] = np.clip(overlap_ema + dt * doverlap, 0, None)
    state["consolidation"] = np.clip(consolidation + dt * dconsol, 0, 1)

    # polarity relaxes toward geography UNLESS protected by consolidation
    target_pol = np.clip(1 - 2 * pos / L, -1, 1)
    protect = consolidation_protect * consolidation
    state["pol"] = pol + dt * (1 - protect) * 0.005 * (target_pol - pol)

    state["step"] += 1
    return state

def classify_layers(state, frustrated_thresh=0.45, glassy_consol_thresh=0.6, glassy_radius=3.0):
    """Spin layer membership from continuous state.
    Frustrated: weak polarity + high tension (boundary nodes)
    Glassy: frustrated + high consolidation + clustered (stable memory nodes)"""
    n = state["n"]
    is_frustrated = (np.abs(state["pol"]) < 0.35) & (state["overlap_ema"] > frustrated_thresh)
    state["is_frustrated"] = is_frustrated

    is_glassy = np.zeros(n, dtype=bool)
    frustrated_idx = np.where(is_frustrated & (state["consolidation"] > glassy_consol_thresh))[0]
    if len(frustrated_idx) >= 2:
        frustrated_pos = state["pos"][frustrated_idx]
        tree = cKDTree(frustrated_pos[:, None])
        pairs = tree.query_pairs(r=glassy_radius)
        clustered = set()
        for a, b in pairs:
            clustered.add(a); clustered.add(b)
        for local_i in clustered:
            is_glassy[frustrated_idx[local_i]] = True
    state["is_glassy"] = is_glassy
    return state

# ============================================================================
# PART 5: scalar-only logging + checkpointing
# ============================================================================

def summarize(state):
    pol = state["pol"]
    spin_up_frac = float((pol > 0.35).mean())
    spin_down_frac = float((pol < -0.35).mean())
    frustrated_frac = float(state["is_frustrated"].mean())
    order_param = float(np.abs(np.exp(1j * state["phase"]).mean()))
    return dict(
        step=int(state["step"]),
        spin_up_frac=spin_up_frac, spin_down_frac=spin_down_frac, frustrated_frac=frustrated_frac,
        n_frustrated=int(state["is_frustrated"].sum()), n_glassy=int(state["is_glassy"].sum()),
        mean_alpha=float(state["alpha"].mean()),
        mean_resource=float(state["resource"].mean()),
        min_resource=float(state["resource"].min()),
        mean_consolidation=float(state["consolidation"].mean()),
        order_param=order_param,
    )

def run(n=500, steps=20000, out_dir="run", seed=0, resume=None,
        log_every=200, checkpoint_every=2000, rebuild_every=25,
        neighbor_radius=6.0, mobility_on=True):
    os.makedirs(out_dir, exist_ok=True)
    log_path = os.path.join(out_dir, "log.jsonl")
    ckpt_path = os.path.join(out_dir, "checkpoint.pkl")

    if resume is not None:
        with open(resume, "rb") as f:
            state = pickle.load(f)
        print(f"Resumed from {resume} at step {state['step']}")
    else:
        state = init_state(n, seed=seed)

    neigh = build_neighbors(state["pos"], neighbor_radius)
    t0 = time.time()
    target_step = state["step"] + steps

    with open(log_path, "a") as logf:
        while state["step"] < target_step:
            if state["step"] % rebuild_every == 0:
                neigh = build_neighbors(state["pos"], neighbor_radius)

            state = step(state, neigh, mobility_on=mobility_on)

            if state["step"] % log_every == 0:
                classify_layers(state)
                rec = summarize(state)
                rec["elapsed_s"] = round(time.time() - t0, 1)
                logf.write(json.dumps(rec) + "\n")
                logf.flush()
                print(f"step {rec['step']:6d}  spin_up={rec['spin_up_frac']:.2f} "
                      f"spin_down={rec['spin_down_frac']:.2f} frustrated={rec['n_frustrated']:4d} "
                      f"glassy={rec['n_glassy']:3d} alpha={rec['mean_alpha']:.3f} "
                      f"R={rec['order_param']:.3f}")

            if state["step"] % checkpoint_every == 0:
                with open(ckpt_path, "wb") as f:
                    pickle.dump(state, f)

    with open(ckpt_path, "wb") as f:
        pickle.dump(state, f)
    print(f"Done. Final checkpoint: {ckpt_path}")
    return state

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, default=500)
    p.add_argument("--steps", type=int, default=5000)
    p.add_argument("--out", type=str, default="run")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--resume", type=str, default=None)
    p.add_argument("--no-mobility", action="store_true")
    args = p.parse_args()
    run(n=args.n, steps=args.steps, out_dir=args.out, seed=args.seed,
        resume=args.resume, mobility_on=not args.no_mobility)