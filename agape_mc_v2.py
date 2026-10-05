#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGAPE-MC v2  --  standalone, label-blind, pre-registered Monte Carlo of bottom-up edge plasticity
=====================================================================================================
Design principle: COHERENCE OVER COERCION. Every rule below is local (a node or an edge sees only
its own neighbourhood and its own history). Ground-truth cluster labels are used in exactly three
places and nowhere in the dynamics: (G) the graph GENERATOR, (X) external DAMAGE applied by an
adversary, (V) the EVALUATOR. The simulator class never receives labels (checked in self-test T10).

WHAT CHANGED FROM v1 (agape_montecarlo_proof.py) AND WHY  (each item was a verified defect)
  D1  v1 growth was restricted to same ground-truth label  -> ORACLE. Removed. Growth is now spatially
      local + resonance-gated; labels are never visible.
  D2  v1 pruning acted only via a degree cap (>6) and the phase signal was uninformative (global sync,
      coherence > 0.99 in nearly every error run). Replaced by an edge-local STRAIN TRACE (below) whose
      information content is measured directly (AUROC) and tested against a shuffle null.
  D3  v1 "no_plasticity" was growth-only, not the promised "rewiring-only". Full ablation ladder now.
  D4  v1 alpha used additive demand + noise + clip. The Lean file (Logistics) proves the closed form only
      for the pure multiplicative logistic. v2 uses the pure logistic, UNCLIPPED; boundedness is a
      measured outcome (violation counter), not an enforced one.
  D5  v1 "accuracy" = raw Rand index of connected components; it floors at the single-component value and
      is bimodal. v2 reports adjusted Rand index, perfect-separation (success/fail) with Wilson CIs,
      cross-edge removal, collateral damage (intra-edge retention), and pruning precision.
  D6  v1 large-scale loader stored edges in one direction and all labels were 0 ("accuracy" = connectivity).
      v2 uses one undirected edge list (u<v) everywhere and a labelled clustered geometric graph.
  D7  v1 pruning_rate was defined as 1.0 when there was nothing to prune. v2 reports None.
  D8  v1 physics used a bare sin() coupling. v2 uses the proven Core.lean field (resonance + repulsion gate),
      friction from local distortion, and per-node coupling weight alpha (Core.lean / Energy.lean).
  D9  v1 large-scale results never existed (n_rep = 0, NaN in JSON). v2 writes valid JSON only.

-----------------------------------------------------------------------------------------------------
1. STATE
  node i: phase theta_i, velocity v_i, coupling weight alpha_i in (0,K], natural frequency omega_i,
          set-point degree t_i (= its degree in the initial graph, no global constant).
  edge e=(u,v), u<v: strain trace s_e in [0,1], age a_e.
  Graph is undirected; edges are stored once. Mass m=1.

2. EQUATIONS  (all from Core.lean unless marked NEW)
  E1  smoothAttenuation(x) = 1/(1+e^x)
  E2  resonanceField(d)    = (1+cos d)/2 * 1/(1+e^{-8 cos d})                         in [0,1], even
  E3  phaseDistance(a,b)   = 2 arcsin|sin((a-b)/2)|                                    in [0,pi]
  E4  repulsionGate(d)     = smoothAttenuation(20 * phaseDistance(d,0)^2)
  E5  F(d) = (resonanceField(d) - rs*repulsionGate(d)) * sin d ,  rs = 3.0              odd, 2pi-periodic
        F'(0) = 1/(1+e^-8) - rs/2  <0  <=>  rs > rs* = 2/(1+e^-8) ~ 1.9993  (exact fusion unstable)
  E6  D_i = sum_{j~i} phaseDistance(theta_j,theta_i)^2                                  (localDistortion, W=1)
  E7  friction_i = gamma0*smoothAttenuation(D_i) + beta*D_i
  E8  m dv_i/dt = alpha_i * sum_{j~i} F(theta_j - theta_i) - friction_i v_i + gamma0*0.5*omega_i
      dtheta_i/dt = v_i      (isolated node: v -> omega_i, since friction(D=0)=gamma0/2)
  E9  alpha:  d alpha_i/dt = eta * alpha_i * g_i * (1 - alpha_i/K),  g_i = mean_j resonanceField(.) - c2*D_i
        Bernoulli-linearisable: alpha(t) = 1/[1/K + (1/alpha0 - 1/K) exp(-int g)]   (Logistics.lean, exact)
  E10 NEW strain trace (edge-local, Hebbian-like, slow):  ds_e/dt = (phaseDistance(theta_v,theta_u)/pi - s_e)/tau_s
        A locked edge has s ~ 0.06; a drifting edge has s -> 0.5 (mean of |uniform phase|/pi). 0.5 is also the
        uninformative prior used to initialise new edges.
  E11 NEW prune (every topo_every steps, after warm-up): node i NOMINATES its highest-strain mature edge e* iff
        deg_i >= min_deg,  s_e* > s_floor,  and  s_e* > kappa * mean_{e != e*} s_e   (leave-one-out, node-relative).
        An edge is removed if nominated by either endpoint, provided both endpoints keep degree >= 1.
  E12 NEW grow (same cadence): node i with deg_i < t_i proposes the nearest spatial neighbour j (within
        r_grow = 2.5 x median 3rd-neighbour distance, a PHYSICAL length) not already linked, with deg_j < t_j+1,
        and resonanceField(theta_j-theta_i) >= grow_gate * (mean resonance of i's current edges).
  Information source (NEW, named confound C1): clusters have distinct intrinsic rhythms,
        omega_i = (label_i - (C-1)/2) * delta_omega + N(0, jitter). A wrongly-wired edge between rhythms
        sees persistent phase drift (high strain); a correct edge locks (low strain). If cross-coupling is
        strong enough to lock the clusters together the signal vanishes (predicted failure regime).

3. MECHANISMS, EACH WITH ITS VALIDATION (see self-tests T1..T15; run automatically, abort on failure)
  M1 coupling field (E2-E5)      T1 oddness, T2 zeros at 0/pi, T3 bounds, T4 phaseDistance^2 = d^2, T5 fusion threshold
  M2 equilibrium gap             T6 two-node locked gap equals root of resonance - rs*gate, dt-converged
  M3 energy decline (ω=0, α fixed)  T7 E + int(dissipation) conserved along RK4 trajectory (Energy.lean identity, numerical)
  M4 logistic alpha              T8 closed form vs RK4 (constant and time-varying g, from above and below)
  M5 no interior fixed point     T9 toy ODE: eigenvalues at (K,0) negative, 50 random starts -> (K,0)   [PROVEN for the toy only]
  M6 label blindness             T10 Sim signature has no labels; ARI invariant to label renaming
  M7 strain/prune/grow           T11 invariants over a run (u<v, unique, finite, alpha range), T12 shuffle null keeps marginal, AUROC ~ 0.5
  M8 metrics/statistics          T13 ARI vs sklearn, T14 Wilson/McNemar known values, T15 determinism

4. ABLATION LADDER (all modes share graph, initial phases and seeds -> paired)
  static             no topology change, alpha frozen at 1          (physics only)
  alpha_only         alpha dynamics, topology frozen
  prune_only         strain pruning, no growth, alpha frozen
  grow_only          growth, no pruning, alpha frozen
  rewire             prune + grow, alpha frozen                      ("rewiring-only", promised in v1)
  full               prune + grow + alpha
  rewire_shuffle_null / full_shuffle_null   as rewire / full but the strain vector is randomly permuted across
                     edges at every decision (identical marginal distribution, zero information)

5. METRICS (labels used here only)
  cross_remaining = cross edges now / cross edges at start (None if none at start);  intra_kept = intra now / intra at start
  ARI of connected components vs labels;  perfect = (no cross edge) and (components == clusters) and (ARI == 1)
  AUROC(strain: cross vs intra) = P(s_cross > s_intra), measured at the end in every mode (signal quality, independent of policy)
  pruning precision = cross edges among pruned / pruned;  cross edges created by growth (must be ~0: growth cannot import errors)
  alpha: mean, sd, fraction within 2% of K ("wall"), fraction < 0.1 ("floor"), unclipped violation count
  stiffness S = dt*sqrt(max_i(alpha_i deg_i) * max|F'| / m); runs with S > 2 are flagged as numerically unreliable

6. PRE-REGISTERED PREDICTIONS (written to prereg.json BEFORE any experiment runs; thresholds fixed here)
  P1 signal exists      Exp A, delta_omega>0, eps in {0.05,0.10}, static: median AUROC >= 0.90 (both graphs)
  P2 mechanism effect   Exp A: cross_remaining(full) < cross_remaining(static); Wilcoxon paired, Holm over graph x eps>0 (8 cells);
                        PASS if >= 6 of 8 cells have Holm p < 0.05 with the correct sign
  P3 information        same test, full vs full_shuffle_null; PASS if >= 6 of 8 cells
  P4 alpha effect       full vs rewire. EXPLORATORY, no directional prediction.
  P5 collateral         full: median intra_kept >= 0.80 in every graph x eps cell
  P6 degradation        Spearman(eps, perfect-rate of full) <= 0 on each graph (eps > 0)
  P7 boundedness        zero alpha violations in all runs AND zero runs with stiffness S > 2
  P8 wall               alpha_only, eps = 0: median fraction of nodes within 2% of K >= 0.80   (supports Part 2 in this realisation)
  P9 negative control   delta_omega = 0: full NOT better than full_shuffle_null (Wilcoxon p >= 0.05) and static AUROC in [0.35,0.65]
  P10 restoration (large) full: fraction of (seed x damage) events restored >= 0.50   (R > 0.5, spectrum Level-4 criterion, local rules only)
        restored := edges >= 0.9 E_pre, intra-only components <= intra-only components_pre (no true cluster left more fragmented),
        cross edges <= cross_pre + 0.02 E_pre; checked just before the next damage event (>= 100 time units later).
        REVISION NOTE: the first draft also required total components <= pre and ARI >= pre-0.05. A pilot run (seed 900000, NOT a test seed)
        showed this penalises genuine error removal (error edges merge clusters, so separating them raises the component count).
        Criterion replaced before any test seed was run; the first draft is disclosed here rather than silently dropped.
  Verdict labels: PASS -> "Supported", FAIL -> "Falsified (this realisation)". Nothing is "Proven" by simulation.

7. NAMED CONFOUNDS / LIMITS
  C1 cluster-correlated rhythms are the information source (negative control P9, sensitivity on delta_omega).
  C2 geometry is also informative (errors are long-range). Growth cannot create cross edges (counted), pruning ignores geometry.
  C3 set-point degrees come from the initial graph incl. error edges.
  C4 hyper-parameters (kappa, s_floor, tau_s, grow_gate, topo_every, K, delta_omega) are swept one-at-a-time in Exp C.
  C5 semi-implicit Euler is stable only for S < 2; large K (unbounded growth, a stated feature of the framework) needs adaptive steps. Not tested.
  C6 K is a modelling choice; the wall is a property of the cap. Part 2 proves "no interior fixed point" for the TOY ODE only
     (there D' = -lambda*alpha*D makes D -> 0 by construction); the full coupled system keeps D* > 0 via repulsion.
  C7 finite N, finite seeds; calibration of dt and delta_omega used pilot seeds >= 900000, disjoint from test seeds (100000+).

8. POST-HOC ADDITIONS  (specified AFTER Exp A-E results were seen; labelled POST-HOC everywhere; not pre-registered)
  Finding that motivated them: full_shuffle_null (P3 null) beat the real rule. It prunes ~550 edges/run vs ~20 for the real rule, and growth
  can only re-create local edges, so heavy random churn is a RATCHET that eventually deletes every long-range error. P3's null was
  matched on the strain marginal but not on churn, so it could not isolate information.
  X1 rewire_rate_null / prune_rate_null : same number of prunes per event as the strain rule would nominate, random identity (rate-matched null)
  X2 prune_shuffle_null                 : shuffled strain, NO growth (no ratchet) -- isolates the ratchet from the information
  X3 alpha_only, eps=0, T=1200          : finite-time check of the alpha wall (P8 missed 0.80 at T=400)
  Interpretation rule fixed before running X: information is demonstrated only if the strain rule beats its rate-matched null on
  cross_remaining with Holm p<0.05 in >=6 of 8 graph x eps cells.

Usage:
  python3 agape_mc_v2.py --selftest-only
  python3 agape_mc_v2.py --pilot                         # calibration pilot on disjoint seeds
  python3 agape_mc_v2.py --out results --n_rep 20        # full pipeline (resumable)
  python3 agape_mc_v2.py --out results --report-only
Dependencies: numpy, scipy (sympy / scikit-learn optional, used only for cross-checks).
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import sys, json, math, time, argparse, hashlib, inspect
from dataclasses import dataclass, replace, asdict
import numpy as np
from scipy import stats
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from scipy.spatial import cKDTree
from scipy.optimize import brentq

BASE_SEED = 100000
PILOT_SEED = 900000
RS_CRIT = 2.0 / (1.0 + math.exp(-8.0))


# =====================================================================================================
# 1. CORE PHYSICS  (E1-E5)
# =====================================================================================================
def _exp(x):
    return np.exp(np.clip(x, -700.0, 700.0))

def smooth_attenuation(x):
    return 1.0 / (1.0 + _exp(x))

def resonance_field(d):
    c = np.cos(d)
    return 0.5 * (1.0 + c) / (1.0 + _exp(-8.0 * c))

def phase_distance(a, b):
    return 2.0 * np.arcsin(np.minimum(1.0, np.abs(np.sin(0.5 * (a - b)))))

def repulsion_gate(d, steep=20.0):
    return smooth_attenuation(steep * phase_distance(d, 0.0) ** 2)

def coupling_force(d, rs=3.0, steep=20.0):
    return (resonance_field(d) - rs * repulsion_gate(d, steep)) * np.sin(d)

_FPMAX_CACHE = {}
def fprime_max(rs=3.0, steep=20.0):
    key = (rs, steep)
    if key not in _FPMAX_CACHE:
        x = np.linspace(-math.pi, math.pi, 400001)
        _FPMAX_CACHE[key] = float(np.max(np.abs(np.gradient(coupling_force(x, rs, steep), x))))
    return _FPMAX_CACHE[key]


@dataclass(frozen=True)
class Params:
    dt: float = 0.1
    T: float = 400.0
    m: float = 1.0
    gamma0: float = 1.0
    beta: float = 0.2
    rs: float = 3.0
    steep: float = 20.0
    c2: float = 0.1
    eta: float = 0.02
    K: float = 5.0
    alpha0: float = 1.0
    tau_s: float = 20.0
    maturity: float = 40.0
    warmup: float = 40.0
    topo_every: int = 20
    kappa: float = 3.0
    s_floor: float = 0.12
    min_deg: int = 3
    grow_gate: float = 0.5
    grow_radius_mult: float = 2.5
    k_cand: int = 14
    delta_omega: float = 0.5
    omega_jitter: float = 0.01


MODES = {
    "static":              dict(prune=False, grow=False, alpha=False, shuffle=False),
    "alpha_only":          dict(prune=False, grow=False, alpha=True,  shuffle=False),
    "prune_only":          dict(prune=True,  grow=False, alpha=False, shuffle=False),
    "grow_only":           dict(prune=False, grow=True,  alpha=False, shuffle=False),
    "rewire":              dict(prune=True,  grow=True,  alpha=False, shuffle=False),
    "full":                dict(prune=True,  grow=True,  alpha=True,  shuffle=False),
    "rewire_shuffle_null": dict(prune=True,  grow=True,  alpha=False, shuffle=True),
    "full_shuffle_null":   dict(prune=True,  grow=True,  alpha=True,  shuffle=True),
    # ---- POST-HOC controls (added after Exp A-E were seen; see docstring section 8) ----
    "rewire_rate_null":    dict(prune=True,  grow=True,  alpha=False, shuffle=False, rate_matched=True),
    "prune_rate_null":     dict(prune=True,  grow=False, alpha=False, shuffle=False, rate_matched=True),
    "prune_shuffle_null":  dict(prune=True,  grow=False, alpha=False, shuffle=True),
}


def edge_forces(theta, alpha, U, V, N, p):
    """Per-node coupling force, distortion D, raw phase distance per edge, and edge phase difference."""
    d = theta[V] - theta[U]
    F = coupling_force(d, p.rs, p.steep)
    force = np.bincount(U, alpha[U] * F, N) + np.bincount(V, -alpha[V] * F, N)   # F odd: force on V uses -F
    pd = phase_distance(theta[V], theta[U])
    D = np.bincount(U, pd ** 2, N) + np.bincount(V, pd ** 2, N)
    return force, D, pd, d


# =====================================================================================================
# 2. GRAPH GENERATORS  (labels used here only -- generative model)
# =====================================================================================================
def _knn_within(points, idx, k):
    tree = cKDTree(points[idx])
    kk = min(k + 1, len(idx))
    _, nb = tree.query(points[idx], k=kk)
    out = set()
    for a in range(len(idx)):
        for b in nb[a][1:]:
            i, j = int(idx[a]), int(idx[b])
            out.add((min(i, j), max(i, j)))
    return out

def build_graph(kind, eps, seed, p):
    rng = np.random.default_rng(np.random.SeedSequence([seed, 11]))
    if kind == "corners":
        C, n_per, k = 4, 10, 3
        centers = np.array([[0, 0], [0, 10], [10, 0], [10, 10]], float)
        pos = np.vstack([c + rng.normal(0, 0.1, (n_per, 2)) for c in centers])
    elif kind == "chain":
        C, n_per, k = 2, 8, 3
        pos = np.array([[float(i), 10.0 * c] for c in range(C) for i in range(n_per)])
    elif kind == "large":
        C, n_per, k = 6, 100, 5
        ang = 2 * math.pi * np.arange(C) / C
        centers = 20.0 * np.c_[np.cos(ang), np.sin(ang)]
        pos = np.vstack([c + rng.normal(0, 1.5, (n_per, 2)) for c in centers])
    else:
        raise ValueError(kind)
    N = C * n_per
    labels = np.repeat(np.arange(C), n_per)
    edges = set()
    for c in range(C):
        edges |= _knn_within(pos, np.where(labels == c)[0], k)
    n_intra = len(edges)
    n_err = int(round(eps * n_intra))
    errs = set()
    while len(errs) < n_err:
        i, j = int(rng.integers(N)), int(rng.integers(N))
        if labels[i] == labels[j]:
            continue
        key = (min(i, j), max(i, j))
        if key in edges or key in errs:
            continue
        errs.add(key)
    all_edges = np.array(sorted(edges | errs), dtype=np.int64)
    omega = (labels - (C - 1) / 2.0) * p.delta_omega + rng.normal(0, p.omega_jitter, N)
    return dict(pos=pos, labels=labels, edges=all_edges, omega=omega, n_intra0=n_intra, n_err=n_err, C=C)


# =====================================================================================================
# 3. SIMULATOR  (label-blind)
# =====================================================================================================
class Sim:
    def __init__(self, pos, edges, omega, p, flags, seed):
        self.p, self.flags = p, flags
        self.N = N = len(pos)
        self.pos = pos
        self.U = edges[:, 0].astype(np.int64).copy()
        self.V = edges[:, 1].astype(np.int64).copy()
        assert np.all(self.U < self.V)
        self.s = np.full(len(self.U), 0.5)
        self.age = np.zeros(len(self.U))
        self.omega = np.asarray(omega, float)
        rng = np.random.default_rng(np.random.SeedSequence([seed, 23]))
        self.theta = rng.uniform(0, 2 * math.pi, N)
        self.v = self.omega + rng.normal(0, 0.01, N)
        self.alpha = np.full(N, p.alpha0)
        self.rng_topo = np.random.default_rng(np.random.SeedSequence([seed, 37]))
        self.target = (np.bincount(self.U, minlength=N) + np.bincount(self.V, minlength=N)).astype(float)
        tree = cKDTree(pos)
        dist, nb = tree.query(pos, k=min(p.k_cand + 1, N))
        self.cand = nb[:, 1:]
        self.cand_dist = dist[:, 1:]
        k3 = dist[:, min(3, dist.shape[1] - 1)]
        self.r_grow = p.grow_radius_mult * float(np.median(k3))
        self.keys = set((self.U * N + self.V).tolist())
        self.step_i = 0
        self.alpha_violations = 0
        self.stiff_max = 0.0
        self.fpmax = fprime_max(p.rs, p.steep)
        self.pruned = []   # (u, v) pairs, classified later by the evaluator
        self.added = []

    @property
    def t(self):
        return self.step_i * self.p.dt

    def degrees(self):
        return np.bincount(self.U, minlength=self.N) + np.bincount(self.V, minlength=self.N)

    def step(self):
        p, N, U, V = self.p, self.N, self.U, self.V
        force, D, pd, d = edge_forces(self.theta, self.alpha, U, V, N, p)
        fric = p.gamma0 * smooth_attenuation(D) + p.beta * D
        self.v = (self.v + p.dt * (force + p.gamma0 * 0.5 * self.omega) / p.m) / (1.0 + p.dt * fric / p.m)
        self.theta = self.theta + p.dt * self.v
        self.s += (p.dt / p.tau_s) * (pd / math.pi - self.s)
        self.age += p.dt
        deg = None
        if self.flags["alpha"]:
            deg = self.degrees()
            res = resonance_field(d)
            avg = (np.bincount(U, res, N) + np.bincount(V, res, N)) / np.maximum(deg, 1)
            g = avg - p.c2 * D
            self.alpha = self.alpha + p.dt * p.eta * self.alpha * g * (1.0 - self.alpha / p.K)
            if self.alpha.min() <= 0.0 or self.alpha.max() > p.K * (1 + 1e-9) or not np.all(np.isfinite(self.alpha)):
                self.alpha_violations += 1
        self.step_i += 1
        if self.step_i % 20 == 0:
            if deg is None:
                deg = self.degrees()
            S = p.dt * math.sqrt(max(float(np.max(self.alpha * deg)), 1e-12) * self.fpmax / p.m)
            self.stiff_max = max(self.stiff_max, S)

    # ---- topology plasticity -------------------------------------------------------------------
    def _rebuild_keys(self):
        self.keys = set((self.U * self.N + self.V).tolist())

    def remove_edges(self, mask):
        keep = ~mask
        self.U, self.V, self.s, self.age = self.U[keep], self.V[keep], self.s[keep], self.age[keep]
        self._rebuild_keys()

    def _prune(self):
        p, N, E = self.p, self.N, len(self.U)
        if E == 0:
            return
        s = self.rng_topo.permutation(self.s) if self.flags["shuffle"] else self.s
        node = np.concatenate([self.U, self.V])
        sv = np.concatenate([s, s])
        ev = np.concatenate([np.arange(E), np.arange(E)])
        mat = np.concatenate([self.age >= p.maturity] * 2)
        deg = np.bincount(node, minlength=N)
        sv_m = np.where(mat, sv, -1.0)
        nmax = np.full(N, -1.0)
        np.maximum.at(nmax, node, sv_m)
        ssum = np.bincount(node, weights=sv, minlength=N)
        loo = (ssum - nmax) / np.maximum(deg - 1, 1)
        nominate = (deg >= p.min_deg) & (nmax > p.s_floor) & (nmax > p.kappa * loo)
        m = nominate[node] & (sv_m == nmax[node])
        if not m.any():
            return
        cand_e, cand_n = ev[m], node[m]
        _, first = np.unique(cand_n, return_index=True)
        pe = np.unique(cand_e[first])
        if self.flags.get("rate_matched") and len(pe):
            # POST-HOC null: same NUMBER of prunes per event as the strain rule nominates, but random identity
            pe = self.rng_topo.choice(E, size=len(pe), replace=False)
        keep = np.ones(E, bool)
        deg = deg.copy()
        for e in pe:
            u, v = self.U[e], self.V[e]
            if deg[u] >= 2 and deg[v] >= 2:
                keep[e] = False
                deg[u] -= 1
                deg[v] -= 1
                self.pruned.append((int(u), int(v)))
        if not keep.all():
            self.U, self.V, self.s, self.age = self.U[keep], self.V[keep], self.s[keep], self.age[keep]
            self._rebuild_keys()

    def _grow(self):
        p, N = self.p, self.N
        deg = self.degrees()
        deficit = np.where(deg < self.target)[0]
        if deficit.size == 0:
            return
        res = resonance_field(self.theta[self.V] - self.theta[self.U])
        rsum = np.bincount(self.U, res, N) + np.bincount(self.V, res, N)
        avg_res = np.where(deg > 0, rsum / np.maximum(deg, 1), 0.0)
        new = []
        for i in self.rng_topo.permutation(deficit):
            if deg[i] >= self.target[i]:
                continue
            gate = p.grow_gate * avg_res[i]
            for j, dj in zip(self.cand[i], self.cand_dist[i]):
                if dj > self.r_grow:
                    break
                a, b = (i, j) if i < j else (j, i)
                if a * N + b in self.keys or deg[j] >= self.target[j] + 1:
                    continue
                if float(resonance_field(self.theta[j] - self.theta[i])) < gate:
                    continue
                self.keys.add(a * N + b)
                new.append((a, b))
                deg[i] += 1
                deg[j] += 1
                break
        if new:
            nu = np.array(new, dtype=np.int64)
            self.U = np.concatenate([self.U, nu[:, 0]])
            self.V = np.concatenate([self.V, nu[:, 1]])
            self.s = np.concatenate([self.s, np.full(len(new), 0.5)])
            self.age = np.concatenate([self.age, np.zeros(len(new))])
            self.added.extend((int(a), int(b)) for a, b in new)

    def topology_event(self):
        if self.flags["prune"]:
            self._prune()
        if self.flags["grow"]:
            self._grow()

    def run(self, T=None, events=None, on_record=None, record_every=0):
        """events: {step_index: callable(sim)} applied BEFORE that step."""
        p = self.p
        n = int(round((T if T is not None else p.T) / p.dt))
        end = self.step_i + n
        while self.step_i < end:
            if events and self.step_i in events:
                events[self.step_i](self)
            self.step()
            if (self.flags["prune"] or self.flags["grow"]) and self.step_i % p.topo_every == 0 and self.t >= p.warmup:
                self.topology_event()
            if record_every and on_record and self.step_i % record_every == 0:
                on_record(self)


# =====================================================================================================
# 4. METRICS  (labels used here only)
# =====================================================================================================
def adjusted_rand(a, b):
    a, b = np.asarray(a), np.asarray(b)
    n = len(a)
    _, ai = np.unique(a, return_inverse=True)
    _, bi = np.unique(b, return_inverse=True)
    cont = np.zeros((ai.max() + 1, bi.max() + 1), dtype=np.int64)
    np.add.at(cont, (ai, bi), 1)
    c2 = lambda x: x * (x - 1) / 2.0
    sij, sa, sb = c2(cont).sum(), c2(cont.sum(1)).sum(), c2(cont.sum(0)).sum()
    tot = c2(n)
    exp = sa * sb / tot
    mx = 0.5 * (sa + sb)
    return 1.0 if mx == exp else float((sij - exp) / (mx - exp))

def auroc(scores, positive):
    pos, neg = scores[positive], scores[~positive]
    if len(pos) == 0 or len(neg) == 0:
        return None
    r = stats.rankdata(np.concatenate([pos, neg]))
    return float((r[:len(pos)].sum() - len(pos) * (len(pos) + 1) / 2) / (len(pos) * len(neg)))

def snapshot(sim, labels, init, with_logs=False):
    N, U, V, p = sim.N, sim.U, sim.V, sim.p
    cross = labels[U] != labels[V]
    nc, ni = int(cross.sum()), int((~cross).sum())
    ncomp, comp = connected_components(csr_matrix((np.ones(len(U)), (U, V)), shape=(N, N)), directed=False)
    nl = len(np.unique(labels))
    ari = adjusted_rand(comp, labels)
    iu_, iv_ = U[~cross], V[~cross]
    intra_ncomp = int(connected_components(csr_matrix((np.ones(len(iu_)), (iu_, iv_)), shape=(N, N)), directed=False)[0])
    deg = sim.degrees()
    H = 1.0 / (1.0 + float(np.mean(np.abs(deg - sim.target) / np.maximum(1.0, sim.target))))
    z = np.exp(1j * sim.theta)
    r_intra = float(np.mean([abs(z[labels == c].mean()) for c in np.unique(labels)]))
    out = dict(t=float(sim.t), edges=int(len(U)), cross=nc, intra=ni, ncomp=int(ncomp), intra_ncomp=intra_ncomp, ari=float(ari),
               perfect=bool(nc == 0 and ncomp == nl and ari > 1 - 1e-12),
               cross_remaining=(nc / init["cross"] if init["cross"] > 0 else None),
               intra_kept=ni / max(init["intra"], 1), H=H,
               alpha_mean=float(sim.alpha.mean()), alpha_sd=float(sim.alpha.std()),
               alpha_min=float(sim.alpha.min()), alpha_max=float(sim.alpha.max()),
               frac_wall=float(np.mean(sim.alpha >= 0.98 * p.K)), frac_floor=float(np.mean(sim.alpha < 0.1)),
               r_global=float(abs(z.mean())), r_intra=r_intra, auroc_strain=auroc(sim.s, cross))
    if with_logs:
        pr = np.array(sim.pruned, dtype=int).reshape(-1, 2)
        ad = np.array(sim.added, dtype=int).reshape(-1, 2)
        out.update(n_pruned=int(len(pr)), cross_pruned=int((labels[pr[:, 0]] != labels[pr[:, 1]]).sum()) if len(pr) else 0,
                   n_added=int(len(ad)), cross_added=int((labels[ad[:, 0]] != labels[ad[:, 1]]).sum()) if len(ad) else 0,
                   alpha_violations=int(sim.alpha_violations), stiff_max=float(sim.stiff_max))
    return out

def init_counts(G):
    cross = G["labels"][G["edges"][:, 0]] != G["labels"][G["edges"][:, 1]]
    return dict(cross=int(cross.sum()), intra=int((~cross).sum()))


# =====================================================================================================
# 5. WORKERS
# =====================================================================================================
def run_small(task):
    t0 = time.time()
    p = replace(Params(), **task.get("params", {}))
    G = build_graph(task["kind"], task["eps"], task["seed"], p)
    sim = Sim(G["pos"], G["edges"], G["omega"], p, MODES[task["mode"]], task["seed"])
    init = init_counts(G)
    sim.run()
    out = snapshot(sim, G["labels"], init, with_logs=True)
    out.update({k: task[k] for k in ("exp", "kind", "eps", "mode", "seed", "tag")}, init_cross=init["cross"], init_intra=init["intra"],
               runtime=time.time() - t0)
    return out

def apply_damage(sim, kind, labels, rng):
    N, U, V = sim.N, sim.U, sim.V
    if kind == "hub":
        deg = sim.degrees()
        hubs = np.argsort(deg)[-max(1, int(0.08 * N)):]
        inc = np.where(np.isin(U, hubs) | np.isin(V, hubs))[0]
        mask = np.zeros(len(U), bool)
        mask[rng.choice(inc, size=len(inc) // 2, replace=False)] = True
    elif kind == "region":
        c = sim.pos[rng.integers(N)]
        near = np.argsort(np.linalg.norm(sim.pos - c, axis=1))[:max(1, int(0.08 * N))]
        mask = np.isin(U, near) | np.isin(V, near)
    elif kind == "targeted":
        cl = rng.choice(np.unique(labels))
        inside = np.where((labels[U] == cl) & (labels[V] == cl))[0]
        mask = np.zeros(len(U), bool)
        mask[rng.choice(inside, size=int(0.6 * len(inside)), replace=False)] = True
    elif kind == "storm":
        mask = np.zeros(len(U), bool)
        mask[rng.choice(len(U), size=int(0.15 * len(U)), replace=False)] = True
    else:
        raise ValueError(kind)
    n = int(mask.sum())
    sim.remove_edges(mask)
    return n

LARGE_DAMAGE = [("hub", 200.0), ("region", 300.0), ("targeted", 400.0), ("storm", 500.0)]

def run_large(task):
    t0 = time.time()
    p = replace(Params(), **task.get("params", {}))
    p = replace(p, T=600.0)
    G = build_graph("large", task["eps"], task["seed"], p)
    labels = G["labels"]
    sim = Sim(G["pos"], G["edges"], G["omega"], p, MODES[task["mode"]], task["seed"])
    init = init_counts(G)
    rng = np.random.default_rng(np.random.SeedSequence([task["seed"], 53]))
    traj, events_log = [], []
    state = {}
    def mk(kind, tt):
        def f(s):
            pre = snapshot(s, labels, init)
            removed = apply_damage(s, kind, labels, rng)
            post = snapshot(s, labels, init)
            events_log.append(dict(kind=kind, t=tt, removed=removed, pre=pre, post=post, recovered_at=None, restored=None))
        return f
    events = {int(round(tt / p.dt)): mk(k, tt) for k, tt in LARGE_DAMAGE}
    def crit(ev, snap):
        pre = ev["pre"]
        return bool(snap["edges"] >= 0.9 * pre["edges"] and snap["intra_ncomp"] <= pre["intra_ncomp"]
                    and snap["cross"] <= pre["cross"] + 0.02 * pre["edges"])
    def rec(s):
        snap = snapshot(s, labels, init)
        traj.append({k: snap[k] for k in ("t", "edges", "cross", "ncomp", "ari", "alpha_mean", "H", "intra_kept")})
        for ev in events_log:
            if ev["recovered_at"] is None and s.t > ev["t"] and crit(ev, snap):
                ev["recovered_at"] = float(s.t - ev["t"])
    end_steps = {int(round((tt - 1e-9) / p.dt)) for _, tt in LARGE_DAMAGE[1:]} | {int(round(p.T / p.dt))}
    # run in segments so that "just before next damage" snapshots are exact
    marks = sorted(end_steps)
    sim_done = 0
    pre_marks = {}
    for mk_step in marks:
        n = mk_step - sim.step_i
        if n > 0:
            sim.run(T=n * p.dt, events=events, on_record=rec, record_every=100)
        pre_marks[mk_step] = snapshot(sim, labels, init)
    # attach "just before next damage" / final snapshot to each event
    steps_of = [int(round(tt / p.dt)) for _, tt in LARGE_DAMAGE]
    for idx, ev in enumerate(events_log):
        nxt = steps_of[idx + 1] if idx + 1 < len(steps_of) else int(round(p.T / p.dt))
        key = min(k for k in pre_marks if k >= (nxt - 1 if idx + 1 < len(steps_of) else nxt))
        ev["recov"] = pre_marks[key]
        ev["restored"] = crit(ev, ev["recov"])
    final = snapshot(sim, labels, init, with_logs=True)
    return dict(exp="E", kind="large", eps=task["eps"], mode=task["mode"], seed=task["seed"], tag=task["tag"], final=final,
                events=events_log, traj=traj, runtime=time.time() - t0)


# =====================================================================================================
# 6. STATISTICS
# =====================================================================================================
def wilson(k, n, z=1.959964):
    if n == 0:
        return (None, None)
    ph = k / n
    den = 1 + z * z / n
    c = (ph + z * z / (2 * n)) / den
    h = z * math.sqrt(ph * (1 - ph) / n + z * z / (4 * n * n)) / den
    return (max(0.0, c - h), min(1.0, c + h))

def mcnemar_exact(b, c):
    return 1.0 if b + c == 0 else float(stats.binomtest(b, b + c, 0.5).pvalue)

def paired_wilcoxon(x, y):
    d = np.asarray(x, float) - np.asarray(y, float)
    if np.allclose(d, 0):
        return 1.0
    try:
        return float(stats.wilcoxon(d, zero_method="wilcox").pvalue)
    except ValueError:
        return 1.0

def holm(ps):
    ps = np.asarray(ps, float)
    order = np.argsort(ps)
    adj = np.empty_like(ps)
    run = 0.0
    for rank, idx in enumerate(order):
        run = max(run, (len(ps) - rank) * ps[idx])
        adj[idx] = min(1.0, run)
    return adj.tolist()


# =====================================================================================================
# 7. SELF-TESTS  (every mechanism validated before any experiment)
# =====================================================================================================
def run_selftests(verbose=True):
    results = []
    def check(name, ok, detail=""):
        results.append((name, bool(ok), detail))
        if verbose:
            print(f"  [{'PASS' if ok else 'FAIL'}] {name}  {detail}")
    rng = np.random.default_rng(0)
    x = rng.uniform(-math.pi, math.pi, 2000)
    # T1-T5 coupling field
    check("T1 F odd", np.max(np.abs(coupling_force(-x) + coupling_force(x))) < 1e-12)
    check("T2 F(0)=F(pi)=0", abs(coupling_force(0.0)) < 1e-15 and abs(coupling_force(math.pi)) < 1e-12)
    r = resonance_field(x)
    check("T3 resonance in [0,1], even", r.min() >= 0 and r.max() <= 1 and np.max(np.abs(r - resonance_field(-x))) < 1e-12)
    check("T4 phaseDistance(d,0)^2 = d^2 on [-pi,pi]", np.max(np.abs(phase_distance(x, 0.0) ** 2 - x ** 2)) < 1e-9)
    h = 1e-6
    fp0 = (coupling_force(h) - coupling_force(-h)) / (2 * h)
    closed = resonance_field(0.0) - 3.0 * repulsion_gate(0.0)
    sgn_ok = all(((coupling_force(h, rs) - coupling_force(-h, rs)) / (2 * h) < 0) == (rs > RS_CRIT) for rs in (RS_CRIT - 0.01, RS_CRIT + 0.01, 1.0, 3.0))
    check("T5 F'(0)=res(0)-rs*gate(0); sign flips at rs*=2/(1+e^-8)", abs(fp0 - closed) < 1e-6 and sgn_ok, f"rs*={RS_CRIT:.6f}")
    # T6 two-node locked gap
    f = lambda d: float(resonance_field(d) - 3.0 * repulsion_gate(d))
    root = brentq(f, 0.05, 1.0)
    gaps = []
    for dt in (0.1, 0.05):
        p = replace(Params(), dt=dt)
        s = Sim(np.zeros((2, 2)) + [[0, 0], [1, 0]], np.array([[0, 1]]), np.zeros(2), p, MODES["static"], 1)
        s.theta = np.array([0.0, 0.8]); s.v = np.zeros(2)
        s.run(T=150.0)
        gaps.append(abs(float(s.theta[1] - s.theta[0])))
    check("T6 locked gap = root of res - rs*gate (dt-converged)", all(abs(g - root) < 2e-3 for g in gaps), f"root={root:.5f} sim={gaps}")
    # T7 energy identity
    N = 6
    iu, iv = np.triu_indices(N, 1)
    alpha = rng.uniform(0.5, 2.0, N)
    p = Params()
    grid = np.linspace(0, math.pi, 200001)
    Fg = coupling_force(grid)
    Gt = np.concatenate([[0], np.cumsum(0.5 * (Fg[1:] + Fg[:-1]) * np.diff(grid))])
    def Gpot(dd):
        w = (dd + math.pi) % (2 * math.pi) - math.pi
        return np.interp(np.abs(w), grid, Gt)
    def rhs(y):
        th, v = y[:N], y[N:2 * N]
        force, D, _, _ = edge_forces(th, alpha, iu, iv, N, p)
        fric = p.gamma0 * smooth_attenuation(D) + p.beta * D
        return np.concatenate([v, (force - fric * v) / p.m, [np.sum(fric * v ** 2 / alpha)]])
    def energy(y):
        th, v = y[:N], y[N:2 * N]
        return np.sum(p.m * v ** 2 / (2 * alpha)) + np.sum(Gpot(th[iv] - th[iu]))
    y = np.concatenate([rng.uniform(0, 2 * math.pi, N), rng.normal(0, 0.5, N), [0.0]])
    E0, h_ = energy(y), 0.005
    maxinc, maxdrift = 0.0, 0.0
    Eprev = E0
    for _ in range(4000):
        k1 = rhs(y); k2 = rhs(y + 0.5 * h_ * k1); k3 = rhs(y + 0.5 * h_ * k2); k4 = rhs(y + h_ * k3)
        y = y + h_ / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        Ecur = energy(y)
        maxinc = max(maxinc, Ecur - Eprev)
        Eprev = Ecur
        maxdrift = max(maxdrift, abs(Ecur + y[-1] - E0))
    check("T7 dE/dt = -sum friction*v^2/alpha  (E+Q conserved; E non-increasing)", maxdrift < 1e-6 and maxinc < 1e-9, f"drift={maxdrift:.2e} max_increase={maxinc:.2e}")
    # T8 logistic closed form
    def logistic_check(a0, K, gfun, T=300.0, h=0.01):
        a, t, I = a0, 0.0, 0.0
        for _ in range(int(T / h)):
            f1 = lambda a_, t_: a_ * gfun(t_) * (1 - a_ / K)
            k1 = f1(a, t); k2 = f1(a + 0.5 * h * k1, t + 0.5 * h); k3 = f1(a + 0.5 * h * k2, t + 0.5 * h); k4 = f1(a + h * k3, t + h)
            a += h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
            I += h * 0.5 * (gfun(t) + gfun(t + h)); t += h
        return a, 1.0 / (1.0 / K + (1.0 / a0 - 1.0 / K) * math.exp(-I))
    errs = []
    for a0, K, gf in [(1.0, 5.0, lambda t: 0.02), (10.0, 5.0, lambda t: 0.02), (0.2, 2.0, lambda t: 0.03 + 0.02 * math.sin(0.1 * t))]:
        a, c = logistic_check(a0, K, gf)
        errs.append(abs(a - c))
    check("T8 logistic: RK4 matches Logistics.lean closed form (from below, above, time-varying g)", max(errs) < 1e-5, f"max err={max(errs):.1e}")
    # T9 toy ODE
    from scipy.integrate import solve_ivp
    K, c1, c2_, lam, eta = 5.0, 0.8, 0.1, 0.05, 0.02
    ok = True
    for _ in range(50):
        a0, D0 = rng.uniform(0.05, 4.9), rng.uniform(0.0, 8.0)
        sol = solve_ivp(lambda t, z: [eta * z[0] * (c1 - c2_ * z[1]) * (1 - z[0] / K), -lam * z[0] * z[1]], (0, 4000), [a0, D0], method="LSODA", rtol=1e-8, atol=1e-10)
        ok &= abs(sol.y[0, -1] - K) < 0.05 and sol.y[1, -1] < 1e-3
    J = np.array([[eta * (c1) * (1 - 2), 0.0], [0.0, -lam * K]])
    detail = ""
    try:
        import sympy as sp
        a_, D_, K_, c1_, c2s, l_, e_ = sp.symbols("a D K c1 c2 l e", positive=True)
        adot = e_ * a_ * (c1_ - c2s * D_) * (1 - a_ / K_)
        sols = sp.solve(sp.factor(adot.subs(D_, 0)), a_)
        detail = f"sympy D=0 branch: {sols}"
        ok &= (sols == [K_])
    except Exception as ex:
        detail = f"sympy unavailable ({ex})"
    check("T9 toy ODE: only fixed point (K,0), stable (eigs<0), 50 random starts converge  [PROVEN for toy only]", ok and np.all(np.linalg.eigvals(J) < 0), detail)
    # T10 label blindness
    sig = inspect.signature(Sim.__init__)
    lab = rng.integers(0, 4, 40); perm = np.array([2, 0, 3, 1])[lab]
    other = rng.integers(0, 3, 40)
    check("T10 Sim has no label input; ARI invariant to label renaming",
          not any("label" in k for k in sig.parameters) and abs(adjusted_rand(lab, other) - adjusted_rand(perm, other)) < 1e-12)
    # T11 invariants over a run
    p = Params(T=150.0)
    G = build_graph("corners", 0.2, 5, p)
    s = Sim(G["pos"], G["edges"], G["omega"], p, MODES["full"], 5)
    s.run()
    keys = s.U * s.N + s.V
    inv = (np.all(s.U < s.V) and len(np.unique(keys)) == len(keys) and np.all(np.isfinite(s.theta)) and s.alpha_violations == 0
           and s.alpha.min() > 0 and s.alpha.max() <= p.K * (1 + 1e-9) and s.degrees().sum() == 2 * len(s.U) and s.keys == set(keys.tolist()))
    check("T11 invariants: u<v, unique edges, finite, alpha in (0,K] (unclipped), degree-sum, key set consistent", inv, f"stiff_max={s.stiff_max:.2f}")
    # T12 shuffle null
    sc = np.concatenate([rng.normal(0.06, 0.01, 60), rng.normal(0.5, 0.05, 6)])
    pos = np.arange(66) >= 60
    au = np.mean([auroc(rng.permutation(sc), pos) for _ in range(2000)])
    check("T12 shuffle null: same marginal, AUROC -> 0.5 (true signal AUROC=1)", abs(au - 0.5) < 0.03 and auroc(sc, pos) == 1.0 and np.allclose(np.sort(rng.permutation(sc)), np.sort(sc)), f"mean AUROC={au:.3f}")
    # T13 ARI vs sklearn
    try:
        from sklearn.metrics import adjusted_rand_score
        a = rng.integers(0, 5, 200); b = rng.integers(0, 4, 200)
        check("T13 ARI equals scikit-learn", abs(adjusted_rand(a, b) - adjusted_rand_score(a, b)) < 1e-12 and adjusted_rand(a, a) == 1.0)
    except ImportError:
        check("T13 ARI identity/known cases", adjusted_rand([0, 0, 1, 1], [5, 5, 7, 7]) == 1.0)
    # T14 statistics
    lo, hi = wilson(0, 10)
    check("T14 Wilson(0/10) upper=0.2775; McNemar(4,0) p=0.125; Holm", abs(hi - 0.2775) < 1e-3 and abs(mcnemar_exact(4, 0) - 0.125) < 1e-12 and holm([0.01, 0.04, 0.03]) == [0.03, 0.06, 0.06])
    # T15 determinism
    def once():
        p = Params(T=60.0)
        G = build_graph("chain", 0.2, 9, p)
        s = Sim(G["pos"], G["edges"], G["omega"], p, MODES["full"], 9)
        s.run()
        return s.theta.copy(), s.U.copy(), s.alpha.copy()
    a1, a2 = once(), once()
    check("T15 determinism (same seed -> bitwise identical)", all(np.array_equal(x_, y_) for x_, y_ in zip(a1, a2)))
    ok_all = all(r[1] for r in results)
    return ok_all, results


# =====================================================================================================
# 8. EXPERIMENTS
# =====================================================================================================
A_MODES = ["static", "alpha_only", "prune_only", "grow_only", "rewire", "full", "rewire_shuffle_null", "full_shuffle_null"]
EPS = [0.0, 0.05, 0.10, 0.20, 0.30]
SENS = [("kappa=2", dict(kappa=2.0)), ("kappa=5", dict(kappa=5.0)), ("tau_s=10", dict(tau_s=10.0, maturity=20.0)),
        ("tau_s=40", dict(tau_s=40.0, maturity=80.0)), ("delta_omega=0.25", dict(delta_omega=0.25)), ("delta_omega=1.0", dict(delta_omega=1.0)),
        ("K=2.5", dict(K=2.5)), ("K=10", dict(K=10.0)), ("s_floor=0.06", dict(s_floor=0.06)), ("s_floor=0.2", dict(s_floor=0.2)),
        ("grow_gate=0.25", dict(grow_gate=0.25)), ("grow_gate=0.75", dict(grow_gate=0.75)), ("topo_every=10", dict(topo_every=10)),
        ("topo_every=40", dict(topo_every=40))]

def make_tasks(n_rep, n_sens, n_large, skip_large=False, kinds=("corners", "chain")):
    tasks = []
    for kind in kinds:
        for eps in EPS:
            for mode in A_MODES:
                for r in range(n_rep):
                    tasks.append(dict(exp="A", kind=kind, eps=eps, mode=mode, seed=BASE_SEED + r, tag="default", params={}))
    for mode in ("static", "full", "full_shuffle_null"):                         # Exp B negative control
        for r in range(n_rep):
            tasks.append(dict(exp="B", kind="corners", eps=0.10, mode=mode, seed=BASE_SEED + r, tag="delta_omega=0", params=dict(delta_omega=0.0)))
    for name, ov in SENS:                                                        # Exp C sensitivity
        modes = ("alpha_only",) if name.startswith("K=") else ("static", "full", "full_shuffle_null")
        for mode in modes:
            for r in range(n_sens):
                eps = 0.0 if mode == "alpha_only" else 0.10
                tasks.append(dict(exp="C", kind="corners", eps=eps, mode=mode, seed=BASE_SEED + r, tag=name, params=ov))
    if not skip_large:
        for mode in ("static", "rewire", "full", "full_shuffle_null"):         # Exp E large-scale
            for r in range(n_large):
                tasks.append(dict(exp="E", kind="large", eps=0.10, mode=mode, seed=BASE_SEED + r, tag="default", params={}))
    return tasks

def make_posthoc_tasks(n_rep):
    tasks = []
    for kind in ("corners", "chain"):
        for eps in EPS[1:]:
            for mode in ("rewire_rate_null", "prune_rate_null", "prune_shuffle_null"):
                for r in range(n_rep):
                    tasks.append(dict(exp="X", kind=kind, eps=eps, mode=mode, seed=BASE_SEED + r, tag="default", params={}))
    for r in range(12):
        tasks.append(dict(exp="X", kind="corners", eps=0.0, mode="alpha_only", seed=BASE_SEED + r, tag="T1200", params=dict(T=1200.0)))
    return tasks

def task_key(t):
    return f"{t['exp']}|{t['kind']}|{t['eps']}|{t['mode']}|{t['seed']}|{t['tag']}"

def run_task(t):
    try:
        return run_large(t) if t["exp"] == "E" else run_small(t)
    except Exception as ex:   # never silently drop a run
        return dict(exp=t["exp"], kind=t["kind"], eps=t["eps"], mode=t["mode"], seed=t["seed"], tag=t["tag"], error=repr(ex))

def execute(tasks, path, workers=1):
    done = set()
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                try:
                    r = json.loads(line); done.add(task_key(r))
                except Exception:
                    pass
    todo = [t for t in tasks if task_key(t) not in done]
    print(f"{len(tasks)} tasks, {len(done)} already done, {len(todo)} to run", flush=True)
    t0 = time.time()
    def sink(f, r, i):
        f.write(json.dumps(r) + "\n"); f.flush()
        if (i + 1) % 25 == 0:
            el = time.time() - t0
            print(f"  {i+1}/{len(todo)}  {el/60:.1f} min elapsed  ETA {el/(i+1)*(len(todo)-i-1)/60:.1f} min", flush=True)
    with open(path, "a") as f:
        if workers > 1:
            import multiprocessing as mp
            with mp.Pool(workers) as pool:
                for i, r in enumerate(pool.imap_unordered(run_task, todo)):
                    sink(f, r, i)
        else:
            for i, t in enumerate(todo):
                sink(f, run_task(t), i)

def load_runs(path):
    runs = []
    with open(path) as f:
        for line in f:
            runs.append(json.loads(line))
    return runs


# =====================================================================================================
# 9. ANALYSIS + REPORT
# =====================================================================================================
def _sel(runs, **kw):
    return [r for r in runs if "error" not in r and all(r.get(k) == v for k, v in kw.items())]

def _paired(runs, kind, eps, ma, mb, key, exp="A", tag="default"):
    expa = "X" if ma.endswith(("rate_null", "prune_shuffle_null")) else exp
    expb = "X" if mb.endswith(("rate_null", "prune_shuffle_null")) else exp
    A = {r["seed"]: r for r in _sel(runs, exp=expa, kind=kind, eps=eps, mode=ma, tag=tag)}
    B = {r["seed"]: r for r in _sel(runs, exp=expb, kind=kind, eps=eps, mode=mb, tag=tag)}
    seeds = sorted(set(A) & set(B))
    return seeds, [A[s][key] for s in seeds], [B[s][key] for s in seeds]

def _med(xs):
    xs = [x for x in xs if x is not None]
    return float(np.median(xs)) if xs else None

def _fmt(x, nd=3):
    return "n/a" if x is None else (f"{x:.{nd}f}" if isinstance(x, float) else str(x))

def contrast(runs, ma, mb, kinds=("corners", "chain"), exp="A", metric="cross_remaining", tag="default"):
    """Paired contrast: metric(ma) vs metric(mb); returns rows and the Holm-adjusted family."""
    rows = []
    for kind in kinds:
        for eps in EPS[1:]:
            seeds, x, y = _paired(runs, kind, eps, ma, mb, metric, exp, tag)
            if not seeds:
                continue
            _, pa, pb = _paired(runs, kind, eps, ma, mb, "perfect", exp, tag)
            b = sum(1 for u, w in zip(pa, pb) if u and not w); c = sum(1 for u, w in zip(pa, pb) if w and not u)
            rows.append(dict(kind=kind, eps=eps, n=len(seeds), mean_a=float(np.mean(x)), mean_b=float(np.mean(y)),
                             p=paired_wilcoxon(x, y), perfect_a=int(sum(pa)), perfect_b=int(sum(pb)), mcnemar_p=mcnemar_exact(b, c)))
    adj = holm([r["p"] for r in rows]) if rows else []
    for r, a in zip(rows, adj):
        r["p_holm"] = a
    return rows

def evaluate_predictions(runs):
    V = {}
    A = [r for r in runs if "error" not in r and r["exp"] == "A"]
    # P1
    meds = {}
    for kind in ("corners", "chain"):
        vals = [r["auroc_strain"] for r in A if r["kind"] == kind and r["mode"] == "static" and r["eps"] in (0.05, 0.10) and r["auroc_strain"] is not None]
        meds[kind] = _med(vals)
    V["P1"] = (all(m is not None and m >= 0.90 for m in meds.values()), f"median AUROC (static, eps .05/.10): {meds}")
    # P2, P3, P4
    for pid, mb in (("P2", "static"), ("P3", "full_shuffle_null"), ("P4", "rewire")):
        rows = contrast(runs, "full", mb)
        good = sum(1 for r in rows if r["mean_a"] < r["mean_b"] and r["p_holm"] < 0.05)
        if pid == "P4":
            V[pid] = (None, f"EXPLORATORY full vs rewire: cells where full lower & Holm p<.05: {good}/{len(rows)}; "
                            f"cells where full higher & Holm p<.05: {sum(1 for r in rows if r['mean_a'] > r['mean_b'] and r['p_holm'] < 0.05)}/{len(rows)}")
        else:
            V[pid] = (good >= 6 and len(rows) == 8, f"{good}/{len(rows)} cells with correct sign and Holm p<0.05 (need >=6/8)")
    # P5
    bad = []
    for kind in ("corners", "chain"):
        for eps in EPS[1:]:
            m = _med([r["intra_kept"] for r in _sel(runs, exp="A", kind=kind, eps=eps, mode="full")])
            if m is None or m < 0.80:
                bad.append((kind, eps, m))
    V["P5"] = (not bad, "median intra_kept >= 0.80 in every cell" if not bad else f"violations: {bad}")
    # P6
    rho = {}
    for kind in ("corners", "chain"):
        xs, ys = [], []
        for eps in EPS[1:]:
            rs_ = _sel(runs, exp="A", kind=kind, eps=eps, mode="full")
            if rs_:
                xs.append(eps); ys.append(np.mean([r["perfect"] for r in rs_]))
        if len(set(ys)) > 1:
            rho[kind] = float(stats.spearmanr(xs, ys).statistic)
        else:
            rho[kind] = 0.0
    V["P6"] = (all(v <= 0 for v in rho.values()), f"Spearman(eps, perfect-rate): {rho}")
    # P7
    allr = [r for r in runs if "error" not in r and r["exp"] != "E"] + [r["final"] for r in runs if "error" not in r and r["exp"] == "E"]
    viol = sum(r.get("alpha_violations", 0) for r in allr)
    unstable = sum(1 for r in allr if r.get("stiff_max", 0) > 2.0)
    errs = sum(1 for r in runs if "error" in r)
    V["P7"] = (viol == 0 and unstable == 0 and errs == 0, f"alpha violations={viol}, runs with stiffness>2: {unstable}/{len(allr)}, crashed runs={errs}")
    # P8
    fw = [r["frac_wall"] for r in _sel(runs, exp="A", eps=0.0, mode="alpha_only")]
    V["P8"] = (_med(fw) is not None and _med(fw) >= 0.80, f"median fraction within 2% of K (alpha_only, eps=0): {_fmt(_med(fw))} over {len(fw)} runs")
    # P9
    B = [r for r in runs if "error" not in r and r["exp"] == "B"]
    s1 = {r["seed"]: r["cross_remaining"] for r in B if r["mode"] == "full"}
    s2 = {r["seed"]: r["cross_remaining"] for r in B if r["mode"] == "full_shuffle_null"}
    seeds = sorted(set(s1) & set(s2))
    pw = paired_wilcoxon([s1[s] for s in seeds], [s2[s] for s in seeds]) if seeds else None
    au = _med([r["auroc_strain"] for r in B if r["mode"] == "static"])
    V["P9"] = (pw is not None and pw >= 0.05 and au is not None and 0.35 <= au <= 0.65,
               f"delta_omega=0: full vs shuffle Wilcoxon p={_fmt(pw)}; static median AUROC={_fmt(au)}")
    # P10
    E = [r for r in runs if "error" not in r and r["exp"] == "E" and r["mode"] == "full"]
    ev = [e["restored"] for r in E for e in r["events"]]
    V["P10"] = (len(ev) > 0 and np.mean(ev) >= 0.5, f"restored fraction (full) = {np.mean(ev):.2f} over {len(ev)} events" if ev else "no large-scale data")
    return V

def make_report(runs, out_dir, selftests, prereg_hash, final_hash=None):
    L = []
    w = L.append
    w("# AGAPE-MC v2 -- results report (auto-generated)\n")
    w(f"Pre-registered script SHA-256 (Exp A-E ran with this exact file; snapshot kept as `agape_mc_v2_prereg_snapshot.py`): `{prereg_hash}`  ")
    if final_hash and final_hash != prereg_hash:
        w(f"Final script SHA-256: `{final_hash}`  (differs: POST-HOC controls X1-X3 and report sections 6b were added after Exp A-E results were seen; nothing in Exp A-E code paths changed.)  ")
    w(f"Runs: {len(runs)} total, {sum(1 for r in runs if 'error' in r)} crashed.  Test seeds {BASE_SEED}+, calibration seeds {PILOT_SEED}+ (disjoint).\n")
    w("## 0. Model, mechanisms, predictions, confounds (verbatim from the script)\n")
    w("```text\n" + (__doc__ or "") + "\n```\n")
    w("## 1. Mechanism validation (self-tests)\n")
    w("| test | result | detail |\n|---|---|---|")
    for n, ok, d in selftests:
        w(f"| {n} | {'PASS' if ok else 'FAIL'} | {d} |")
    V = evaluate_predictions(runs)
    w("\n## 2. Pre-registered predictions and verdicts\n")
    w("| id | verdict | evidence |\n|---|---|---|")
    for k in sorted(V, key=lambda s: int(s[1:])):
        ok, d = V[k]
        lab = "EXPLORATORY" if ok is None else ("Supported" if ok else "Falsified (this realisation)")
        w(f"| {k} | **{lab}** | {d} |")
    A = [r for r in runs if "error" not in r and r["exp"] == "A"]
    w("\n## 3. Exp A -- gradient error pressure\n")
    w("Cell = perfect separations / seeds (Wilson 95% CI) ; second line = mean cross_remaining ; third = mean intra_kept.\n")
    for kind in ("corners", "chain"):
        w(f"\n### {kind}\n")
        w("| eps | " + " | ".join(A_MODES) + " |\n|---|" + "---|" * len(A_MODES))
        for eps in EPS:
            cells = []
            for m in A_MODES:
                rs_ = _sel(runs, exp="A", kind=kind, eps=eps, mode=m)
                if not rs_:
                    cells.append("-"); continue
                k = sum(r["perfect"] for r in rs_); lo, hi = wilson(k, len(rs_))
                cr = [r["cross_remaining"] for r in rs_ if r["cross_remaining"] is not None]
                cells.append(f"{k}/{len(rs_)} [{lo:.2f},{hi:.2f}]<br>cr={_fmt(float(np.mean(cr)) if cr else None,2)}<br>ik={np.mean([r['intra_kept'] for r in rs_]):.2f}")
            w(f"| {eps} | " + " | ".join(cells) + " |")
    w("\n### Paired contrasts on cross_remaining (Wilcoxon, Holm within family of 8 cells); McNemar on perfect separation\n")
    for ma, mb, title in (("full", "static", "P2: full vs static"), ("full", "full_shuffle_null", "P3: full vs full_shuffle_null"),
                          ("full", "rewire", "P4 (exploratory): full vs rewire"), ("rewire", "rewire_shuffle_null", "rewire vs rewire_shuffle_null")):
        w(f"\n**{title}**\n\n| graph | eps | n | mean {ma} | mean {mb} | Wilcoxon p | Holm p | perfect {ma} | perfect {mb} | McNemar p |\n|---|---|---|---|---|---|---|---|---|---|")
        for r in contrast(runs, ma, mb):
            w(f"| {r['kind']} | {r['eps']} | {r['n']} | {r['mean_a']:.3f} | {r['mean_b']:.3f} | {r['p']:.4f} | {r['p_holm']:.4f} | {r['perfect_a']} | {r['perfect_b']} | {r['mcnemar_p']:.4f} |")
    w("\n### Signal quality, pruning precision, growth hygiene, phase coherence\n")
    w("| graph | eps | median AUROC(static) | pruning precision (full) | cross edges created by growth (full, total) | r_global static | r_global full |\n|---|---|---|---|---|---|---|")
    for kind in ("corners", "chain"):
        for eps in EPS[1:]:
            st = _sel(runs, exp="A", kind=kind, eps=eps, mode="static"); fu = _sel(runs, exp="A", kind=kind, eps=eps, mode="full")
            npr = sum(r["n_pruned"] for r in fu); cp = sum(r["cross_pruned"] for r in fu)
            w(f"| {kind} | {eps} | {_fmt(_med([r['auroc_strain'] for r in st]),2)} | {('%.2f' % (cp/npr)) if npr else 'n/a'} ({cp}/{npr}) | {sum(r['cross_added'] for r in fu)} | "
              f"{_fmt(_med([r['r_global'] for r in st]),2)} | {_fmt(_med([r['r_global'] for r in fu]),2)} |")
    w("\n### Alpha behaviour (wall / floor / spread)\n")
    w("| graph | eps | mode | median frac within 2% of K | median frac < 0.1 | median alpha mean |\n|---|---|---|---|---|---|")
    for kind in ("corners", "chain"):
        for eps in (0.0, 0.10, 0.30):
            for m in ("alpha_only", "full"):
                rs_ = _sel(runs, exp="A", kind=kind, eps=eps, mode=m)
                if rs_:
                    w(f"| {kind} | {eps} | {m} | {_fmt(_med([r['frac_wall'] for r in rs_]),2)} | {_fmt(_med([r['frac_floor'] for r in rs_]),2)} | {_fmt(_med([r['alpha_mean'] for r in rs_]),2)} |")
    w("\n## 4. Exp B -- negative control (delta_omega = 0, corners, eps = 0.10)\n")
    w("| mode | n | perfect | mean cross_remaining | median AUROC |\n|---|---|---|---|---|")
    for m in ("static", "full", "full_shuffle_null"):
        rs_ = _sel(runs, exp="B", mode=m)
        if rs_:
            cr = [r["cross_remaining"] for r in rs_ if r["cross_remaining"] is not None]
            w(f"| {m} | {len(rs_)} | {sum(r['perfect'] for r in rs_)} | {_fmt(float(np.mean(cr)) if cr else None)} | {_fmt(_med([r['auroc_strain'] for r in rs_]),2)} |")
    w("\n## 5. Exp C -- one-at-a-time sensitivity (corners, eps = 0.10; K rows are alpha_only at eps = 0)\n")
    w("| setting | mode | n | perfect | mean cross_remaining | mean intra_kept | median frac_wall | max stiffness |\n|---|---|---|---|---|---|---|---|")
    tags = ["default"] + [n for n, _ in SENS]
    for tg in tags:
        for m in ("static", "full", "full_shuffle_null", "alpha_only"):
            rs_ = _sel(runs, exp="C", tag=tg, mode=m) if tg != "default" else _sel(runs, exp="A", kind="corners", eps=(0.0 if m == "alpha_only" else 0.10), mode=m)
            if rs_:
                cr = [r["cross_remaining"] for r in rs_ if r["cross_remaining"] is not None]
                w(f"| {tg} | {m} | {len(rs_)} | {sum(r['perfect'] for r in rs_)} | {_fmt(float(np.mean(cr)) if cr else None)} | {np.mean([r['intra_kept'] for r in rs_]):.2f} | {_fmt(_med([r['frac_wall'] for r in rs_]),2)} | {max(r['stiff_max'] for r in rs_):.2f} |")
    E = [r for r in runs if "error" not in r and r["exp"] == "E"]
    w("\n## 6. Exp E -- large clustered graph (N=600, 6 clusters, eps=0.10), four damage events\n")
    if E:
        w("| mode | seeds | final perfect | final cross_remaining (mean) | restored fraction (events) | per-damage restored (hub/region/targeted/storm) | median time-to-restore | final H |\n|---|---|---|---|---|---|---|---|")
        for m in ("static", "rewire", "full", "full_shuffle_null"):
            rs_ = [r for r in E if r["mode"] == m]
            if not rs_:
                continue
            evs = [e for r in rs_ for e in r["events"]]
            per = []
            for k in ("hub", "region", "targeted", "storm"):
                ee = [e["restored"] for e in evs if e["kind"] == k]
                per.append(f"{sum(ee)}/{len(ee)}")
            ttr = [e["recovered_at"] for e in evs if e["recovered_at"] is not None]
            cr = [r["final"]["cross_remaining"] for r in rs_ if r["final"]["cross_remaining"] is not None]
            w(f"| {m} | {len(rs_)} | {sum(r['final']['perfect'] for r in rs_)} | {_fmt(float(np.mean(cr)) if cr else None)} | {np.mean([e['restored'] for e in evs]):.2f} | {' / '.join(per)} | {_fmt(_med(ttr),0)} | {np.mean([r['final']['H'] for r in rs_]):.2f} |")
    else:
        w("No large-scale runs in this results file.")
    X = [r for r in runs if "error" not in r and r["exp"] == "X"]
    w("\n## 6b. POST-HOC diagnostics (specified after seeing Exp A-E; NOT pre-registered)\n")
    if X:
        w("**Why the shuffle null won: churn.** Mean prunes per run, pruning precision (cross edges among pruned) and lift over base rate.\n")
        w("| graph | eps | mode | pruned/run | precision | base rate | lift | growth-added/run |\n|---|---|---|---|---|---|---|---|")
        pool = [r for r in runs if "error" not in r and r["exp"] in ("A", "X") and r["mode"] in
                ("prune_only", "prune_shuffle_null", "prune_rate_null", "rewire", "rewire_rate_null", "rewire_shuffle_null", "full", "full_shuffle_null")]
        for kind in ("corners", "chain"):
            for eps in (0.1, 0.3):
                for m in ("prune_only", "prune_rate_null", "prune_shuffle_null", "rewire", "rewire_rate_null", "rewire_shuffle_null", "full", "full_shuffle_null"):
                    rs_ = [r for r in pool if r["kind"] == kind and r["eps"] == eps and r["mode"] == m]
                    if not rs_:
                        continue
                    n = sum(r["n_pruned"] for r in rs_); c = sum(r["cross_pruned"] for r in rs_)
                    base = float(np.mean([r["init_cross"] / (r["init_cross"] + r["init_intra"]) for r in rs_]))
                    prec = c / n if n else None
                    w(f"| {kind} | {eps} | {m} | {n/len(rs_):.1f} | {_fmt(prec,2)} | {base:.2f} | {_fmt(prec/base if prec is not None else None,1)} | {np.mean([r['n_added'] for r in rs_]):.1f} |")
        w("\n**Information test against rate-matched nulls** (cross_remaining, Wilcoxon paired, Holm within each 8-cell family; lower is better).\n")
        fam = {}
        for ma, mb, title in (("rewire", "rewire_rate_null", "X1a: rewire vs rewire_rate_null (growth on)"),
                              ("prune_only", "prune_rate_null", "X1b: prune_only vs prune_rate_null (growth off)"),
                              ("prune_only", "prune_shuffle_null", "X2: prune_only vs prune_shuffle_null (growth off)"),
                              ("rewire", "prune_only", "ratchet check: rewire (growth on) vs prune_only (growth off)")):
            rows = contrast(runs, ma, mb)
            good = sum(1 for r in rows if r["mean_a"] < r["mean_b"] and r["p_holm"] < 0.05)
            fam[title] = (good, len(rows))
            w(f"\n**{title}** -- cells with {ma} lower & Holm p<0.05: {good}/{len(rows)}\n\n| graph | eps | n | mean {ma} | mean {mb} | Holm p | perfect {ma} | perfect {mb} |\n|---|---|---|---|---|---|---|---|")
            for r in rows:
                w(f"| {r['kind']} | {r['eps']} | {r['n']} | {r['mean_a']:.3f} | {r['mean_b']:.3f} | {r['p_holm']:.4f} | {r['perfect_a']} | {r['perfect_b']} |")
        g1 = fam.get("X1a: rewire vs rewire_rate_null (growth on)", (0, 8))[0]
        w(f"\n**Pre-fixed X interpretation rule (>= 6/8 cells vs rate-matched null with growth on): {'MET' if g1 >= 6 else 'NOT MET'} ({g1}/8).**\n")
        T12 = [r for r in X if r["tag"] == "T1200"]
        if T12:
            w(f"**X3 alpha wall at T=1200** (alpha_only, corners, eps=0, n={len(T12)}): median fraction within 2% of K = {_fmt(_med([r['frac_wall'] for r in T12]),2)}, "
              f"median fraction < 0.1 = {_fmt(_med([r['frac_floor'] for r in T12]),2)} (T=400 pre-registered value: 0.78 / 0.09).\n")
        B_ = [r for r in runs if "error" not in r and r["exp"] == "B"]
        s1 = {r["seed"]: r["cross_remaining"] for r in B_ if r["mode"] == "full"}; s2 = {r["seed"]: r["cross_remaining"] for r in B_ if r["mode"] == "full_shuffle_null"}
        sd = sorted(set(s1) & set(s2))
        if sd:
            d = np.array([s1[k] - s2[k] for k in sd])
            w(f"**P9 direction (post-hoc one-sided reading):** at delta_omega=0, full has HIGHER cross_remaining than full_shuffle_null in {int((d>0).sum())}/{len(d)} seeds "
              f"(Wilcoxon one-sided 'full worse' p={stats.wilcoxon(d, alternative='greater', zero_method='wilcox').pvalue:.2g}). The pre-registered two-sided criterion (p>=0.05) is not met, "
              f"so P9 stays 'Falsified' as registered; the substantive prediction 'full is not better than shuffle' holds, because shuffle's advantage is the churn ratchet.\n")
    else:
        w("Not run. Use --posthoc.\n")
    w("\n## 7. How to read this (status labels)\n")
    w("* Self-tests T1-T8, T10-T15 are numerical checks of identities proven in Lean (Core/Energy/Logistics) or of code correctness: **Validated (numerical)**, not re-proved.\n"
      "* T9 is **Proven for the toy ODE**; for the coupled system it is **Partial** (corroborated by P8 only where the cap K is imposed).\n"
      "* P1-P10 verdicts are properties of this realisation (this graph family, these parameters, these seeds); sensitivity is Section 5.\n"
      "* Anything labelled Falsified is a finding, not a bug, unless a self-test fails.\n")
    path = os.path.join(out_dir, "REPORT.md")
    with open(path, "w") as f:
        f.write("\n".join(L))
    with open(os.path.join(out_dir, "verdicts.json"), "w") as f:
        json.dump({k: dict(pass_=(None if v[0] is None else bool(v[0])), evidence=v[1]) for k, v in V.items()}, f, indent=2)
    return path, V


# =====================================================================================================
# 10. MAIN
# =====================================================================================================
def pilot():
    print("PILOT (calibration seeds, disjoint from test seeds)")
    for dw in (0.25, 0.5, 1.0):
        for mode in ("static", "full"):
            rows = []
            for r in range(4):
                t = dict(exp="P", kind="corners", eps=0.10, mode=mode, seed=PILOT_SEED + r, tag="pilot", params=dict(delta_omega=dw))
                rows.append(run_small(t))
            print(f"  dw={dw} {mode:6s} perfect={sum(x['perfect'] for x in rows)}/4 cross_rem={np.mean([x['cross_remaining'] for x in rows]):.2f} "
                  f"auroc={_fmt(_med([x['auroc_strain'] for x in rows]),2)} r_glob={np.mean([x['r_global'] for x in rows]):.2f} "
                  f"stiff={max(x['stiff_max'] for x in rows):.2f} t={np.mean([x['runtime'] for x in rows]):.1f}s", flush=True)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest-only", action="store_true")
    ap.add_argument("--pilot", action="store_true")
    ap.add_argument("--report-only", action="store_true")
    ap.add_argument("--out", default="results")
    ap.add_argument("--n_rep", type=int, default=20)
    ap.add_argument("--n_sens", type=int, default=10)
    ap.add_argument("--n_large", type=int, default=6)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--skip-large", action="store_true")
    ap.add_argument("--kinds", default="corners,chain")
    ap.add_argument("--posthoc", action="store_true", help="run POST-HOC controls (X1-X3) and append to raw.jsonl")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    print("SELF-TESTS")
    ok, tests = run_selftests()
    if not ok:
        print("SELF-TEST FAILURE -- refusing to run experiments"); sys.exit(1)
    if a.selftest_only:
        return
    if a.pilot:
        pilot(); return
    src = open(os.path.abspath(__file__), "rb").read()
    h = hashlib.sha256(src).hexdigest()
    prereg = os.path.join(a.out, "prereg.json")
    if not os.path.exists(prereg):
        with open(prereg, "w") as f:
            json.dump(dict(script_sha256=h, written=time.strftime("%Y-%m-%d %H:%M:%S"), params=asdict(Params()), n_rep=a.n_rep, n_sens=a.n_sens,
                           n_large=a.n_large, modes=list(MODES), eps=EPS, note="predictions P1-P10 and decision rules are in the script docstring section 6"), f, indent=2)
    raw = os.path.join(a.out, "raw.jsonl")
    if not a.report_only:
        tl = make_tasks(a.n_rep, a.n_sens, a.n_large, a.skip_large, tuple(a.kinds.split(",")))
        if a.posthoc:
            tl = tl + make_posthoc_tasks(a.n_rep)
        execute(tl, raw, a.workers)
    runs = load_runs(raw)
    path, V = make_report(runs, a.out, tests, json.load(open(prereg))["script_sha256"], h)
    print("report:", path)
    for k in sorted(V, key=lambda s: int(s[1:])):
        print(f"  {k}: {V[k][0]}  {V[k][1]}")

if __name__ == "__main__":
    main()
