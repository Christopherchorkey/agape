import Mathlib
import Mathlib.Tactic.MinImports
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
/-! ### Core.lean — base definitions
Sections 1-4 from AgapeFramework_Plastic(2).lean: SystemConfig/SystemState,
non-coercive metrics (resonanceField, phaseDistance, repulsionGate,
couplingForceField, localDistortion), plasticity dynamics, and the
axiomatic InteractionPotential. Everything downstream (Energy, Plasticity,
Logistic) builds on this file.
-/
open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- 1. DECENTRALIZED CONFIGURATION & STATE (now with plasticity)
-- =========================================================================

structure NodeProperties where
  mass              : ℝ  -- m_i > 0 (slowly evolving; no dynamics yet defined for this field)
  baselineFriction  : ℝ  -- γ_0 > 0
  distortionSens    : ℝ  -- β_i > 0
  couplingWeight    : ℝ  -- α_i > 0 (plasticity primarily here)
  naturalFrequency  : ℝ  -- ω_i, intrinsic drive. Added to test whether frequency
                          -- heterogeneity bounds couplingWeight growth under
                          -- sustained coherence. Numerically it does NOT: the
                          -- locked-state phase lag scales like ω_i / α_i, so
                          -- growing α self-consistently shrinks the lag back to
                          -- zero and localDistortion still asymptotes to 0.
                          -- Verified numerically (d_i ~ (Δω/α)^2 to high
                          -- precision), not yet reflected in any theorem below.

/-- Positivity invariant for node properties. Use as a hypothesis instead of
    re-asserting positivity per-lemma with `sorry`. -/
structure NodeProperties.Pos (p : NodeProperties) : Prop where
  mass_pos      : p.mass > 0
  friction_pos  : p.baselineFriction > 0
  sens_pos      : p.distortionSens ≥ 0
  weight_pos    : p.couplingWeight > 0

structure NodeState where
  phase    : ℝ
  velocity : ℝ

abbrev SystemState (ι : Type*) := ι → NodeState
abbrev SystemConfig (ι : Type*) := ι → NodeProperties
abbrev NetworkTopology (ι : Type*) := ι → ι → ℝ

-- =========================================================================
-- 2. NON-COERCIVE METRICS
-- =========================================================================

noncomputable def smoothAttenuation (distortion : ℝ) : ℝ :=
  1 / (1 + Real.exp distortion)

noncomputable def resonanceField (phase_diff : ℝ) : ℝ :=
  let c := Real.cos phase_diff
  (1 + c) / 2 * (1 / (1 + Real.exp (-8 * c)))

noncomputable def phaseDistance (a b : ℝ) : ℝ :=
  2 * Real.arcsin |Real.sin ((a - b) / 2)|

noncomputable def localDistortion (W : NetworkTopology ι) (traj : ℝ → SystemState ι)
    (t : ℝ) (i : ι) (τ : ι → ι → ℝ) : ℝ :=
  ∑ j : ι, W i j * (phaseDistance (traj (t - τ i j) j).phase (traj t i).phase) ^ 2

noncomputable def memeticBandwidth (s1 s2 : NodeState) : ℝ :=
  resonanceField (s1.phase - s2.phase)

/-- Near-field repulsion gate: reuses smoothAttenuation (already defined above)
    evaluated on squared phase distance, rather than introducing a new sigmoid
    family. Peaks at 0.5 when Δ=0 and decays as Δ grows — a genuine "how close
    are these two, specifically" indicator, distinct from resonanceField's own
    (broader) decay. steepness controls how narrow the repulsive core is.

    MULTISTABILITY, CHARACTERIZED (numerically confirmed this session, not
    conjectural — see multi_n.py and three_cluster_test.py):

    `couplingForceField` is exactly zero at Δ=180° (since
    `resonanceField 180° = (1 + cos 180°)/2 = 0` exactly) but only
    approximately zero at other large separations — e.g. at Δ=120°,
    `resonanceField ≈ 0.0045`, `couplingForceField ≈ 0.0039`, small but
    strictly nonzero. This has a direct dynamical consequence: a 2-cluster
    configuration at maximal (≈180°) separation is the ONLY multi-cluster
    arrangement in which every inter-cluster pair sits exactly at the
    function's true zero. Any other cluster count must place at least one
    pair of clusters at a separation where the residual force is small but
    nonzero, giving a persistent (if weak) drift.

    Confirmed two ways this session:
    - Random search (`multi_n.py`): sweeping N ∈ {4,6,8,12,16,20} with
      10–16 random initial conditions each, only 1-cluster (full sync) and
      2-cluster (bipolar split) equilibria were ever found — no 3+-cluster
      state appeared by chance at any tested N.
    - Targeted construction (`three_cluster_test.py`): hand-built 3-cluster
      initial conditions (even splits (2,2,2), (3,3,3), (4,4,4) and uneven
      splits (2,3,4), (2,4,6), clusters placed 120° apart, tiny symmetry-
      breaking jitter to avoid a numerically-frozen exact-symmetry artifact)
      ALL destabilized, collapsing from 3 clusters to 2 within t≈20–30 —
      an order of magnitude faster than the ~1500–2000 time units a random
      start takes to reach a locked state at all, i.e. these are not
      marginally unstable, they decay firmly.

    SCOPE: both tests used the default parameters already in this file
    (`repulsionStrength = 3.0`, `steepness = 20`). Whether a different
    repulsion strength opens a stable 3-cluster window is untested and NOT
    claimed either way — the finding above is specific to the parameters
    already committed to this file, not a claim about the mechanism in
    general. -/
noncomputable def repulsionGate (Δ : ℝ) (steepness : ℝ := 20) : ℝ :=
  smoothAttenuation (steepness * (phaseDistance Δ 0) ^ 2)

/-- Coupling force with a repulsive core added at Δ≈0.

    MOTIVATION / STATUS (validated numerically this session):
    Without this term, Δ=0 (perfect phase alignment between a pair) is a
    stable equilibrium of the pairwise dynamics — verified as an exact fixed
    point of the full N-node system with zero net force at every couplingWeight.
    Nothing in the model ever perturbed a locked state once reached, which was
    identified as the root cause of unbounded couplingWeight growth under
    sustained coherence.

    With `repulsionStrength` large enough (> resonanceField 0 / repulsionGate 0,
    i.e. > ~2 at the default steepness), Δ=0 becomes UNSTABLE and a new stable
    equilibrium Δ* > 0 appears nearby — confirmed analytically (f'(0) < 0) and
    in a full N=6 simulation (order parameter settles at r≈0.9956, never
    reaching 1.00000; local distortion settles at a genuine nonzero floor
    rather than collapsing to exactly zero).

    THIS DOES NOT, BY ITSELF, BOUND couplingWeight GROWTH. Swept both
    repulsionStrength and steepness numerically: the reachable equilibrium gap
    Δ* saturates far below the ~80-90° / d_i≈10 threshold needed to trip the
    plasticity brake (see plasticityDynamics doc comment), and there is no
    smooth path to larger Δ* — widening the core (lower steepness) mostly
    produces NO stable equilibrium at all (repulsion overwhelms attraction
    everywhere) rather than a continuously larger one. Forcing the equilibrium
    further out by tuning parameters would be exactly the kind of coercive
    parameter-chasing this framework is meant to avoid — the mechanism doesn't
    naturally reach that regime, so it's documented as a real but partial fix:
    it resolves the "perfect fusion" degeneracy (nodes maintain a nonzero
    floor of individual distinctness), not the unbounded-growth question. -/
noncomputable def couplingForceField (Δ : ℝ) (repulsionStrength : ℝ := 3.0) : ℝ :=
  (resonanceField Δ - repulsionStrength * repulsionGate Δ) * Real.sin Δ

-- Oddness is preserved: repulsionGate is even (phaseDistance is even in Δ,
-- since it depends on |sin(Δ/2)|), so [even envelope] * sin Δ is still odd,
-- matching InteractionPotential's requirements without any change to that
-- structure or its consistency proof.

noncomputable def IsSymmetricTopology (W : NetworkTopology ι) : Prop :=
  ∀ i j : ι, W i j = W j i

-- =========================================================================
-- 3. PLASTICITY: Slow evolution of node properties
-- =========================================================================

/-- Plasticity rule: couplingWeight evolves slowly via local resonance and distortion.
    This is non-coercive meta-dynamics — properties adjust based on experienced coherence.

    GATE FIX (validated numerically): the gate multiplying the rate is now
    `(1 - smoothAttenuation d_i)` rather than `smoothAttenuation d_i`. With the
    original gate, `smoothAttenuation d_i → 0` as distortion grows, which killed
    the magnitude of the correction term at exactly the distortion level where
    it should have been strongest — the sign of `(avg_resonance - 0.1*d_i)` was
    already correct at high distortion, but the gate suppressed it to ~1e-11,
    effectively *freezing* couplingWeight instead of shrinking it. The
    complementary gate agrees exactly with the original at d_i = 0 (both equal
    0.5), so near-synchrony dynamics are unchanged, but at high distortion it
    goes to 1 instead of 0, restoring genuine (and now numerically verified,
    ~9 orders of magnitude larger) shrinkage. This does NOT fix unbounded growth
    under sustained coherence — see naturalFrequency note above and Summary
    below; that is a separate, still-open structural gap. -/
noncomputable def plasticityDynamics (cfg : SystemConfig ι) (W : NetworkTopology ι) (τ : ι → ι → ℝ)
    (traj : ℝ → SystemState ι) (t : ℝ) (i : ι) : ℝ :=
  let props := cfg i
  let d_i := localDistortion W traj t i τ
  let avg_resonance := (1 / (Fintype.card ι : ℝ)) *
    ∑ j : ι, memeticBandwidth (traj (t - τ i j) j) (traj t i)

  -- Slow increase when coherent, tempered by distortion; gate stays active at
  -- high distortion instead of collapsing to zero (see doc comment above).
  0.01 * props.couplingWeight * (avg_resonance - 0.1 * d_i) * (1 - smoothAttenuation d_i)

/-- Full plastic system dynamics bundle. -/
structure FullDynamics where
  phase_accel : ℝ
  prop_plasticity : ℝ  -- e.g. for couplingWeight

noncomputable def fullAgapeDynamics (cfg : SystemConfig ι) (W : NetworkTopology ι) (τ : ι → ι → ℝ)
    (traj : ℝ → SystemState ι) (t : ℝ) (i : ι) : FullDynamics :=
  { phase_accel :=
      let props := cfg i
      let current := traj t i
      let coupling_force := props.couplingWeight * ∑ j : ι,
        W i j * couplingForceField ((traj (t - τ i j) j).phase - current.phase)
      let d_i := localDistortion W traj t i τ
      let friction := props.baselineFriction * smoothAttenuation d_i + props.distortionSens * d_i
      -- naturalFrequency drive: chosen so an isolated node (no coupling, d_i = 0)
      -- has steady-state velocity → naturalFrequency, since at that point
      -- friction = baselineFriction * smoothAttenuation 0 = baselineFriction * 0.5.
      -- NOT yet accounted for in `totalAgapeEnergy` / `agape_energy_decline` below —
      -- a nonzero naturalFrequency introduces an extra term in dE/dt that the
      -- current potential does not cancel. Flagging rather than silently
      -- extending the theorem's scope.
      let drive := props.baselineFriction * 0.5 * props.naturalFrequency
      (coupling_force - friction * current.velocity + drive) / props.mass,
    prop_plasticity := plasticityDynamics cfg W τ traj t i }

/-- A simple wrapper for phase-only dynamics (for energy proof). -/
noncomputable def agapePhaseDynamics (cfg : SystemConfig ι) (W : NetworkTopology ι) (τ : ι → ι → ℝ)
    (traj : ℝ → SystemState ι) (t : ℝ) (i : ι) : ℝ :=
  (fullAgapeDynamics cfg W τ traj t i).phase_accel

-- =========================================================================
-- 4. AXIOMATIC POTENTIAL
-- =========================================================================

structure InteractionPotential (G : ℝ → ℝ) : Prop where
  even_deriv : ∀ Δ, G (-Δ) = G Δ
  -- SIGN FIX (verified by hand, chain-rule derivation done twice independently):
  -- with the original `- couplingForceField Δ`, the cross terms in dE/dt from
  -- the kinetic and potential pieces of totalAgapeEnergy ADD instead of
  -- cancel, giving dE/dt = 2*Σ vᵢ·coupling_force_i/αᵢ - Σ friction_i·vᵢ²/αᵢ,
  -- which is not sign-definite and does not match agape_energy_decline's
  -- claim. Dropping the negation here makes the cross terms cancel exactly,
  -- so dE/dt = -Σ dissipation_i as claimed. even_deriv's consequence (G' odd)
  -- still holds either way since couplingForceField itself is odd.
  deriv      : ∀ Δ, HasDerivAt G (couplingForceField Δ) Δ

noncomputable def totalAgapeEnergy (cfg : SystemConfig ι) (W : NetworkTopology ι) (G : ℝ → ℝ)
    (traj : ℝ → SystemState ι) (t : ℝ) : ℝ :=
  let kinetic := Finset.sum Finset.univ (fun i : ι =>
    (cfg i).mass * (traj t i).velocity ^ 2 / (2 * (cfg i).couplingWeight))
  let potential := (1 / 2) * Finset.sum Finset.univ (fun i : ι =>
    Finset.sum Finset.univ (fun j : ι =>
      W i j * G ((traj t j).phase - (traj t i).phase)))
  kinetic + potential

-- =========================================================================
#min_imports