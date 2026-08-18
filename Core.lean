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
/-!
ADDITION TO Core.lean: repulsion_strength stability threshold.

STATUS: highest-risk Lean of this session -- arcsin API + neighborhood
transfer (HasDerivAt.congr_of_eventuallyEq), not the well-worn
.sum/.const_mul/.comp/.pow combinators used elsewhere. Confident in the
MATH, less confident in exact Mathlib names/signatures here. Two build
rounds in already; treat this as still-in-progress, not finished.

MATH SUMMARY: phaseDistance(Δ,0) = 2·arcsin|sin(Δ/2)| has a corner at
Δ=0 (built from |·|), but SQUARING it removes the corner:
  phaseDistance(Δ,0)² = Δ²   exactly, for Δ ∈ [-π,π]
via arcsin(|x|) = |arcsin(x)| (arcsin odd + monotonic). That's what makes
repulsionGate differentiable at 0 despite the |·| in its definition.

Then couplingForceField(Δ,rs) = f(Δ)·sin(Δ), f = resonanceField - rs·repulsionGate.
Product rule at Δ=0: f'(0)·sin(0) + f(0)·cos(0) = f(0) (f'(0) term vanishes
regardless of its value, since sin(0)=0 -- so neither resonanceField's nor
repulsionGate's derivative *value* at 0 is actually needed, only that both
exist). So couplingForceField'(0) = resonanceField(0) - rs·repulsionGate(0)
  = 1/(1+exp(-8)) - rs·(1/2),
negative (exact fusion unstable) exactly when rs > 2/(1+exp(-8)) ≈ 1.9993 --
slightly less than 2; the existing doc's "repulsionStrength > 2" is a good
approximation, not the exact value.
-/

-- Step 1: the corner-removing identity.
lemma phaseDistance_sq_eq (Δ : ℝ) (hΔ : Δ ∈ Set.Icc (-Real.pi) Real.pi) :
    phaseDistance Δ 0 ^ 2 = Δ ^ 2 := by
  unfold phaseDistance
  have hx1 : -(Real.pi / 2) ≤ Δ / 2 := by linarith [hΔ.1]
  have hx2 : Δ / 2 ≤ Real.pi / 2 := by linarith [hΔ.2]
  have harcsin : Real.arcsin (Real.sin (Δ / 2)) = Δ / 2 := Real.arcsin_sin hx1 hx2
  have hsin_nonneg : 0 ≤ Δ / 2 → 0 ≤ Real.sin (Δ / 2) := fun h =>
    Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hΔ.2])
  have hsin_neg : Δ / 2 < 0 → Real.sin (Δ / 2) < 0 := by
    intro h
    have hpos : 0 < -(Δ / 2) := by linarith
    have hlt : -(Δ / 2) < Real.pi := by linarith [hΔ.1, Real.pi_pos]
    have hpp := Real.sin_pos_of_pos_of_lt_pi hpos hlt
    rw [Real.sin_neg] at hpp
    linarith
  have habs : Real.arcsin |Real.sin (Δ / 2)| = |Δ / 2| := by
    by_cases h : (0:ℝ) ≤ Δ / 2
    · rw [abs_of_nonneg (hsin_nonneg h), harcsin, abs_of_nonneg h]
    · have h' : Δ / 2 < 0 := not_le.mp h
      rw [abs_of_neg (hsin_neg h'), Real.arcsin_neg, harcsin, abs_of_neg h']
  have hsub : (Δ - 0) / 2 = Δ / 2 := by ring
  rw [hsub, habs, mul_pow, sq_abs]
  ring

-- Step 2: repulsionGate matches a clean, corner-free closed form near 0.
lemma repulsionGate_eq_on_Icc (Δ steepness : ℝ) (hΔ : Δ ∈ Set.Icc (-Real.pi) Real.pi) :
    repulsionGate Δ steepness = smoothAttenuation (steepness * Δ ^ 2) := by
  unfold repulsionGate
  rw [phaseDistance_sq_eq Δ hΔ]

-- Step 3: smoothAttenuation is differentiable everywhere (division form,
-- matching the actual definition -- NOT (1+exp x)⁻¹).
lemma smoothAttenuation_hasDerivAt (x : ℝ) :
    HasDerivAt smoothAttenuation (-Real.exp x / (1 + Real.exp x) ^ 2) x := by
  unfold smoothAttenuation
  have h1 : HasDerivAt (fun y => 1 + Real.exp y) (Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_add 1
  have h2 := h1.inv (by positivity)
  have hfe : (fun y => 1 + Real.exp y)⁻¹ = fun distortion => 1 / (1 + Real.exp distortion) := by
    funext y
    show (1 + Real.exp y)⁻¹ = 1 / (1 + Real.exp y)
    rw [one_div]
  rw [hfe] at h2
  exact h2

-- Step 4: repulsionGate's derivative at 0 is exactly 0 (the outer
-- derivative's value doesn't matter -- it's multiplied by d/dΔ[Δ²]=2Δ=0).
lemma repulsionGate_hasDerivAt_zero (steepness : ℝ) :
    HasDerivAt (fun Δ => repulsionGate Δ steepness) 0 0 := by
  have hsq : HasDerivAt (fun Δ : ℝ => steepness * Δ ^ 2) 0 0 := by
    have h := (hasDerivAt_pow 2 (0 : ℝ)).const_mul steepness
    simpa using h
  have houter := smoothAttenuation_hasDerivAt (steepness * (0 : ℝ) ^ 2)
  have hcomp := houter.comp 0 hsq
  have heq0 : (-Real.exp (steepness * (0 : ℝ) ^ 2) / (1 + Real.exp (steepness * (0 : ℝ) ^ 2)) ^ 2) * 0 = 0 := by
    ring
  rw [heq0] at hcomp
  have hfe : (smoothAttenuation ∘ fun Δ : ℝ => steepness * Δ ^ 2)
      = fun Δ => smoothAttenuation (steepness * Δ ^ 2) := by
    funext Δ
    rfl
  rw [hfe] at hcomp
  have hnb : Set.Icc (-Real.pi) Real.pi ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnb] with Δ hΔ
  exact repulsionGate_eq_on_Icc Δ steepness hΔ

-- Step 5: resonanceField's existence (not closed form -- it's multiplied
-- by sin(0)=0 downstream, so the value never matters). fun_prop was tried
-- here twice and failed both times (couldn't auto-discharge the nonzero
-- denominator side-condition), so this is a fully manual HasDerivAt chain
-- instead, using a metavariable for the derivative value since only the
-- function *shape* needs to match, not the exact value.
--
-- BUILD FIX (confirmed against actual `lake build` error): the original
-- version of this proof built hE/hF via `.div`/`.mul` with no type
-- ascription, then tried to bridge the result to a pointwise `fun x => _`
-- shape with a `funext x; rfl`-proved rewrite (`hfe`), deferring the
-- existential witness via `refine ⟨_, ?_⟩`. `.div`/`.mul` in this Mathlib
-- version produce their HasDerivAt conclusion using Pi-level `/`/`*`
-- notation rather than a pointwise lambda -- defeq-equal (that's exactly
-- how the Pi instances unfold) but not syntactically matched by `rw`, and
-- with the witness left as a deferred metavariable via `refine ⟨_, ?_⟩`,
-- Lean gave up on solving it ("don't know how to synthesize placeholder
-- for argument `w`" -- `w` being Exists.intro's witness parameter name)
-- before the later `exact hF` could pin it down.
--
-- Fix: ascribe the intended pointwise-lambda type directly on hE and hF,
-- forcing Lean to check the assignment via defeq instead of leaving the
-- shape to whatever `.div`/`.mul` happen to emit -- this removes the need
-- for `hfe`/`rw` entirely. Then close with a single `exact ⟨_, hF⟩` at the
-- very end (no gap between introducing the witness and fixing it).
lemma resonanceField_hasDerivAt_zero : ∃ D : ℝ, HasDerivAt resonanceField D 0 := by
  have hne : (1:ℝ) + Real.exp (-8 * Real.cos (0:ℝ)) ≠ 0 := by positivity
  have hcos : HasDerivAt Real.cos (-Real.sin 0) 0 := Real.hasDerivAt_cos 0
  have hA : HasDerivAt (fun x => (1 + Real.cos x) / 2) ((-Real.sin 0) / 2) 0 :=
    (hcos.const_add 1).div_const 2
  have hB : HasDerivAt (fun x => -8 * Real.cos x) (-8 * -Real.sin 0) 0 := hcos.const_mul (-8)
  have hC : HasDerivAt (fun x => Real.exp (-8 * Real.cos x))
      (Real.exp (-8 * Real.cos 0) * (-8 * -Real.sin 0)) 0 := hB.exp
  have hD : HasDerivAt (fun x => 1 + Real.exp (-8 * Real.cos x))
      (Real.exp (-8 * Real.cos 0) * (-8 * -Real.sin 0)) 0 := hC.const_add 1
  have hE : HasDerivAt (fun x => 1 / (1 + Real.exp (-8 * Real.cos x)))
      ((0 * (1 + Real.exp (-8 * Real.cos 0))
          - 1 * (Real.exp (-8 * Real.cos 0) * (-8 * -Real.sin 0)))
        / (1 + Real.exp (-8 * Real.cos 0)) ^ 2) 0 :=
    (hasDerivAt_const (0:ℝ) (1:ℝ)).div hD hne
  have hF : HasDerivAt
      (fun x => (1 + Real.cos x) / 2 * (1 / (1 + Real.exp (-8 * Real.cos x))))
      ((-Real.sin 0 / 2) * (1 / (1 + Real.exp (-8 * Real.cos 0)))
        + (1 + Real.cos 0) / 2
          * ((0 * (1 + Real.exp (-8 * Real.cos 0))
                - 1 * (Real.exp (-8 * Real.cos 0) * (-8 * -Real.sin 0)))
              / (1 + Real.exp (-8 * Real.cos 0)) ^ 2)) 0 :=
    hA.mul hE
  have hgoal : resonanceField
      = fun phase_diff => (1 + Real.cos phase_diff) / 2
          * (1 / (1 + Real.exp (-8 * Real.cos phase_diff))) := by
    funext x
    simp only [resonanceField]
  rw [hgoal]
  exact ⟨_, hF⟩

-- Step 6: couplingForceField's derivative at Δ=0, in closed form.
-- NOTE: couplingForceField itself has no independent steepness parameter
-- -- it calls repulsionGate Δ using THAT function's own default (20).
-- So this theorem is only over repulsionStrength, with repulsionGate 0
-- implicitly at steepness=20, matching couplingForceField's actual body.
theorem couplingForceField_hasDerivAt_zero (repulsionStrength : ℝ) :
    HasDerivAt (fun Δ => couplingForceField Δ repulsionStrength)
      (resonanceField 0 - repulsionStrength * repulsionGate 0) 0 := by
  unfold couplingForceField
  obtain ⟨D, hD⟩ := resonanceField_hasDerivAt_zero
  have hgate := repulsionGate_hasDerivAt_zero (20 : ℝ)
  have hf : HasDerivAt (fun Δ => resonanceField Δ - repulsionStrength * repulsionGate Δ 20)
      (D - repulsionStrength * 0) 0 := hD.sub (hgate.const_mul repulsionStrength)
  have hsin : HasDerivAt Real.sin (Real.cos 0) 0 := Real.hasDerivAt_sin 0
  have hprod := hf.mul hsin
  have hfe : ((fun Δ => resonanceField Δ - repulsionStrength * repulsionGate Δ 20) * Real.sin)
      = fun Δ => (resonanceField Δ - repulsionStrength * repulsionGate Δ 20) * Real.sin Δ := by
    funext Δ
    rfl
  rw [hfe] at hprod
  have heq : (D - repulsionStrength * 0) * Real.sin 0
      + (resonanceField 0 - repulsionStrength * repulsionGate 0 20) * Real.cos 0
      = resonanceField 0 - repulsionStrength * repulsionGate 0 20 := by
    simp
  rw [heq] at hprod
  exact hprod

-- Step 7: the threshold. Exact fusion (Δ=0) is linearly unstable exactly
-- when repulsionStrength exceeds 2/(1+exp(-8)) -- very slightly less than
-- 2 (exp(-8) ≈ 0.000335). Stated in cross-multiplied form to avoid any
-- division-vs-product rewriting fragility.
theorem exact_fusion_unstable_iff (repulsionStrength : ℝ) :
    resonanceField 0 - repulsionStrength * repulsionGate 0 < 0
      ↔ 2 < repulsionStrength * (1 + Real.exp (-8)) := by
  have hexp : (0:ℝ) < 1 + Real.exp (-8) := by positivity
  have h_res : resonanceField 0 = 1 / (1 + Real.exp (-8)) := by
    unfold resonanceField
    simp only [Real.cos_zero]
    norm_num
  have hpd : phaseDistance 0 0 = 0 := by
    unfold phaseDistance
    norm_num [Real.sin_zero, Real.arcsin_zero]
  have h_rep : repulsionGate 0 = 1 / 2 := by
    unfold repulsionGate
    rw [hpd]
    unfold smoothAttenuation
    norm_num [Real.exp_zero]
  have hstep : (1 / (1 + Real.exp (-8)) - repulsionStrength * (1 / 2) < 0)
      ↔ (1 / (1 + Real.exp (-8)) < repulsionStrength * (1 / 2)) := by
    constructor <;> intro h <;> linarith
  have hkey : (1:ℝ) / (1 + Real.exp (-8)) * (1 + Real.exp (-8)) = 1 := by
    field_simp
  rw [h_res, h_rep, hstep]
  constructor
  · intro h
    nlinarith [mul_lt_mul_of_pos_right h hexp, hkey]
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hexp.le, hkey]

#min_imports
