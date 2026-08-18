import AGAPE.Core
import Mathlib

/-! ### Energy.lean — Section 6: energy decline (symmetric-topology case)
Includes couplingForceField_odd (extracted from AgapeEnergy(3).lean — this
lemma is used by the asymmetry-residual derivation in Plasticity.lean for
the sign-flip/relabeling step, but was never carried over when that file
branched off the Energy lineage; it belongs here since it's fundamentally
a property of couplingForceField itself, defined in Core.lean).
-/
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- 5. LEMMA: Non-negative dissipation
-- =========================================================================

lemma dissipation_nonneg (cfg : SystemConfig ι) (W : NetworkTopology ι)
    (traj : ℝ → SystemState ι) (t : ℝ) (τ : ι → ι → ℝ := fun _ _ => 0)
    (hpos : ∀ i, (cfg i).Pos)
    (hW_nonneg : ∀ i j, 0 ≤ W i j) :  -- ← new hypothesis
    ∀ i : ι,
      ((cfg i).baselineFriction * smoothAttenuation (localDistortion W traj t i τ) +
       (cfg i).distortionSens * localDistortion W traj t i τ) ≥ 0 := by
  intro i
  have h_fric : (cfg i).baselineFriction ≥ 0 := (hpos i).friction_pos.le
  have h_att : smoothAttenuation (localDistortion W traj t i τ) ≥ 0 := by
    unfold smoothAttenuation
    positivity
  have h_sens : (cfg i).distortionSens ≥ 0 := (hpos i).sens_pos

  have h_dist : localDistortion W traj t i τ ≥ 0 := by
    unfold localDistortion
    apply Finset.sum_nonneg
    intro x hx
    have h_sq : 0 ≤ phaseDistance (traj (t - τ i x) x).phase (traj t i).phase * phaseDistance (traj (t - τ i x) x).phase (traj t i).phase :=
      mul_self_nonneg _
    have h_W_nonneg : 0 ≤ W i x := hW_nonneg i x  -- ← fixed
    exact mul_nonneg h_W_nonneg (sq_nonneg _)
  nlinarith

-- =========================================================================
-- 6. MAIN THEOREM (towards formalization)
-- =========================================================================

-- =========================================================================
-- couplingForceField_odd (relocated here from end-of-file: agape_energy_decline
-- below needs it, and Lean doesn't allow forward references).
lemma couplingForceField_odd : ∀ Δ, couplingForceField (-Δ) = -couplingForceField Δ := by
  intro Δ
  have hRes : resonanceField (-Δ) = resonanceField Δ := by
    simp [resonanceField, Real.cos_neg]
  have hPhase : phaseDistance (-Δ) 0 = phaseDistance Δ 0 := by
    unfold phaseDistance
    have h1 : (-Δ - 0) / 2 = -(Δ / 2) := by rw [sub_zero, neg_div]
    have h2 : (Δ - 0) / 2 = Δ / 2 := by rw [sub_zero]
    rw [h1, h2]
    congr 1
    simp [Real.sin_neg]
  have hGate : repulsionGate (-Δ) 20 = repulsionGate Δ 20 := by
    unfold repulsionGate
    rw [hPhase]
  unfold couplingForceField
  rw [hRes, hGate, Real.sin_neg]
  exact mul_neg _ _

-- =========================================================================
theorem agape_energy_decline
    (cfg : SystemConfig ι)
    (W : NetworkTopology ι)
    (hW : IsSymmetricTopology W)
    (hpos : ∀ i, (cfg i).Pos)
    (hω : ∀ i, (cfg i).naturalFrequency = 0)
    (G : ℝ → ℝ)
    (hG : InteractionPotential G)
    (traj : ℝ → SystemState ι)
    (h_phase : ∀ t i, HasDerivAt (fun s => (traj s i).phase) (traj t i).velocity t)
    (h_vel   : ∀ t i, HasDerivAt (fun s => (traj s i).velocity)
                      (agapePhaseDynamics cfg W (fun _ _ => 0) traj t i) t) :
    ∀ t : ℝ,
      let dissipation i :=
        ((cfg i).baselineFriction * smoothAttenuation (localDistortion W traj t i (fun _ _ => 0)) +
         (cfg i).distortionSens * localDistortion W traj t i (fun _ _ => 0)) *
        (traj t i).velocity ^ 2 / (cfg i).couplingWeight
      HasDerivAt (totalAgapeEnergy cfg W G traj)
        (- ∑ i : ι, dissipation i) t := by
  intro t
  set v : ι → ℝ := fun i => (traj t i).velocity with hv_def
  set V : ι → ℝ := fun i => agapePhaseDynamics cfg W (fun _ _ => 0) traj t i with hV_def
  set dissipation : ι → ℝ := fun i =>
    ((cfg i).baselineFriction * smoothAttenuation (localDistortion W traj t i (fun _ _ => 0)) +
     (cfg i).distortionSens * localDistortion W traj t i (fun _ _ => 0)) * v i ^ 2 /
      (cfg i).couplingWeight with hdiss_def
  -- KINETIC DERIVATIVE
  have hkin : HasDerivAt
      (fun s => ∑ i : ι, (cfg i).mass * (traj s i).velocity ^ 2 / (2 * (cfg i).couplingWeight))
      (∑ i : ι, (cfg i).mass * (2 * v i * V i) / (2 * (cfg i).couplingWeight)) t := by
    have h : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt
        (fun s => (cfg i).mass * (traj s i).velocity ^ 2 / (2 * (cfg i).couplingWeight))
        ((cfg i).mass * (2 * v i * V i) / (2 * (cfg i).couplingWeight)) t := by
      intro i _
      have h1 := (((h_vel t i).pow 2).const_mul (cfg i).mass).div_const (2 * (cfg i).couplingWeight)
      simpa [pow_one, mul_comm, mul_assoc, mul_left_comm] using h1
    have hraw := HasDerivAt.sum h
    have hfe : (∑ i : ι, fun s => (cfg i).mass * (traj s i).velocity ^ 2 / (2 * (cfg i).couplingWeight))
        = fun s => ∑ i : ι, (cfg i).mass * (traj s i).velocity ^ 2 / (2 * (cfg i).couplingWeight) := by
      funext s; simp
    rw [hfe] at hraw
    exact hraw
  -- POTENTIAL DERIVATIVE
  have hpot : HasDerivAt
      (fun s => (1 / 2 : ℝ) * ∑ i : ι, ∑ j : ι, W i j * G ((traj s j).phase - (traj s i).phase))
      ((1 / 2 : ℝ) * ∑ i : ι, ∑ j : ι,
        W i j * (couplingForceField ((traj t j).phase - (traj t i).phase) * (v j - v i))) t := by
    apply HasDerivAt.const_mul
    have hinner : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt
        (fun s => ∑ j : ι, W i j * G ((traj s j).phase - (traj s i).phase))
        (∑ j : ι, W i j * (couplingForceField ((traj t j).phase - (traj t i).phase) * (v j - v i))) t := by
      intro i _
      have hj : ∀ j ∈ (Finset.univ : Finset ι), HasDerivAt
          (fun s => W i j * G ((traj s j).phase - (traj s i).phase))
          (W i j * (couplingForceField ((traj t j).phase - (traj t i).phase) * (v j - v i))) t := by
        intro j _
        apply HasDerivAt.const_mul
        have hΔ : HasDerivAt (fun s => (traj s j).phase - (traj s i).phase) (v j - v i) t :=
          (h_phase t j).sub (h_phase t i)
        have hGd := hG.deriv ((traj t j).phase - (traj t i).phase)
        have hraw := hGd.comp t hΔ
        have hfe : (G ∘ fun s => (traj s j).phase - (traj s i).phase)
            = fun s => G ((traj s j).phase - (traj s i).phase) := by
          funext s; simp [Function.comp]
        rw [hfe] at hraw
        exact hraw
      have hraw := HasDerivAt.sum hj
      have hfe : (∑ j : ι, fun s => W i j * G ((traj s j).phase - (traj s i).phase))
          = fun s => ∑ j : ι, W i j * G ((traj s j).phase - (traj s i).phase) := by
        funext s; simp
      rw [hfe] at hraw
      exact hraw
    have hraw2 := HasDerivAt.sum hinner
    have hfe2 : (∑ i : ι, fun s => ∑ j : ι, W i j * G ((traj s j).phase - (traj s i).phase))
        = fun s => ∑ i : ι, ∑ j : ι, W i j * G ((traj s j).phase - (traj s i).phase) := by
      funext s; simp
    rw [hfe2] at hraw2
    exact hraw2
  have htot := hkin.add hpot
  -- Per-node kinetic identity: unfolds V i via agapePhaseDynamics, cancels
  -- mass and couplingWeight (using hpos), and kills the drive term (using hω).
  -- This is the single riskiest step in this proof — the rest is standard
  -- HasDerivAt combinators and a Finset-sum relabeling I'm confident in.
  have hkin_pointwise : ∀ i : ι,
      (cfg i).mass * (2 * v i * V i) / (2 * (cfg i).couplingWeight)
      = v i * (∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase))
        - dissipation i := by
    intro i
    have hm : (cfg i).mass ≠ 0 := (hpos i).mass_pos.ne'
    have hα : (cfg i).couplingWeight ≠ 0 := (hpos i).weight_pos.ne'
    have hVunfold :
        (cfg i).mass * V i =
          (cfg i).couplingWeight *
              (∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase))
            - (((cfg i).baselineFriction *
                  smoothAttenuation (localDistortion W traj t i (fun _ _ => 0)) +
                (cfg i).distortionSens * localDistortion W traj t i (fun _ _ => 0)) * v i) := by
      show (cfg i).mass * agapePhaseDynamics cfg W (fun _ _ => 0) traj t i = _
      unfold agapePhaseDynamics fullAgapeDynamics
      dsimp only
      simp only [sub_zero, hω i, mul_zero, add_zero]
      field_simp
      ring
    have hstep : (cfg i).mass * (2 * v i * V i)
        = 2 * v i * ((cfg i).couplingWeight *
              (∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase))
            - (((cfg i).baselineFriction *
                  smoothAttenuation (localDistortion W traj t i (fun _ _ => 0)) +
                (cfg i).distortionSens * localDistortion W traj t i (fun _ _ => 0)) * v i)) := by
      have hre : (cfg i).mass * (2 * v i * V i) = 2 * v i * ((cfg i).mass * V i) := by ring
      rw [hre, hVunfold]
    rw [hstep, hdiss_def]
    field_simp
  -- Combine and finish: sum the per-node identity, then relabel the
  -- cross-coupling piece of the potential derivative via hW + couplingForceField_odd.
  have heq :
      (∑ i : ι, (cfg i).mass * (2 * v i * V i) / (2 * (cfg i).couplingWeight)) +
        ((1 / 2 : ℝ) * ∑ i : ι, ∑ j : ι,
          W i j * (couplingForceField ((traj t j).phase - (traj t i).phase) * (v j - v i))) =
      - ∑ i : ι, dissipation i := by
    rw [Finset.sum_congr rfl (fun i _ => hkin_pointwise i), Finset.sum_sub_distrib]
    have hterm1 :
        (∑ i : ι, v i * ∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase))
        = ∑ i : ι, ∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hexpand :
        ((1 / 2 : ℝ) * ∑ i : ι, ∑ j : ι,
          W i j * (couplingForceField ((traj t j).phase - (traj t i).phase) * (v j - v i)))
        = (1 / 2 : ℝ) *
            ((∑ i : ι, ∑ j : ι,
                W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v j)
              - ∑ i : ι, ∑ j : ι,
                W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v i) := by
      rw [← Finset.sum_sub_distrib]
      apply congrArg
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hS1 :
        (∑ i : ι, ∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v j)
        = - ∑ i : ι, ∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v i := by
      have hcomm :
          (∑ i : ι, ∑ j : ι, W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v j)
          = ∑ i : ι, ∑ j : ι, W j i * couplingForceField ((traj t i).phase - (traj t j).phase) * v i :=
        Finset.sum_comm
      have hsum0 :
          (∑ i : ι, ∑ j : ι,
              W i j * couplingForceField ((traj t j).phase - (traj t i).phase) * v i)
            + (∑ i : ι, ∑ j : ι,
                W j i * couplingForceField ((traj t i).phase - (traj t j).phase) * v i) = 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro j _
        rw [hW j i]
        have hΔ : (traj t i).phase - (traj t j).phase
            = -((traj t j).phase - (traj t i).phase) := by ring
        rw [hΔ, couplingForceField_odd]
        ring
      rw [hcomm]
      exact eq_neg_of_add_eq_zero_right hsum0
    rw [hterm1, hexpand, hS1]
    ring
  rw [heq] at htot
  exact htot

/-!
## Summary of Plastic + Proof Structure — status as of this session

Fixes applied this session (all validated numerically, not yet mechanically
checked in Lean beyond the hand chain-rule derivation noted above):

1. **Sign fix, `InteractionPotential.deriv`**: removed an erroneous negation.
   Without the fix, `agape_energy_decline`'s claim is false as stated (cross
   terms add, not cancel). With it, the claim is true for τ=0, ω=0.
2. **Gate fix, `plasticityDynamics`**: `smoothAttenuation d_i` → `(1 -
   smoothAttenuation d_i)`. Original gate suppressed the shrinkage-side
   correction to ~1e-11 at high distortion (sign right, magnitude dead —
   effectively froze couplingWeight instead of shrinking it). Fix verified
   numerically to restore ~9 orders of magnitude more shrinkage at the same
   distortion level, while leaving near-synchrony (d_i≈0) dynamics unchanged
   (both gates equal 0.5 there).
3. **naturalFrequency field added**, wired into `fullAgapeDynamics` as a
   constant drive. Tested as a candidate mechanism to bound couplingWeight
   growth under sustained coherence — numerically REFUTED: locked-state phase
   lag scales as ω_i/α_i, so growing couplingWeight self-consistently drives
   distortion back toward zero regardless of frequency heterogeneity
   (confirmed d_i ~ (Δω/α)² to high numerical precision). Not yet incorporated
   into the energy theorem — see note in Section 6.
4. **Positivity**: `dissipation_nonneg`'s `sorry` on distortionSens positivity
   replaced with an explicit `NodeProperties.Pos` hypothesis rather than an
   unstated assumption.

Still open / still `sorry`:

- `agape_energy_decline`'s main derivative claim — statement is now correct
  for τ=0, ω=0, and a full chain-rule + `hW`/`couplingForceField_odd`
  cancellation proof has been written (no `sorry` remains), requiring two
  hypotheses (`hpos`, `hω`) that the statement was implicitly relying on but
  never declared. NOT YET RUN THROUGH `lake build` — no toolchain access when
  written; treat as unverified until it compiles.
- **The real open problem, found this session**: under sustained coherence
  (any trajectory that phase-locks), `localDistortion → 0` and nothing in the
  current definitions — not the gate, not naturalFrequency, not damping-ratio
  effects (checked: the system stays linearly stable, just increasingly
  underdamped, ζ ~ 1/√α, never unstable) — ever perturbs it back up. Numerically
  confirmed unbounded exponential growth of couplingWeight under near-synchrony
  initial conditions (α: 1 → ~4150 by t=2000 in an N=6 all-to-all test). This
  is a structural property of the multiplicative growth law
  `dα/dt = 0.01·α·(...)` combined with the total absence, anywhere in
  NodeProperties, of a mechanism that reintroduces distortion once a locked
  state is reached. Not resolved by any fix applied this session.

5. **repulsionGate / near-field repulsion added to `couplingForceField`**.
   Second candidate mechanism tried (after naturalFrequency). Fixes a real,
   separate degeneracy: without it, perfect phase alignment (Δ=0) is a stable
   equilibrium and an exact fixed point of the full system at every
   couplingWeight — confirmed nothing ever perturbs it once reached. With
   repulsion, Δ=0 becomes unstable and a genuine nonzero equilibrium gap
   appears (confirmed numerically: order parameter settles at r≈0.9956, never
   1.00000). Also numerically REFUTED as a fix for unbounded growth: the
   reachable equilibrium gap saturates well below the distortion level needed
   to engage the plasticity brake, with no smooth parameter path to push it
   further — only a narrow window between "negligible" and "no stable
   equilibrium exists at all."

Two candidate self-referential ceilings tried and ruled out this session
(naturalFrequency, repulsionGate) — both real, useful additions to the model
in their own right, neither closes the growth question. A third mechanism,
attention-budget coupling, is documented separately in Section 7 below —
now with a working fix for its own failure mode (exclusivity drift); see the
updated status there.
-/
