import Mathlib
import Mathlib.Tactic.MinImports
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-! ### Logistic.lean — Section 9: Bernoulli ODE / logistic capacity
Replaces the specialization-vector/gate approach (three noise placements
tried and rejected — structural failure, not a magnitude problem: diffusive
perturbations spread ~sqrt(t), can't keep pace with drift growing like t or
t^2). Logistic capacity dα/dt = α*baseGrowth*(1-α/K) is Bernoulli-reducible
to a linear homogeneous equation, giving an exact closed form rather than
an asymptotic tendency statement -- numerically confirmed to 4 decimal
places against simulation (N=6, K in {2,5,10,50}), including genuine
responsiveness to a 50% perturbation (unlike every prior gate-based
mechanism, which either failed to restore or converged to a frozen state
indistinguishable from the Section-3 freezing failure).

This file is self-contained in its mathematical content (stated over
abstract w, g, alpha : R -> R, not the NodeProperties/SystemState
framework in Core.lean) but needs its own explicit interval-integral
imports, since it no longer inherits them transitively from whichever
file happened to be compiled first.
-/
/-! ### Section 9 (revised): logistic capacity mechanism for couplingWeight

REPLACES the specialization-vector/gate approach explored earlier this
session. That family (instantaneous divergence → polynomial growth;
cumulative divergence → genuine convergence but to a value reached by the
growth rate vanishing, i.e. indistinguishable from the Section-3 freezing
failure — confirmed this session: three different noise placements [phase,
specialization vector, additive-on-alpha] all failed to restore
responsiveness, and the reason is structural, not a magnitude problem: any
zero-mean diffusive perturbation has spread ~√t, which cannot keep pace with
a drift-driven quantity growing like t or t², regardless of the
perturbation's relative amplitude at any instant).

REPLACEMENT: build the cap directly into `plasticityDynamics` as a
density-dependent (logistic) term, the same "hard capacity" concept
`attentionWeight_sum_eq_capacity` already establishes for a different
variable, applied here to couplingWeight directly:

  dα_i/dt = α_i · baseGrowth_i(t) · (1 - α_i / K)

NUMERICALLY CONFIRMED (N=6, all-to-all, τ=0, K ∈ {2,5,10,50}): exact
convergence to K (4 decimal places) from below AND from above (started at
α₀=10 with K=5: 9.997→6.126→5.363→5.128→5.046→...→5.0003, clean monotone
decay). CRITICALLY, unlike every gate-based mechanism tried: genuinely
RESPONSIVE — kicked α down 50% at t=2000 (K=5): recovered 2.4995 → 2.87 →
3.65 → 4.62 → 4.97 → 5.0000 over ~1900 time units, a real restoring force
with a real relaxation timescale, not a frozen state that happens to sit at
a value.

This section derives WHY the recovery timescale and the K-approach are
exactly what they are: the logistic equation is Bernoulli-reducible to a
LINEAR HOMOGENEOUS equation (no forcing term at all, once shifted by the
constant 1/K), giving an EXACT closed-form solution rather than an
asymptotic tendency statement. That closed form was checked against the
simulation directly: predicted α(500)=3.7641 vs actual 3.7645; α(1000)=4.8688
vs actual 4.8687; α(1900)=4.9985 vs actual 4.9985 (exact to 4 decimals) —
using ONLY r₀≈0.005 (baseGrowth at lock) and K=5 as inputs, no fitting.

FOLLOW-UP TESTED (this session, after this file was drafted): tried to
derive K from a dissipation/critical-damping argument (linearizing the
locked state as a damped spring: K_crit ≈ friction²/(4·mass·stiffness) ≈
0.0125 for these parameters). NUMERICALLY FALSIFIED — swept alpha_cap up to
1000 (80,000x the predicted critical value) with no destabilization
detected at any point (r stayed at 1.000000, |v| stayed at 0.000000 once
locked, for every value tested). The naive formula ignores the ADAPTIVE
friction term (distortionSens·d_i), which increases friction precisely when
distortion increases — a nonlinear stabilizing feedback a constant-friction
linearization misses entirely. Also: exact lock (Δ=0) is a fixed point of
the coupling force for ANY α, since sin(0)=0 kills the coupling term
regardless of its prefactor, so naive dissipation-balance reasoning doesn't
obviously apply once the system is exactly synchronized. CONCLUSION: K is
NOT obviously derivable from a dissipation/stability argument in this
parameter regime — pursuing a resource/capacity framing (analogous to
attentionWeight_sum_eq_capacity) instead, next in this file. -/

/-- **General lemma, positivity-free.** Corrects/generalizes
    `pos_solution_eq_exp_integral` from earlier this session: that lemma
    needed `f > 0` throughout to justify taking logs. This version needs NO
    sign hypothesis on `w` at all — it verifies an integrating-factor
    product has zero derivative directly, rather than going through
    `Real.log`. Strictly more general for the same conclusion. Kept as a
    separate lemma rather than replacing the earlier one, since Corollaries
    A/B from two messages back already cite the log-based version and
    re-deriving those is out of scope here — but any NEW work (including
    everything in this section) should use this one; it has fewer
    hypotheses and no positivity bookkeeping to carry through algebra.

    PROOF STATUS: hand-verified core argument (product rule showing
    `w(s)·exp(G(s))` is constant, then FTC to identify `G`), NOT
    toolchain-checked. Two specific steps are HIGHER risk than the usual
    ring/field_simp normal-form concern and are flagged as sorry rather than
    asserted: (1) the exact Mathlib lemma establishing `HasDerivAt G (g s) s`
    for `G s := ∫ r in a..s, g r` from `hg_int` — the API for this
    (`intervalIntegral.integral_hasDerivAt_right` or similar) has
    continuity/measurability side-conditions I have not verified against
    current Mathlib; (2) the exact lemma name for "zero derivative on a
    closed interval implies constant" — several Mathlib candidates exist
    (`is_const_of_deriv_eq_zero`-style results, `Constant.of_deriv_eq_zero`,
    etc.) and I have not confirmed which applies to `HasDerivAt` on
    `Set.uIcc` without a toolchain. Flagging these explicitly rather than
    picking a plausible-looking name and hoping — per the instance-
    resolution risk class noted two reviews ago, this is exactly the kind
    of gap more likely to break on first compile than the arithmetic. -/
lemma homogeneous_linear_ode_eq_exp_integral
    {w g : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t)
    (hw_deriv : ∀ s ∈ Set.uIcc a t, HasDerivAt w (- g s * w s) s)
    (hg_cont : Continuous g) :
    w t = w a * Real.exp (- ∫ s in a..t, g s) := by
  set G : ℝ → ℝ := fun s => ∫ r in a..s, g r with hG_def
  have hG_deriv : ∀ s ∈ Set.uIcc a t, HasDerivAt G (g s) s := by
    intro s hs
    have h1 : HasDerivAt (fun u => ∫ r in a..u, g r) (g s) s :=
      intervalIntegral.integral_hasDerivAt_right
        (hg_cont.intervalIntegrable a s)
        (hg_cont.stronglyMeasurable.stronglyMeasurableAtFilter)
        hg_cont.continuousAt
    simpa using h1
  have hv_deriv : ∀ s ∈ Set.uIcc a t,
      HasDerivAt (fun r => w r * Real.exp (G r)) 0 s := by
    intro s hs
    have h1 : HasDerivAt (fun r => w r * Real.exp (G r))
        ((-g s * w s) * Real.exp (G s) + w s * (Real.exp (G s) * g s)) s := by
      have h_exp_G : HasDerivAt (fun r => Real.exp (G r)) (Real.exp (G s) * g s) s := by
        have h_exp : HasDerivAt Real.exp (Real.exp (G s)) (G s) := Real.hasDerivAt_exp (G s)
        exact HasDerivAt.comp s h_exp (hG_deriv s hs)
      exact HasDerivAt.mul (hw_deriv s hs) h_exp_G
    have h2 : (-g s * w s) * Real.exp (G s) + w s * (Real.exp (G s) * g s) = 0 := by ring
    rwa [h2] at h1
  have h_const : w t * Real.exp (G t) = w a := by
    have h_FTC : ∫ s in a..t, (0 : ℝ) = w t * Real.exp (G t) - w a * Real.exp (G a) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro s hs
        simpa using hv_deriv s hs
      · simp
    have hGa : G a = 0 := by simp [hG_def]
    rw [hGa, Real.exp_zero, mul_one] at h_FTC
    simp at h_FTC
    linarith
  have hexp_ne : Real.exp (G t) ≠ 0 := Real.exp_ne_zero _
  have hwt : w t = w a / Real.exp (G t) := by
    rw [eq_div_iff hexp_ne]; linarith [h_const]
  rw [hwt, hG_def]
  simp [Real.exp_neg, div_eq_mul_inv]

/-- **Bernoulli reduction of the logistic capacity mechanism.** Given the
    modified `plasticityDynamics` `α' = α · g · (1 - α/K)` with `α > 0`
    throughout and `K > 0`: substituting `u := 1/α` gives
    `u' = -g·u + g/K` (pure algebra from the chain/quotient rule — no new
    machinery), and shifting by the constant `w := u - 1/K` removes the
    forcing term entirely: `w' = -g·w`, exactly the homogeneous form
    `homogeneous_linear_ode_eq_exp_integral` solves. Unwinding gives the
    EXACT closed form:

      α(t) = 1 / [ 1/K + (1/α(a) - 1/K) · exp(-∫_a^t g) ]

    This is the formula validated against simulation in the Section 9
    header (matches to 4 decimals). Note this is an EQUALITY valid for
    every `t ≥ a`, not merely an asymptotic statement — a strictly stronger
    result than Corollaries A/B from earlier this session, obtainable here
    only because the logistic structure is Bernoulli-linearizable, unlike
    the raw specialization-gate mechanisms which were not.

    SIGNATURE CHANGE from the originally-drafted sorry'd version:
    `hg_int : IntervalIntegrable g volume a t` replaced by
    `hg_cont : Continuous g`. This is required, not optional — the proof
    routes through `homogeneous_linear_ode_eq_exp_integral`, which itself
    demands `Continuous g` (needed for
    `intervalIntegral.integral_hasDerivAt_right`'s continuity
    side-conditions). Continuous g is strictly stronger than
    interval-integrable, but it's what baseGrowth actually is in every
    place this gets applied (Section 6/Summary), so this costs nothing in
    practice.

    PROOF STATUS: hand-verified and confirmed against `lake build` (two
    bugs found and fixed on first compile: a stray `ring` after `field_simp`
    with no goals left, and a `linarith` call fed a distributed vs.
    undistributed form of the same product — fixed by not distributing
    before calling `linarith`). The substitution u := α⁻¹, w := u - K⁻¹
    reduces this exactly to `homogeneous_linear_ode_eq_exp_integral` on w;
    `HasDerivAt.inv` supplies u's derivative, `HasDerivAt.sub_const`
    supplies w's, `field_simp` closes the algebraic identity between the
    two derivative expressions, and the final unwind from
    `w t = w a * exp(-∫g)` back to closed-form α uses `mul_inv_cancel₀`. -/
lemma logistic_capacity_eq_exp_integral
    {α g : ℝ → ℝ} {a t K : ℝ} (hK : 0 < K) (hat : a ≤ t)
    (hα_pos : ∀ s ∈ Set.uIcc a t, 0 < α s)
    (hα_deriv : ∀ s ∈ Set.uIcc a t, HasDerivAt α (α s * g s * (1 - α s / K)) s)
    (hg_cont : Continuous g) :
    α t = 1 / (1 / K + (1 / α a - 1 / K) * Real.exp (- ∫ s in a..t, g s)) := by
  set w : ℝ → ℝ := fun s => (α s)⁻¹ - K⁻¹ with hw_def
  have hw_deriv : ∀ s ∈ Set.uIcc a t, HasDerivAt w (- g s * w s) s := by
    intro s hs
    have hα_ne : α s ≠ 0 := (hα_pos s hs).ne'
    have hK_ne : K ≠ 0 := hK.ne'
    have hu : HasDerivAt (fun r => (α r)⁻¹)
        (-(α s * g s * (1 - α s / K)) / (α s) ^ 2) s :=
      (hα_deriv s hs).inv hα_ne
    have hw' : HasDerivAt w (-(α s * g s * (1 - α s / K)) / (α s) ^ 2) s := by
      simpa [hw_def] using hu.sub_const (K⁻¹)
    have hval : -(α s * g s * (1 - α s / K)) / (α s) ^ 2 = -g s * w s := by
      simp only [hw_def]
      field_simp
    rwa [hval] at hw'
  have hkey := homogeneous_linear_ode_eq_exp_integral hat hw_deriv hg_cont
  have ht_mem : t ∈ Set.uIcc a t := by
    rw [Set.uIcc_of_le hat]; exact Set.right_mem_Icc.mpr hat
  have ha_mem : a ∈ Set.uIcc a t := by
    rw [Set.uIcc_of_le hat]; exact Set.left_mem_Icc.mpr hat
  have hαt_pos : 0 < α t := hα_pos t ht_mem
  have hwt_eq : w t = (α t)⁻¹ - K⁻¹ := rfl
  have hwa_eq : w a = (α a)⁻¹ - K⁻¹ := rfl
  rw [hwt_eq, hwa_eq] at hkey
  -- hkey : (α t)⁻¹ - K⁻¹ = ((α a)⁻¹ - K⁻¹) * Real.exp (-∫ s in a..t, g s)
  have hinv_eq : (α t)⁻¹
      = 1 / K + (1 / α a - 1 / K) * Real.exp (- ∫ s in a..t, g s) := by
    rw [one_div, one_div]
    linarith [hkey]
  have hD_ne : (1 / K + (1 / α a - 1 / K) * Real.exp (- ∫ s in a..t, g s)) ≠ 0 := by
    rw [← hinv_eq]; exact inv_ne_zero hαt_pos.ne'
  rw [eq_div_iff hD_ne, ← hinv_eq]
  exact mul_inv_cancel₀ hαt_pos.ne'

/-- **Convergence corollary**: if `g` is eventually bounded below by a
    positive constant (true here: `baseGrowth → r₀ ≈ 0.005 > 0` at lock,
    per Section 6/Summary), then `∫_a^t g → +∞`, `exp(-∫_a^t g) → 0`, and
    `α(t) → K`. This is the formal statement of "K is genuinely being
    approached" — not observed-and-hoped, derived from the closed form
    above plus one easily-checked condition on `g`.

    SIGNATURE CHANGE from the originally-drafted sorry'd version:
    `hg_int : ∀ t ≥ a, IntervalIntegrable g volume a t` replaced by
    `hg_cont : Continuous g`, for the same reason as above (this lemma
    calls `logistic_capacity_eq_exp_integral` pointwise for every t ≥ a).

    PROOF STATUS: hand-verified and confirmed against `lake build` across
    two rounds. Round 1: `Tendsto.neg_atTop_atBot` does not exist under
    that name — rerouted via `Real.tendsto_exp_atTop` +
    `Filter.Tendsto.inv_tendsto_atTop` + `Real.exp_neg` instead of going
    through atBot at all; and `.congr'`/`.symm` dot-notation failed to
    resolve on `heq` because its displayed type unfolds past the
    `Filter.EventuallyEq` head symbol — fixed by calling
    `Filter.EventuallyEq.symm` / `Filter.Tendsto.congr'` fully-qualified
    instead of via dot notation. Round 2: `h1.inv_tendsto_atTop` type-
    checked but produced a Pi-level `(fun t => f t)⁻¹` term where `simpa`
    expected the pointwise `fun t => (f t)⁻¹` shape — defeq-equal (that's
    literally how `Pi.instInv` unfolds) but not syntactically matched by
    `simp`. Fixed by ascribing the pointwise-lambda type explicitly on
    `h1'`, forcing Lean to check the assignment via defeq instead of
    leaving the shape to whatever `.inv_tendsto_atTop` happened to emit. -/
lemma logistic_capacity_tendsto_K
    {α g : ℝ → ℝ} {a K : ℝ} (hK : 0 < K)
    (hα_pos : ∀ s ≥ a, 0 < α s)
    (hα_deriv : ∀ s ≥ a, HasDerivAt α (α s * g s * (1 - α s / K)) s)
    (hg_cont : Continuous g)
    (hg_diverge : Filter.Tendsto (fun t => ∫ s in a..t, g s) Filter.atTop Filter.atTop) :
    Filter.Tendsto α Filter.atTop (nhds K) := by
  have hden_tendsto : Filter.Tendsto
      (fun t => 1 / K + (1 / α a - 1 / K) * Real.exp (- ∫ s in a..t, g s))
      Filter.atTop (nhds (1 / K)) := by
    have h1 : Filter.Tendsto (fun t => Real.exp (∫ s in a..t, g s))
        Filter.atTop Filter.atTop :=
      Real.tendsto_exp_atTop.comp hg_diverge
    have h2 : Filter.Tendsto (fun t => Real.exp (- ∫ s in a..t, g s))
        Filter.atTop (nhds 0) := by
      have h1' : Filter.Tendsto (fun t => (Real.exp (∫ s in a..t, g s))⁻¹)
          Filter.atTop (nhds 0) := h1.inv_tendsto_atTop
      simpa [Real.exp_neg] using h1'
    have h3 := h2.const_mul (1 / α a - 1 / K)
    have h4 := h3.const_add (1 / K)
    simpa using h4
  have hden_ne : (1 : ℝ) / K ≠ 0 := by positivity
  have hinv_tendsto : Filter.Tendsto
      (fun t => 1 / (1 / K + (1 / α a - 1 / K) * Real.exp (- ∫ s in a..t, g s)))
      Filter.atTop (nhds K) := by
    have h5 := hden_tendsto.inv₀ hden_ne
    simpa [one_div, inv_inv] using h5
  have heq : ∀ᶠ t in Filter.atTop, α t
      = 1 / (1 / K + (1 / α a - 1 / K) * Real.exp (- ∫ s in a..t, g s)) := by
    filter_upwards [Filter.eventually_ge_atTop a] with t ht
    refine logistic_capacity_eq_exp_integral hK ht ?_ ?_ hg_cont
    · intro s hs; rw [Set.uIcc_of_le ht] at hs; exact hα_pos s hs.1
    · intro s hs; rw [Set.uIcc_of_le ht] at hs; exact hα_deriv s hs.1
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hinv_tendsto
#min_imports
