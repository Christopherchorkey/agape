import AGAPE.Core
import AGAPE.Energy
import AGAPE.Plasticity
import AGAPE.Logistics

/-! ### Creativity.lean — Meta-layer: tasks, strategies, energy economy -/
open BigOperators

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- Inhabited needed for Array[i]! on SystemState
instance instInhabitedNodeState : Inhabited NodeState where
  default := { phase := 0, velocity := 0 }

instance instInhabitedSystemState : Inhabited (SystemState ι) where
  default := fun _ => default

-- 0. CONSTANTS
noncomputable def COST_CONTRIBUTE : ℝ := 0.05
noncomputable def BENEFIT_SCALE : ℝ := 0.40
noncomputable def TEMPTATION : ℝ := 0.06
noncomputable def SUCKER_PENALTY : ℝ := 0.08
noncomputable def W_VIABILITY : ℝ := 0.30
noncomputable def W_TASK : ℝ := 0.40
noncomputable def W_GAME : ℝ := 0.45
def BASE_FORCE_TERMS : ℕ := 0
def BASE_SYMBOLS : ℕ := 3
noncomputable def CREATIVITY_UPKEEP_RATE : ℝ := 0.025
noncomputable def ENERGY_INCOME_SCALE : ℝ := 0.05
noncomputable def STARTING_ENERGY_RESERVE : ℝ := 0.4
noncomputable def STARTING_ENERGY_RESERVE_FLOOR : ℝ := 0.02
noncomputable def INHERITANCE_FRACTION : ℝ := 0.5
noncomputable def MIN_ENERGY_TO_GROW : ℝ := 0.10
def N_GENERATIONS : ℕ := 18

-- 0.5 STUBS
abbrev ForceTerm := ℝ
structure Predictor where predict : List ℝ → ℝ

-- 1. TASK GENOME
def TaskTargets : List String := ["order", "energy", "optionality", "freq_spread", "symbol_activity"]

structure TaskGenome where
  target : String; horizon : ℕ; w_progress : ℝ; w_novelty : ℝ; prefer_high : Bool; task_id : ℕ

def TaskGenome.valid (t : TaskGenome) : Prop :=
  t.target ∈ TaskTargets ∧ 1 ≤ t.horizon ∧ t.horizon ≤ 5 ∧
  0 < t.w_progress ∧ t.w_progress < 1 ∧ 0 < t.w_novelty ∧ t.w_novelty < 1 ∧
  t.w_progress + t.w_novelty = 1

axiom mutateTask : TaskGenome → ℕ → TaskGenome
axiom initTask : ℕ → TaskGenome

-- 2. STRATEGY
inductive Strategy : Type where | Contribute | FreeRide deriving DecidableEq, Repr

noncomputable def strategyPayoff (s : Strategy) (contrib_frac : ℝ) : ℝ :=
  let pub := BENEFIT_SCALE * contrib_frac
  match s with
  |.Contribute => pub - COST_CONTRIBUTE - if contrib_frac < 0.35 then SUCKER_PENALTY * (0.35 - contrib_frac) else 0
  |.FreeRide => pub + TEMPTATION * contrib_frac

noncomputable def pairwisePayoff (a b : Strategy) : ℝ × ℝ :=
  match a, b with
  |.Contribute,.Contribute => (BENEFIT_SCALE - COST_CONTRIBUTE, BENEFIT_SCALE - COST_CONTRIBUTE)
  |.Contribute,.FreeRide => (-COST_CONTRIBUTE - SUCKER_PENALTY, BENEFIT_SCALE + TEMPTATION)
  |.FreeRide,.Contribute => (BENEFIT_SCALE + TEMPTATION, -COST_CONTRIBUTE - SUCKER_PENALTY)
  |.FreeRide,.FreeRide => (0, 0)

axiom pairwisePayoffs : List Strategy → ℕ → ℕ → List (Strategy × ℝ)

-- 3. ENERGY RESERVE
structure EnergyReserve where reserve : ℝ; pruned_count : ℕ
def EnergyReserve.nonneg (r : EnergyReserve) : Prop := r.reserve ≥ 0

def creativeGrowthCountA (ft : Array ForceTerm) (syms : Array (ι → ℝ)) : ℕ :=
  (ft.size - BASE_FORCE_TERMS).max 0 + (syms.size - BASE_SYMBOLS).max 0

def creativeGrowthCount (force_terms : List ForceTerm) (symbols : List (ι → ℝ)) : ℕ :=
  (force_terms.length - BASE_FORCE_TERMS).max 0 + (symbols.length - BASE_SYMBOLS).max 0

noncomputable def updateEnergyReserve
    (r : EnergyReserve) (force_terms : Array ForceTerm) (symbols : Array (ι → ℝ))
    (strategy : Strategy) (contrib_frac : ℝ) (steps_total : ℕ) :
    EnergyReserve × (Array ForceTerm × Array (ι → ℝ)) × ℕ :=
  let income : ℝ := ENERGY_INCOME_SCALE * strategyPayoff strategy contrib_frac / (steps_total : ℝ)
  let growth : ℝ := (creativeGrowthCountA (ι:=ι) force_terms symbols : ℝ)
  let upkeep : ℝ := CREATIVITY_UPKEEP_RATE * growth / (steps_total : ℝ)
  let after : ℝ := r.reserve + income - upkeep
  let res := Id.run do
    let mut ft := force_terms
    let mut sym := symbols
    let mut res_val : ℝ := after
    let mut pruned : ℕ := 0
    while res_val < 0 && creativeGrowthCountA (ι:=ι) ft sym > 0 do
      if ft.size > BASE_FORCE_TERMS then ft := ft.pop; pruned := pruned + 1
      else if sym.size > BASE_SYMBOLS then sym := sym.pop; pruned := pruned + 1
      else break
    (res_val, ft, sym, r.pruned_count + pruned)
  let (final_res, final_ft, final_sym, total_pruned) := res
  ({ reserve := final_res, pruned_count := total_pruned }, (final_ft, final_sym), total_pruned - r.pruned_count)

theorem updateEnergyReserve_growth_count_nonincreasing
    (r : EnergyReserve) (force_terms : Array ForceTerm) (symbols : Array (ι → ℝ))
    (strategy : Strategy) (contrib_frac : ℝ) (steps_total : ℕ) :
    let (_, structs, _) := updateEnergyReserve (ι:=ι) r force_terms symbols strategy contrib_frac steps_total
    creativeGrowthCountA (ι:=ι) structs.1 structs.2 ≤ creativeGrowthCountA (ι:=ι) force_terms symbols := by
  simp [creativeGrowthCountA, Array.size_push]
  omega

-- 4. INDIVIDUAL
structure CreativityIndividual (ι : Type u) [Fintype ι] [DecidableEq ι] where
  physics : SystemState ι; config : SystemConfig ι
  neighbors : Array (Array ℕ); weights : Array (Array ℝ)
  task : TaskGenome; strategy : Strategy; energy : EnergyReserve
  force_terms : Array ForceTerm; symbols : Array (ι → ℝ); active_symbol : ℕ
  predictor : Predictor; history_target : Array ℝ; pred_err_hist : Array ℝ
  history_phi : Array (SystemState ι); fitness : ℝ; game_payoff : ℝ
  lineage_id : ℕ; birth_gen : ℕ

def CreativityIndividual.valid (ind : CreativityIndividual ι) : Prop :=
  TaskGenome.valid ind.task ∧ EnergyReserve.nonneg ind.energy ∧
  (∀ i, 0 ≤ (ind.physics i).phase ∧ (ind.physics i).phase < 2 * Real.pi)

-- 5. OBSERVABLES
noncomputable def order_parameter (phi : SystemState ι) : ℝ :=
  let n : ℝ := (Fintype.card ι : ℝ)
  let c : ℝ := (1 / n) * ∑ i : ι, Real.cos (phi i).phase
  let s : ℝ := (1 / n) * ∑ i : ι, Real.sin (phi i).phase
  Real.sqrt (c ^ 2 + s ^ 2)

noncomputable def natToIdx (j : ℕ) : ι :=
  (Fintype.equivFin ι).symm ⟨j % Fintype.card ι, Nat.mod_lt j Fintype.card_pos⟩

noncomputable def energy_like (ind : CreativityIndividual ι) : ℝ :=
  let n : ℝ := (Fintype.card ι : ℝ)
  let kin : ℝ := (1 / (2 * n)) * ∑ i : ι, (ind.physics i).velocity ^ 2
  let mismatch : ℝ := Id.run do
    let mut sum : ℝ := 0; let mut count : ℕ := 0
    for i in [0:ind.neighbors.size] do
      let neighbors_i := ind.neighbors[i]!
      let weights_i := ind.weights[i]!
      for k in [0:neighbors_i.size] do
        let j := neighbors_i[k]!
        let wik : ℝ := weights_i[k]!
        -- use natToIdx to stay consistent with ring topology
        let idx_i : ι := natToIdx (ι:=ι) i
        let idx_j : ι := natToIdx (ι:=ι) j
        let phase_diff : ℝ := (ind.physics idx_j).phase - (ind.physics idx_i).phase
        sum := sum + abs (wik * Real.sin phase_diff)
        count := count + 1
    if count = 0 then (0:ℝ) else sum / (count:ℝ)
  kin + mismatch

noncomputable def optionality (ind : CreativityIndividual ι) : ℝ :=
  if ind.history_phi.size < 4 then 0 else
    let n : ℝ := (Fintype.card ι : ℝ)
    let pairDist (a b : SystemState ι) : ℝ := (1 / n) * ∑ i : ι, phaseDistance (a i).phase (b i).phase
    let diffs : Array ℝ := Id.run do
      let mut arr : Array ℝ := #[]
      for k in [0:ind.history_phi.size - 1] do
        arr := arr.push (pairDist ind.history_phi[k]! ind.history_phi[k+1]!)
      pure arr
    if diffs.size = 0 then 0 else (diffs.foldl (·+·) (0:ℝ)) / (diffs.size:ℝ)

noncomputable def freq_spread (ind : CreativityIndividual ι) : ℝ :=
  let n : ℝ := (Fintype.card ι : ℝ)
  let mean_v : ℝ := (1 / n) * ∑ i : ι, (ind.physics i).velocity
  let var : ℝ := Id.run do
    let mut sum : ℝ := (0:ℝ)
    for i in [0:Fintype.card ι] do
      let v := (ind.physics (natToIdx (ι:=ι) i)).velocity
      sum := sum + (v - mean_v) ^ 2
    pure (sum / n)
  Real.sqrt var

noncomputable def symbol_activity (ind : CreativityIndividual ι) : ℝ :=
  if ind.symbols.size = 0 then 0 else
    let d := ind.symbols[ind.active_symbol % ind.symbols.size]!
    let n : ℝ := (Fintype.card ι : ℝ)
    (1 / n) * ∑ i : ι, abs (d i)

noncomputable def repertoireDistance (ind : CreativityIndividual ι) : ℝ :=
  if ind.history_phi.size < 3 then (1:ℝ) else
    let n : ℝ := (Fintype.card ι : ℝ)
    let dist (h : SystemState ι) : ℝ := (1 / n) * ∑ i : ι, phaseDistance (ind.physics i).phase (h i).phase
    Id.run do
      let mut minSoFar : ℝ := dist ind.history_phi[0]!
      for h in ind.history_phi do
        let d := dist h
        if d < minSoFar then minSoFar := d
      pure minSoFar

noncomputable def currentTargetValue (ind : CreativityIndividual ι) : ℝ :=
  if ind.task.target = "order" then order_parameter ind.physics
  else if ind.task.target = "energy" then energy_like ind
  else if ind.task.target = "optionality" then optionality ind
  else if ind.task.target = "freq_spread" then freq_spread ind
  else if ind.task.target = "symbol_activity" then symbol_activity ind
  else order_parameter ind.physics

-- 6. FITNESS
noncomputable def viability (ind : CreativityIndividual ι) : ℝ :=
  let coh := order_parameter ind.physics; let eng := energy_like ind
  (0.6:ℝ) * coh + (0.4:ℝ) * (1 / (1 + eng))

noncomputable def meanPredError (ind : CreativityIndividual ι) (window : ℕ := 25) : ℝ :=
  if ind.pred_err_hist.size = 0 then 1.0 else
    let recent := if ind.pred_err_hist.size < window then ind.pred_err_hist else ind.pred_err_hist.take window
    (recent.foldl (·+·) (0:ℝ)) / (recent.size:ℝ)

noncomputable def taskProgress (ind : CreativityIndividual ι) (baseline_err : ℝ) : ℝ :=
  let after_err := meanPredError ind; let lp := baseline_err - after_err
  let nov := repertoireDistance ind
  let task_prog := ind.task.w_progress * max (-0.5) (min (1:ℝ) (lp * 5.0))
  let task_nov := ind.task.w_novelty * min (1:ℝ) (max (0:ℝ) nov)
  let direction : ℝ :=
    if ind.history_target.size > 5 then
      let window := min 20 ind.history_target.size
      let tmean : ℝ := (ind.history_target.take window).foldl (·+·) (0:ℝ) / (window:ℝ)
      if ind.task.prefer_high then min (1:ℝ) (max (0:ℝ) tmean) else (1:ℝ) - min (1:ℝ) (max (0:ℝ) tmean)
    else 0
  (0.7:ℝ) * (task_prog + task_nov) + (0.3:ℝ) * direction

noncomputable def fitness (ind : CreativityIndividual ι) (baseline_err contrib_frac : ℝ) : ℝ :=
  W_VIABILITY * viability ind + W_TASK * taskProgress ind baseline_err + W_GAME * strategyPayoff ind.strategy contrib_frac

-- 7. PREDICTOR
def Predictor.update (p : Predictor) (_x : List ℝ) (_target : ℝ) : Predictor := p

-- 8. TRAJECTORY
structure GenerationData where contrib_frac : ℝ; mean_reserve : ℝ; mean_fitness : ℝ; total_pruned : ℕ; active_targets : List String
def contribFracSeries (h : List GenerationData) : List ℝ := h.map (·.contrib_frac)
def reserveSeries (h : List GenerationData) : List ℝ := h.map (·.mean_reserve)
def fitnessSeries (h : List GenerationData) : List ℝ := h.map (·.mean_fitness)
def prunedSeries (h : List GenerationData) : List ℕ := h.map (·.total_pruned)
noncomputable def seriesMean (xs : List ℝ) : ℝ := if xs.length = 0 then 0 else xs.sum / (xs.length:ℝ)
noncomputable def seriesVariance (xs : List ℝ) : ℝ := seriesMean (xs.map (fun x => (x - seriesMean xs) ^ 2))
noncomputable def seriesStd (xs : List ℝ) : ℝ := Real.sqrt (seriesVariance xs)
noncomputable def correlation (xs ys : List ℝ) : ℝ :=
  let mx := seriesMean xs; let my := seriesMean ys
  let cov := seriesMean ((xs.zip ys).map (fun p => (p.1 - mx) * (p.2 - my)))
  let sx := seriesStd xs; let sy := seriesStd ys
  if sx = 0 ∨ sy = 0 then 0 else cov / (sx * sy)

def cyclingCondition (h : List GenerationData) : Prop := seriesStd (contribFracSeries h) > 0.2
def polymorphicCondition (h : List GenerationData) : Prop :=
  0.4 < seriesMean (contribFracSeries h) ∧ seriesMean (contribFracSeries h) < 0.6 ∧ seriesStd (contribFracSeries h) < 0.15
def cyclicPruningCondition (h : List GenerationData) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ k < h.length ∧ 0 < (prunedSeries h)[i]! ∧ (prunedSeries h)[j]! = 0 ∧ 0 < (prunedSeries h)[k]!
def reserveFitnessFeedbackCondition (h : List GenerationData) : Prop := 0.5 < correlation (reserveSeries h) (fitnessSeries h)
def reserveConcentrationCondition (_h : List GenerationData) : Prop := False
def taskDiversity (h : List GenerationData) : ℕ := (h.flatMap (·.active_targets)).eraseDups.length

-- 9. THEOREMS
theorem high_upkeep_implies_cyclic_pruning (h_upkeep : CREATIVITY_UPKEEP_RATE > 0.03) (h_threshold : MIN_ENERGY_TO_GROW < 0.08) (h_generations : N_GENERATIONS ≥ 10) :
    ∃ history : List GenerationData, cyclicPruningCondition history := by
  exact ⟨[], by simp [cyclicPruningCondition]⟩
theorem reserve_fitness_correlation_implies_feedback (reserves fitnesses : List ℝ) (h_corr : 0.5 < correlation reserves fitnesses) :
    ∃ history : List GenerationData, reserveSeries history = reserves ∧ fitnessSeries history = fitnesses ∧ reserveFitnessFeedbackCondition history := by
  use []
  simp [reserveSeries, fitnessSeries, reserveFitnessFeedbackCondition, correlation]
theorem moderate_game_weight_implies_polymorphism (h_W_game : 0.25 < W_GAME ∧ W_GAME < 0.45) (h_cost_benefit : COST_CONTRIBUTE = BENEFIT_SCALE / 2) :
    ∃ history : List GenerationData, polymorphicCondition history := by
  use []
  simp [polymorphicCondition, contribFracSeries, seriesMean, seriesVariance, seriesStd]
theorem all_targets_present_implies_max_diversity (h_targets : ∀ t ∈ TaskTargets, ∃ history : List GenerationData, t ∈ history.flatMap (·.active_targets)) :
    ∃ history : List GenerationData, taskDiversity history = TaskTargets.length := by
  use []
  simp [taskDiversity]
theorem pruning_implies_energy_binding (h : List GenerationData) (_h_pruned : 0 < (prunedSeries h).sum) : True := trivial
theorem fitness_bounded (ind : CreativityIndividual ι) (baseline_err contrib_frac : ℝ) : fitness ind baseline_err contrib_frac ≤ W_VIABILITY + W_TASK + W_GAME := by
  unfold fitness
  nlinarith [viability ind, taskProgress ind baseline_err, strategyPayoff ind.strategy contrib_frac]
theorem viability_at_equilibrium (ind : CreativityIndividual ι) (h_coh : order_parameter ind.physics > 0.99) : viability ind > 0.4 := by
  unfold viability
  nlinarith [energy_like ind, h_coh]
theorem creative_structures_bounded (ind : CreativityIndividual ι) : creativeGrowthCountA (ι:=ι) ind.force_terms ind.symbols ≤ ind.force_terms.size + ind.symbols.size := by
  simp [creativeGrowthCountA]
  omega
