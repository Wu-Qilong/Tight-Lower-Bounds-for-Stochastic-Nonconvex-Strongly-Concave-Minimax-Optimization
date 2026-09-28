import ManuscriptPartialHistory

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- Outputs are supplied only at stopped histories; batches only at continuing histories. -/
structure StoppingHistoryPolicy (Ω : Type*) [MeasurableSpace Ω] (T K : ℕ) where
  domain : ∀ n, Set (FiniteHistory Ω T K n)
  domain_measurable : ∀ n, MeasurableSet (domain n)
  stop : ∀ n, domain n → Bool
  stop_measurable : ∀ n, Measurable (stop n)
  output : ∀ n, {s : domain n // stop n s = true} → Vec T
  batch : ∀ n, {s : domain n // stop n s ≠ true} → NonemptyOnlineBatch T K
  output_measurable : ∀ n, Measurable (output n)
  batch_measurable : ∀ n, Measurable (fun s => batchCode (batch n s).points)

namespace StoppingHistoryPolicy
variable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ}

theorem stopped_measurable (P : StoppingHistoryPolicy Ω T K) (n : ℕ) :
    MeasurableSet {s : P.domain n | P.stop n s = true} :=
  (P.stop_measurable n) (measurableSet_singleton true)

theorem continuing_measurable (P : StoppingHistoryPolicy Ω T K) (n : ℕ) :
    MeasurableSet {s : P.domain n | P.stop n s ≠ true} :=
  (P.stopped_measurable n).compl

/-- The auxiliary values are never used in a successfully stopped execution. -/
def toPartial (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K) :
    PartialHistoryPolicy Ω T K where
  domain := P.domain
  domain_measurable := P.domain_measurable
  stop := P.stop
  stop_measurable := P.stop_measurable
  output n := extendHistoryRule {s | P.stop n s = true} (P.output n) 0
  batch n := extendHistoryRule {s | P.stop n s ≠ true} (P.batch n) dummy
  output_measurable n := extendHistoryRule_measurable _ (P.stopped_measurable n) _
    (P.output_measurable n) _
  batch_measurable n := by
    classical
    have hm := extendHistoryRule_measurable {s : P.domain n | P.stop n s ≠ true}
      (P.continuing_measurable n) (fun s => batchCode (P.batch n s).points)
      (P.batch_measurable n) (batchCode dummy.points)
    convert hm using 1
    funext s
    by_cases h : P.stop n s = true <;> simp [extendHistoryRule, h]

theorem toPartial_output (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (n : ℕ) (s : P.domain n) (h : P.stop n s = true) :
    (P.toPartial dummy).output n s = P.output n ⟨s, h⟩ := by
  simp [toPartial, extendHistoryRule, h]

theorem toPartial_batch (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (n : ℕ) (s : P.domain n) (h : P.stop n s ≠ true) :
    (P.toPartial dummy).batch n s = P.batch n ⟨s, h⟩ := by
  simp [toPartial, extendHistoryRule, h]

/-- A finite execution is successful only if it actually stops, including at fuel zero.
Undefined histories and exhaustion at a continuing history both return `none`. -/
def run? {Seed : Type} (P : StoppingHistoryPolicy Ω T K) (O : StochasticOracle T Seed) :
    (H n : ℕ) → FiniteHistory Ω T K n → (Fin H → Seed) → Option (InteractionTrace T H K)
  | 0, n, s, _ => by
    classical
    exact if hd : s ∈ P.domain n then
      if hs : P.stop n ⟨s, hd⟩ = true then
        some (PartialHistoryPolicy.haltTrace (P.output n ⟨⟨s, hd⟩, hs⟩) 0 K)
      else none
    else none
  | H + 1, n, s, w => by
    classical
    exact if hd : s ∈ P.domain n then
      if hs : P.stop n ⟨s, hd⟩ = true then
        some (PartialHistoryPolicy.haltTrace (P.output n ⟨⟨s, hd⟩, hs⟩) (H + 1) K)
      else
        let q := (P.batch n ⟨⟨s, hd⟩, hs⟩).points
        let r := OnlinePolicy.answer O q (w 0)
        (P.run? O H (n + 1) (appendFiniteHistory s (batchCode q, batchCode r))
          (fun t => w t.succ)).map (prependOnlineTrace q r)
    else none

theorem run_zero_continuing {Seed : Type} (P : StoppingHistoryPolicy Ω T K)
    (O : StochasticOracle T Seed) (n : ℕ) (s : FiniteHistory Ω T K n)
    (hd : s ∈ P.domain n) (hs : P.stop n ⟨s, hd⟩ ≠ true) (w : Fin 0 → Seed) :
    P.run? O 0 n s w = none := by simp [run?, hd, hs]

theorem run_stopped {Seed : Type} (P : StoppingHistoryPolicy Ω T K)
    (O : StochasticOracle T Seed) (H n : ℕ) (s : FiniteHistory Ω T K n)
    (hd : s ∈ P.domain n) (hs : P.stop n ⟨s, hd⟩ = true) (w : Fin H → Seed) :
    P.run? O H n s w = some (PartialHistoryPolicy.haltTrace
      (P.output n ⟨⟨s, hd⟩, hs⟩) H K) := by
  cases H <;> simp [run?, hd, hs]

theorem run_zero_defined_iff {Seed : Type} (P : StoppingHistoryPolicy Ω T K)
    (O : StochasticOracle T Seed) (n : ℕ) (s : FiniteHistory Ω T K n) (w : Fin 0 → Seed) :
    (P.run? O 0 n s w).isSome = true ↔
      ∃ hd : s ∈ P.domain n, P.stop n ⟨s, hd⟩ = true := by
  classical
  by_cases hd : s ∈ P.domain n
  · by_cases hs : P.stop n ⟨s, hd⟩ = true <;> simp [run?, hd, hs]
  · simp [run?, hd]

theorem toPartial_run_of_run {Seed : Type} (P : StoppingHistoryPolicy Ω T K)
    (O : StochasticOracle T Seed) (dummy : NonemptyOnlineBatch T K) :
    ∀ H n (s : FiniteHistory Ω T K n) (w : Fin H → Seed) (tr : InteractionTrace T H K),
      P.run? O H n s w = some tr → (P.toPartial dummy).run? O H n s w = some tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simpa [run?, PartialHistoryPolicy.run?, toPartial, extendHistoryRule, hd, hs] using hr
      · simp [run?, hd, hs] at hr
    · simp [run?, hd] at hr
  | succ H ih =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simpa [run?, PartialHistoryPolicy.run?, toPartial, extendHistoryRule, hd, hs] using hr
      · let q := (P.batch n ⟨⟨s, hd⟩, hs⟩).points
        let r := OnlinePolicy.answer O q (w 0)
        cases ht : P.run? O H (n + 1) (appendFiniteHistory s (batchCode q, batchCode r))
            (fun t => w t.succ) with
        | none => simp [run?, hd, hs, q, r, ht] at hr
        | some tail =>
          have he := ih (n + 1) _ (fun t => w t.succ) tail ht
          have hr' : prependOnlineTrace q r tail = tr := by
            simp only [run?, dif_pos hd, dif_neg hs] at hr
            change (P.run? O H (n + 1) (appendFiniteHistory s (batchCode q, batchCode r))
              (fun t => w t.succ)).map (prependOnlineTrace q r) = some tr at hr
            rw [ht] at hr
            exact Option.some.inj hr
          rw [← hr']
          simp only [PartialHistoryPolicy.run?]
          change (if h : s ∈ P.domain n then
            if P.stop n ⟨s, h⟩ = true then _ else _
            else none) = _
          rw [dif_pos hd, if_neg hs, P.toPartial_batch dummy n ⟨s, hd⟩ hs]
          change ((P.toPartial dummy).run? O H (n + 1)
            (appendFiniteHistory s (batchCode q, batchCode r)) (fun t => w t.succ)).map
            (prependOnlineTrace q r) = _
          rw [he]
          rfl
    · simp [run?, hd] at hr

theorem extend_execute_of_run {Seed : Type} (P : StoppingHistoryPolicy Ω T K)
    (O : StochasticOracle T Seed) (dummy : NonemptyOnlineBatch T K)
    (H n : ℕ) (s : FiniteHistory Ω T K n) (w : Fin H → Seed) (tr : InteractionTrace T H K)
    (hr : P.run? O H n s w = some tr) :
    (((P.toPartial dummy).extend dummy).toOnline H n s).execute O w = tr :=
  (P.toPartial dummy).extend_execute_of_run O dummy H n s w tr
    (P.toPartial_run_of_run O dummy H n s w tr hr)

def trace (P : StoppingHistoryPolicy Ω T K) (O : StochasticOracle T Bool) (N : ℕ)
    (z : Ω × RoundWorld N) : InteractionTrace T N K :=
  (P.run? O N 0 (FiniteHistoryPolicy.initial z.1) z.2).getD
    (PartialHistoryPolicy.haltTrace 0 N K)

/-- Actual termination, standard support and call budget hold almost surely. -/
def Admissible (P : StoppingHistoryPolicy Ω T K) (ρ : Measure Ω) (O : StochasticOracle T Bool)
    (p : ℝ) (N : ℕ) : Prop :=
  ∀ᵐ z ∂ρ.prod (roundMeasure p N), ∃ tr,
    P.run? O N 0 (FiniteHistoryPolicy.initial z.1) z.2 = some tr ∧
      StandardZeroRespectingTrace tr ∧ returnedGradientCount tr ≤ N

/-- Paper-style pathwise call budget, with genuine termination on every seed world. -/
def TerminatesWithinBudget (P : StoppingHistoryPolicy Ω T K) (O : StochasticOracle T Bool)
    (N : ℕ) : Prop :=
  ∀ z : Ω × RoundWorld N, ∃ tr,
    P.run? O N 0 (FiniteHistoryPolicy.initial z.1) z.2 = some tr ∧ returnedGradientCount tr ≤ N

/-- A pathwise budget and a.s. standard support suffice for every lower-bound wrapper below. -/
theorem admissible_of_pathwise_budget (P : StoppingHistoryPolicy Ω T K)
    (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ) (N : ℕ)
    (hb : P.TerminatesWithinBudget O N)
    (hs : ∀ᵐ z ∂ρ.prod (roundMeasure p N), StandardZeroRespectingTrace (P.trace O N z)) :
    P.Admissible ρ O p N := by
  filter_upwards [hs] with z hz
  obtain ⟨tr, hr, hbudget⟩ := hb z
  refine ⟨tr, hr, ?_, hbudget⟩
  simpa [trace, hr] using hz

def loss (P : StoppingHistoryPolicy Ω T K) (c : StationarityCriterion)
    (O : StochasticOracle T Bool) (g : Vec T → Vec T) (N : ℕ) (z : Ω × RoundWorld N) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g (P.trace O N z).output‖
  | .squared => ENNReal.ofReal (‖g (P.trace O N z).output‖ ^ 2)

def risk (P : StoppingHistoryPolicy Ω T K) (c : StationarityCriterion) (ρ : Measure Ω)
    (O : StochasticOracle T Bool) (p : ℝ) (g : Vec T → Vec T) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ z, P.loss c O g N z ∂ρ.prod (roundMeasure p N)

theorem toPartial_admissible (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ) (N : ℕ) (ha : P.Admissible ρ O p N) :
    (P.toPartial dummy).Admissible ρ O p N := by
  filter_upwards [ha] with z hz
  obtain ⟨tr, hr, hs, hb⟩ := hz
  exact ⟨tr, P.toPartial_run_of_run O dummy N 0 _ _ tr hr, hs, hb⟩

theorem trace_eq_toPartial_ae (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ) (N : ℕ) (ha : P.Admissible ρ O p N) :
    P.trace O N =ᵐ[ρ.prod (roundMeasure p N)] (P.toPartial dummy).trace O N := by
  filter_upwards [ha] with z hz
  obtain ⟨tr, hr, hs, hb⟩ := hz
  simp [trace, PartialHistoryPolicy.trace, hr, P.toPartial_run_of_run O dummy N 0 _ _ tr hr]

theorem loss_eq_toPartial_ae (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (c : StationarityCriterion) (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (N : ℕ) (ha : P.Admissible ρ O p N) :
    P.loss c O g N =ᵐ[ρ.prod (roundMeasure p N)] (P.toPartial dummy).loss c O g N := by
  filter_upwards [P.trace_eq_toPartial_ae dummy ρ O p N ha] with z hz
  cases c <;> simp only [loss, PartialHistoryPolicy.loss, hz]

theorem risk_eq_toPartial (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (c : StationarityCriterion) (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (N : ℕ) (ha : P.Admissible ρ O p N) :
    P.risk c ρ O p g N = (P.toPartial dummy).risk c ρ O p g N :=
  lintegral_congr_ae (P.loss_eq_toPartial_ae dummy c ρ O p g N ha)

theorem loss_aemeasurable (P : StoppingHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (c : StationarityCriterion) (ρ : Measure Ω) (O : StochasticOracle T Bool) (hO : MeasurableOracle O)
    (p : ℝ) (g : Vec T → Vec T) (hg : Measurable g) (N : ℕ) (ha : P.Admissible ρ O p N) :
    AEMeasurable (P.loss c O g N) (ρ.prod (roundMeasure p N)) :=
  ((P.toPartial dummy).loss_aemeasurable dummy c ρ O hO p g hg N
    (P.toPartial_admissible dummy ρ O p N ha)).congr
    (P.loss_eq_toPartial_ae dummy c ρ O p g N ha).symm

end StoppingHistoryPolicy

namespace ManuscriptBVProblem
theorem stopping_history_product_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : StoppingHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.population.gradPhi N ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.partial_history_product_budget_lower ρ hK (A.toPartial dummy) c
    (A.toPartial_admissible dummy ρ P.oracle P.p N ha)
  rwa [A.risk_eq_toPartial dummy c ρ P.oracle P.p P.population.gradPhi N ha] at h

theorem stopping_history_product_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : StoppingHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.moreau.envelopeGrad N ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.partial_history_product_moreau_budget_lower ρ hK (A.toPartial dummy) c
    (A.toPartial_admissible dummy ρ P.oracle P.p N ha)
  rwa [A.risk_eq_toPartial dummy c ρ P.oracle P.p P.moreau.envelopeGrad N ha] at h
end ManuscriptBVProblem

namespace ManuscriptASProblem
theorem stopping_history_product_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : StoppingHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.population.gradPhi N ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.partial_history_product_budget_lower ρ hK (A.toPartial dummy) c
    (A.toPartial_admissible dummy ρ P.oracle P.p N ha)
  rwa [A.risk_eq_toPartial dummy c ρ P.oracle P.p P.population.gradPhi N ha] at h

theorem stopping_history_product_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : StoppingHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.moreau.envelopeGrad N ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.partial_history_product_moreau_budget_lower ρ hK (A.toPartial dummy) c
    (A.toPartial_admissible dummy ρ P.oracle P.p N ha)
  rwa [A.risk_eq_toPartial dummy c ρ P.oracle P.p P.moreau.envelopeGrad N ha] at h
end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
