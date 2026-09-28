import ManuscriptHistoryPolicy

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- A genuine length-n history: no future slots are present. -/
abbrev FiniteHistory (Ω : Type*) (T K n : ℕ) := Ω × (Fin n → RoundRecord T K)

def restrictHistory {Ω : Type*} {T K : ℕ} (n : ℕ)
    (s : Ω × (ℕ → RoundRecord T K)) : FiniteHistory Ω T K n :=
  (s.1, fun i => s.2 i.val)

def historyPrefix {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K) : FiniteHistory Ω T K s.2.1 :=
  restrictHistory s.2.1 (s.1, s.2.2)

def appendFiniteHistory {Ω : Type*} {T K n : ℕ} (s : FiniteHistory Ω T K n)
    (r : RoundRecord T K) : FiniteHistory Ω T K (n + 1) :=
  (s.1, Fin.lastCases r s.2)

theorem restrictHistory_measurable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ} (n : ℕ) :
    Measurable (restrictHistory (Ω := Ω) (T := T) (K := K) n) := by
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.val).comp measurable_snd

theorem appendFiniteHistory_measurable {Ω : Type*} [MeasurableSpace Ω] {T K n : ℕ} :
    Measurable (fun z : FiniteHistory Ω T K n × RoundRecord T K => appendFiniteHistory z.1 z.2) := by
  apply Measurable.prodMk measurable_fst.fst
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using (measurable_snd : Measurable (fun z :
      FiniteHistory Ω T K n × RoundRecord T K => z.2))
  · simpa only [Fin.lastCases_castSucc] using (measurable_pi_apply j).comp
      (measurable_fst.snd : Measurable (fun z : FiniteHistory Ω T K n × RoundRecord T K => z.1.2))

theorem historyPrefix_append {Ω : Type*} {T K : ℕ} (s : HistoryState Ω T K) (r : RoundRecord T K) :
    historyPrefix (appendHistory s r) = appendFiniteHistory (historyPrefix s) r := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [historyPrefix, restrictHistory, appendHistory, appendFiniteHistory]
    · simp [historyPrefix, restrictHistory, appendHistory, appendFiniteHistory, ne_of_lt j.isLt]

/-- Lift a per-length measurable rule by inspecting only the actual prefix. -/
def liftFiniteRule {Ω α : Type*} {T K : ℕ}
    (f : ∀ n, FiniteHistory Ω T K n → α) (s : HistoryState Ω T K) : α :=
  f s.2.1 (historyPrefix s)

theorem liftFiniteRule_measurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {T K : ℕ} (f : ∀ n, FiniteHistory Ω T K n → α) (hf : ∀ n, Measurable (f n)) :
    Measurable (liftFiniteRule f) := by
  have hm : Measurable (fun z : (Ω × (ℕ → RoundRecord T K)) × ℕ =>
      f z.2 (restrictHistory z.2 z.1)) :=
    measurable_from_prod_countable (fun n => (hf n).comp (restrictHistory_measurable n))
  exact hm.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

/-- The rules are measurable separately on each finite-history space. -/
theorem liftFiniteRule_prefix_invariant {Ω α : Type*} {T K : ℕ}
    (f : ∀ n, FiniteHistory Ω T K n → α) (ω : Ω) (n : ℕ)
    (a b : ℕ → RoundRecord T K) (h : ∀ i : Fin n, a i.val = b i.val) :
    liftFiniteRule f (ω, n, a) = liftFiniteRule f (ω, n, b) := by
  apply congrArg (f n)
  apply Prod.ext
  · rfl
  · funext i
    exact h i

/-- Each clock value has its own finite-history domain. -/
structure FiniteHistoryPolicy (Ω : Type*) [MeasurableSpace Ω] (T K : ℕ) where
  stop : ∀ n, FiniteHistory Ω T K n → Bool
  output : ∀ n, FiniteHistory Ω T K n → Vec T
  batch : ∀ n, FiniteHistory Ω T K n → NonemptyOnlineBatch T K
  stop_measurable : ∀ n, Measurable (stop n)
  output_measurable : ∀ n, Measurable (output n)
  batch_measurable : ∀ n, Measurable (fun s => batchCode (batch n s).points)

namespace FiniteHistoryPolicy

variable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ}

def toHistory (P : FiniteHistoryPolicy Ω T K) : HistoryPolicy Ω T K where
  stop := liftFiniteRule P.stop
  output := liftFiniteRule P.output
  batch := liftFiniteRule P.batch
  stop_measurable := liftFiniteRule_measurable _ P.stop_measurable
  output_measurable := liftFiniteRule_measurable _ P.output_measurable
  batch_measurable := liftFiniteRule_measurable _ P.batch_measurable

def toOnline (P : FiniteHistoryPolicy Ω T K) : (H n : ℕ) → FiniteHistory Ω T K n → OnlinePolicy T K H
  | 0, n, s => .halt (P.output n s)
  | H + 1, n, s => if P.stop n s = true then .halt (P.output n s) else
      .ask (P.batch n s) (fun r => P.toOnline H (n + 1)
        (appendFiniteHistory s (batchCode (P.batch n s).points, batchCode r)))

theorem toHistory_toOnline (P : FiniteHistoryPolicy Ω T K) (H : ℕ) (s : HistoryState Ω T K) :
    P.toHistory.toOnline H s = P.toOnline H s.2.1 (historyPrefix s) := by
  induction H generalizing s with
  | zero => rfl
  | succ H ih =>
    simp only [HistoryPolicy.toOnline, toOnline, toHistory, liftFiniteRule]
    split
    · rfl
    · congr 1
      funext r
      simpa only [toHistory, historyPrefix_append] using
        ih (appendHistory s (batchCode (P.batch s.2.1 (historyPrefix s)).points, batchCode r))

theorem execute_eq {Seed : Type} (P : FiniteHistoryPolicy Ω T K) (O : StochasticOracle T Seed)
    (H : ℕ) (s : HistoryState Ω T K) (w : Fin H → Seed) :
    (P.toHistory.toOnline H s).execute O w = (P.toOnline H s.2.1 (historyPrefix s)).execute O w := by
  rw [P.toHistory_toOnline]

theorem stop_eq {Seed : Type} (P : FiniteHistoryPolicy Ω T K) (O : StochasticOracle T Seed)
    (H : ℕ) (s : HistoryState Ω T K) (w : Fin H → Seed) :
    (P.toHistory.toOnline H s).stop O w = (P.toOnline H s.2.1 (historyPrefix s)).stop O w := by
  rw [P.toHistory_toOnline]

def initial {Ω : Type*} {T K : ℕ} (ω : Ω) : FiniteHistory Ω T K 0 := (ω, Fin.elim0)

omit [MeasurableSpace Ω] in
theorem initial_prefix (ω : Ω) : historyPrefix (initialHistory (T := T) (K := K) ω) = initial ω := by
  apply Prod.ext
  · rfl
  · funext i
    exact Fin.elim0 i

theorem observableOnline (P : FiniteHistoryPolicy Ω T K) (O : StochasticOracle T Bool)
    (hO : MeasurableOracle O) (H : ℕ) :
    ObservableOnline O (fun ω => P.toOnline H 0 (initial ω)) := by
  have h := P.toHistory.observableOnline O hO H
  simpa only [P.toHistory_toOnline, initial_prefix] using h

theorem risk_eq (P : FiniteHistoryPolicy Ω T K) (c : StationarityCriterion) (ρ : Measure Ω)
    (O : StochasticOracle T Bool) (p : ℝ) (g : Vec T → Vec T) (H : ℕ) :
    onlineRisk c ρ O p g (fun ω => P.toHistory.toOnline H (initialHistory ω)) =
      onlineRisk c ρ O p g (fun ω => P.toOnline H 0 (initial ω)) := by
  simp only [P.toHistory_toOnline, initial_prefix]
  rfl

end FiniteHistoryPolicy

namespace ManuscriptBVProblem

theorem finite_history_product_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : FiniteHistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi
      (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

theorem finite_history_product_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : FiniteHistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad
      (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_moreau_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem finite_history_product_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : FiniteHistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi
      (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

theorem finite_history_product_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {N K : ℕ} (A : FiniteHistoryPolicy Ω P.T K) (c : StationarityCriterion)
    (hl : AEOracleLegal ρ P.oracle P.p (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad
      (fun ω => A.toOnline N 0 (FiniteHistoryPolicy.initial ω)) z
      ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.observable_product_moreau_budget_lower ρ _ c (A.observableOnline P.oracle P.oracle_measurable N) hl h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
