import ManuscriptFiniteHistory

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

def extendHistoryRule {X Y : Type*} (D : Set X) (f : D → Y) (fallback : Y) (x : X) : Y := by
  classical
  exact if h : x ∈ D then f ⟨x, h⟩ else fallback

theorem extendHistoryRule_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Set X) (hD : MeasurableSet D) (f : D → Y) (hf : Measurable f) (fallback : Y) :
    Measurable (extendHistoryRule D f fallback) := by
  classical
  exact hf.dite measurable_const hD

/-- Used only as an unqueried default on histories where the total extension halts. -/
def zeroDefaultBatch (T K : ℕ) (hK : 1 ≤ K) : NonemptyOnlineBatch T K where
  points := fun _ => some (0, 0)
  size_pos := by simpa [onlineBatchSize] using hK
  size_le := by simp [onlineBatchSize]

/-- Rules defined only on a measurable admissible-history subset at each length. -/
structure PartialHistoryPolicy (Ω : Type*) [MeasurableSpace Ω] (T K : ℕ) where
  domain : ∀ n, Set (FiniteHistory Ω T K n)
  domain_measurable : ∀ n, MeasurableSet (domain n)
  stop : ∀ n, domain n → Bool
  output : ∀ n, domain n → Vec T
  batch : ∀ n, domain n → NonemptyOnlineBatch T K
  stop_measurable : ∀ n, Measurable (stop n)
  output_measurable : ∀ n, Measurable (output n)
  batch_measurable : ∀ n, Measurable (fun s => batchCode (batch n s).points)

namespace PartialHistoryPolicy

variable {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ}

def extend (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K) :
    FiniteHistoryPolicy Ω T K where
  stop n := extendHistoryRule (P.domain n) (P.stop n) true
  output n := extendHistoryRule (P.domain n) (P.output n) 0
  batch n := extendHistoryRule (P.domain n) (P.batch n) dummy
  stop_measurable n := extendHistoryRule_measurable _ (P.domain_measurable n) _ (P.stop_measurable n) _
  output_measurable n := extendHistoryRule_measurable _ (P.domain_measurable n) _ (P.output_measurable n) _
  batch_measurable n := by
    classical
    have hm := extendHistoryRule_measurable (P.domain n) (P.domain_measurable n)
      (fun s => batchCode (P.batch n s).points) (P.batch_measurable n) (batchCode dummy.points)
    convert hm using 1
    funext s
    by_cases h : s ∈ P.domain n <;> simp [extendHistoryRule, h]

theorem extend_stop (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (n : ℕ) (s : FiniteHistory Ω T K n) (h : s ∈ P.domain n) :
    (P.extend dummy).stop n s = P.stop n ⟨s, h⟩ := by simp [extend, extendHistoryRule, h]

theorem extend_output (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (n : ℕ) (s : FiniteHistory Ω T K n) (h : s ∈ P.domain n) :
    (P.extend dummy).output n s = P.output n ⟨s, h⟩ := by simp [extend, extendHistoryRule, h]

theorem extend_batch (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (n : ℕ) (s : FiniteHistory Ω T K n) (h : s ∈ P.domain n) :
    (P.extend dummy).batch n s = P.batch n ⟨s, h⟩ := by simp [extend, extendHistoryRule, h]

def haltTrace (x : Vec T) (H K : ℕ) : InteractionTrace T H K :=
  ⟨fun _ _ => none, fun _ _ => none, x⟩

/-- Partial interpreter: `none` means a reached history lies outside the domain.
No closure under unrealizable response histories is assumed. -/
def run? {Seed : Type} (P : PartialHistoryPolicy Ω T K) (O : StochasticOracle T Seed) :
    (H n : ℕ) → FiniteHistory Ω T K n → (Fin H → Seed) → Option (InteractionTrace T H K)
  | 0, n, s, _ => by
    classical
    exact if h : s ∈ P.domain n then some (haltTrace (P.output n ⟨s, h⟩) 0 K) else none
  | H + 1, n, s, w => by
    classical
    exact if h : s ∈ P.domain n then
      if P.stop n ⟨s, h⟩ = true then some (haltTrace (P.output n ⟨s, h⟩) (H + 1) K)
      else
        let q := (P.batch n ⟨s, h⟩).points
        let r := OnlinePolicy.answer O q (w 0)
        (P.run? O H (n + 1) (appendFiniteHistory s (batchCode q, batchCode r))
          (fun t => w t.succ)).map (prependOnlineTrace q r)
    else none

theorem extend_execute_of_run {Seed : Type} (P : PartialHistoryPolicy Ω T K)
    (O : StochasticOracle T Seed) (dummy : NonemptyOnlineBatch T K) :
    ∀ H n (s : FiniteHistory Ω T K n) (w : Fin H → Seed) (tr : InteractionTrace T H K),
      P.run? O H n s w = some tr → ((P.extend dummy).toOnline H n s).execute O w = tr := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · simp only [run?, dif_pos hd, Option.some.injEq] at hr
      rw [← hr]
      simp [FiniteHistoryPolicy.toOnline, P.extend_output dummy n s hd, OnlinePolicy.execute, haltTrace]
    · simp [run?, hd] at hr
  | succ H ih =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp only [run?, dif_pos hd, if_pos hs, Option.some.injEq] at hr
        rw [← hr]
        simp [FiniteHistoryPolicy.toOnline, P.extend_stop dummy n s hd,
          P.extend_output dummy n s hd, hs, OnlinePolicy.execute, haltTrace]
      · let q := (P.batch n ⟨s, hd⟩).points
        let r := OnlinePolicy.answer O q (w 0)
        cases ht : P.run? O H (n + 1) (appendFiniteHistory s (batchCode q, batchCode r))
            (fun t => w t.succ) with
        | none => simp [run?, hd, hs, q, r, ht] at hr
        | some tail =>
          have he := ih (n + 1) _ (fun t => w t.succ) tail ht
          have hr' : prependOnlineTrace q r tail = tr := by
            simp only [run?, dif_pos hd, if_neg hs] at hr
            change (P.run? O H (n + 1) (appendFiniteHistory s (batchCode q, batchCode r))
              (fun t => w t.succ)).map (prependOnlineTrace q r) = some tr at hr
            rw [ht] at hr
            exact Option.some.inj hr
          rw [← hr']
          simp only [FiniteHistoryPolicy.toOnline, P.extend_stop dummy n s hd, if_neg hs,
            P.extend_batch dummy n s hd, OnlinePolicy.execute]
          change prependOnlineTrace q r _ = prependOnlineTrace q r tail
          rw [he]
    · simp [run?, hd] at hr

theorem extend_dummy_independent (P : PartialHistoryPolicy Ω T K)
    (a b : NonemptyOnlineBatch T K) : ∀ H n (s : FiniteHistory Ω T K n),
      (P.extend a).toOnline H n s = (P.extend b).toOnline H n s := by
  intro H
  induction H with
  | zero => intro n s; rfl
  | succ H ih =>
    intro n s
    by_cases hd : s ∈ P.domain n
    · simp only [FiniteHistoryPolicy.toOnline, P.extend_stop a n s hd, P.extend_stop b n s hd,
        P.extend_output a n s hd, P.extend_output b n s hd,
        P.extend_batch a n s hd, P.extend_batch b n s hd]
      split
      · rfl
      · congr 1
        funext r
        exact ih _ _
    · simp [FiniteHistoryPolicy.toOnline, extend, extendHistoryRule, hd]

theorem extend_halts_outside (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (H n : ℕ) (s : FiniteHistory Ω T K n) (h : s ∉ P.domain n) :
    (P.extend dummy).toOnline H n s = .halt 0 := by
  cases H <;> simp [FiniteHistoryPolicy.toOnline, extend, extendHistoryRule, h]

def trace (P : PartialHistoryPolicy Ω T K) (O : StochasticOracle T Bool) (N : ℕ)
    (z : Ω × RoundWorld N) : InteractionTrace T N K :=
  (P.run? O N 0 (FiniteHistoryPolicy.initial z.1) z.2).getD (haltTrace 0 N K)

/-- Actual runs must be defined, standard-support legal, and within budget a.s. -/
def Admissible (P : PartialHistoryPolicy Ω T K) (ρ : Measure Ω) (O : StochasticOracle T Bool)
    (p : ℝ) (N : ℕ) : Prop :=
  ∀ᵐ z ∂ρ.prod (roundMeasure p N), ∃ tr,
    P.run? O N 0 (FiniteHistoryPolicy.initial z.1) z.2 = some tr ∧
      StandardZeroRespectingTrace tr ∧ returnedGradientCount tr ≤ N

def loss (P : PartialHistoryPolicy Ω T K) (c : StationarityCriterion)
    (O : StochasticOracle T Bool) (g : Vec T → Vec T) (N : ℕ) (z : Ω × RoundWorld N) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g (P.trace O N z).output‖
  | .squared => ENNReal.ofReal (‖g (P.trace O N z).output‖ ^ 2)

def risk (P : PartialHistoryPolicy Ω T K) (c : StationarityCriterion) (ρ : Measure Ω)
    (O : StochasticOracle T Bool) (p : ℝ) (g : Vec T → Vec T) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ z, P.loss c O g N z ∂ρ.prod (roundMeasure p N)

theorem trace_eq_extend_ae (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ) (N : ℕ) (ha : P.Admissible ρ O p N) :
    P.trace O N =ᵐ[ρ.prod (roundMeasure p N)]
      (fun z => ((P.extend dummy).toOnline N 0 (FiniteHistoryPolicy.initial z.1)).execute O z.2) := by
  filter_upwards [ha] with z hz
  obtain ⟨tr, hr, hs, hb⟩ := hz
  simp only [trace, hr, Option.getD_some]
  exact (P.extend_execute_of_run O dummy N 0 _ _ tr hr).symm

theorem loss_eq_extend_ae (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (c : StationarityCriterion) (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (N : ℕ) (ha : P.Admissible ρ O p N) :
    P.loss c O g N =ᵐ[ρ.prod (roundMeasure p N)]
      onlineLoss c O g (fun ω => (P.extend dummy).toOnline N 0 (FiniteHistoryPolicy.initial ω)) := by
  filter_upwards [P.trace_eq_extend_ae dummy ρ O p N ha] with z hz
  cases c <;> simp only [loss, onlineLoss, hz]

theorem risk_eq_extend (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (c : StationarityCriterion) (ρ : Measure Ω) (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (N : ℕ) (ha : P.Admissible ρ O p N) :
    P.risk c ρ O p g N = ∫⁻ z, onlineLoss c O g
      (fun ω => (P.extend dummy).toOnline N 0 (FiniteHistoryPolicy.initial ω)) z ∂ρ.prod (roundMeasure p N) :=
  lintegral_congr_ae (P.loss_eq_extend_ae dummy c ρ O p g N ha)

theorem extend_legal (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (ρ : Measure Ω) (O : StochasticOracle T Bool) (hO : MeasurableOracle O)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (ha : P.Admissible ρ O p N) :
    AEOracleLegal ρ O p (fun ω => (P.extend dummy).toOnline N 0 (FiniteHistoryPolicy.initial ω)) := by
  have ho := (P.extend dummy).observableOnline O hO N
  have hm := (ObservableMeasurable.joint _ ho).legal_event N
  apply (aeOracleLegal_iff_product ρ O p hp0 hp1 _ hm).mpr
  filter_upwards [ha] with z hz
  obtain ⟨tr, hr, hs, hb⟩ := hz
  rw [P.extend_execute_of_run O dummy N 0 _ _ tr hr]
  exact ⟨hs, hb⟩

theorem loss_aemeasurable (P : PartialHistoryPolicy Ω T K) (dummy : NonemptyOnlineBatch T K)
    (c : StationarityCriterion) (ρ : Measure Ω) (O : StochasticOracle T Bool) (hO : MeasurableOracle O)
    (p : ℝ) (g : Vec T → Vec T) (hg : Measurable g) (N : ℕ) (ha : P.Admissible ρ O p N) :
    AEMeasurable (P.loss c O g N) (ρ.prod (roundMeasure p N)) :=
  ((P.extend dummy).observableOnline O hO N).loss_measurable c O g _ hg |>.aemeasurable.congr
    (P.loss_eq_extend_ae dummy c ρ O p g N ha).symm

end PartialHistoryPolicy
namespace ManuscriptBVProblem

theorem partial_history_product_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : PartialHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.population.gradPhi N ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.finite_history_product_budget_lower ρ (A.extend dummy) c
    (A.extend_legal dummy ρ P.oracle P.oracle_measurable P.p (le_of_lt P.p_pos) P.p_le_one N ha)
  rwa [A.risk_eq_extend dummy c ρ P.oracle P.p P.population.gradPhi N ha] at h

theorem partial_history_product_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : PartialHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.moreau.envelopeGrad N ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.finite_history_product_moreau_budget_lower ρ (A.extend dummy) c
    (A.extend_legal dummy ρ P.oracle P.oracle_measurable P.p (le_of_lt P.p_pos) P.p_le_one N ha)
  rwa [A.risk_eq_extend dummy c ρ P.oracle P.p P.moreau.envelopeGrad N ha] at h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem partial_history_product_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : PartialHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.population.gradPhi N ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.finite_history_product_budget_lower ρ (A.extend dummy) c
    (A.extend_legal dummy ρ P.oracle P.oracle_measurable P.p (le_of_lt P.p_pos) P.p_le_one N ha)
  rwa [A.risk_eq_extend dummy c ρ P.oracle P.p P.population.gradPhi N ha] at h

theorem partial_history_product_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type*}
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (hK : 1 ≤ K)
    (A : PartialHistoryPolicy Ω P.T K) (c : StationarityCriterion) (ha : A.Admissible ρ P.oracle P.p N)
    (h : A.risk c ρ P.oracle P.p P.moreau.envelopeGrad N ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  let dummy := zeroDefaultBatch P.T K hK
  apply P.finite_history_product_moreau_budget_lower ρ (A.extend dummy) c
    (A.extend_legal dummy ρ P.oracle P.oracle_measurable P.p (le_of_lt P.p_pos) P.p_le_one N ha)
  rwa [A.risk_eq_extend dummy c ρ P.oracle P.p P.moreau.envelopeGrad N ha] at h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
