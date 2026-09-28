import ManuscriptMoreauRisk

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u

/-- Keep the two blocks' coordinates distinct, as in (9)--(10). -/
def jointSupport {T : ℕ} (z : Vec T × Vec T) : Set (Fin T ⊕ Fin T) :=
  {c | Sum.elim z.1 z.2 c ≠ 0}

def jointRevealedBefore {T R K : ℕ} (tr : InteractionTrace T R K) (t : Fin R) :
    Set (Fin T ⊕ Fin T) :=
  {c | ∃ s : Fin R, s.val < t.val ∧ ∃ k r, tr.response s k = some r ∧ c ∈ jointSupport r}

def jointRevealedAll {T R K : ℕ} (tr : InteractionTrace T R K) : Set (Fin T ⊕ Fin T) :=
  {c | ∃ s k r, tr.response s k = some r ∧ c ∈ jointSupport r}

/-- The coordinatewise standard condition, with output embedded as `(xhat,0)`. -/
def StandardZeroRespectingTrace {T R K : ℕ} (tr : InteractionTrace T R K) : Prop :=
  (∀ t k q, tr.query t k = some q → jointSupport q ⊆ jointRevealedBefore tr t) ∧
    jointSupport (tr.output, 0) ⊆ jointRevealedAll tr

theorem standardZeroRespecting_implies_pair {T R K : ℕ} (tr : InteractionTrace T R K)
    (h : StandardZeroRespectingTrace tr) : PairZeroRespectingTrace tr := by
  constructor
  · intro t k q hq i hi
    rcases hi with hx | hy
    · obtain ⟨s, hs, k', r, hr, hi'⟩ := h.1 t k q hq (show Sum.inl i ∈ jointSupport q from hx)
      exact ⟨s, hs, k', r, hr, Or.inl hi'⟩
    · obtain ⟨s, hs, k', r, hr, hi'⟩ := h.1 t k q hq (show Sum.inr i ∈ jointSupport q from hy)
      exact ⟨s, hs, k', r, hr, Or.inr hi'⟩
  · intro i hi
    obtain ⟨s, k, r, hr, hi'⟩ := h.2 (show Sum.inl i ∈ jointSupport (tr.output, 0) from hi)
    exact ⟨s, k, r, hr, Or.inl hi'⟩

/-- Response-causal simultaneous queries, with standard rather than pair support. -/
structure StandardBernoulliRun (T H K : ℕ) (O : StochasticOracle T Bool) where
  trace : RoundWorld H → InteractionTrace T H K
  causal_queries : ∀ w w' t,
    (∀ s : Fin H, s.val < t.val → ∀ k, (trace w).response s k = (trace w').response s k) →
    (trace w).query t = (trace w').query t
  causal_output : ∀ w w',
    (∀ t k, (trace w).response t k = (trace w').response t k) →
    (trace w).output = (trace w').output
  response_consistent : ∀ w, OracleConsistentTrace O w (trace w)
  zero_respecting : ∀ w, StandardZeroRespectingTrace (trace w)

def StandardBernoulliRun.toPair {T H K : ℕ} {O : StochasticOracle T Bool}
    (A : StandardBernoulliRun T H K O) : BernoulliRun T H K O where
  trace := A.trace
  causal_queries := A.causal_queries
  causal_output := A.causal_output
  response_consistent := A.response_consistent
  zero_respecting := fun w => standardZeroRespecting_implies_pair _ (A.zero_respecting w)

theorem StandardBernoulliRun.responses_eq_before {T H K : ℕ} {O : StochasticOracle T Bool}
    (A : StandardBernoulliRun T H K O) (w w' : RoundWorld H) (n : ℕ)
    (hw : ∀ t : Fin H, t.val < n → w t = w' t) :
    ∀ t : Fin H, t.val < n → ∀ k, (A.trace w).response t k = (A.trace w').response t k := by
  have aux : ∀ m (t : Fin H), t.val = m → m < n →
      ∀ k, (A.trace w).response t k = (A.trace w').response t k := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro t ht htn k
      have hq := A.causal_queries w w' t (by
        intro s hs k'
        exact ih s.val (by omega) s rfl (by omega) k')
      rw [A.response_consistent w t k, A.response_consistent w' t k,
        congrFun hq k, hw t (by omega)]
  intro t ht k
  exact aux t.val t rfl ht k

/-- A bounded stopping protocol represented on a presampled finite gate horizon.
After termination the slots are empty, not additional oracle calls. -/
structure StoppedStandardRun (T H K : ℕ) (O : StochasticOracle T Bool)
    extends StandardBernoulliRun T H K O where
  stop : RoundWorld H → ℕ
  stop_le : ∀ w, stop w ≤ H
  causal_stop : ∀ w w' n, n ≤ H →
    (∀ t : Fin H, t.val < n → ∀ k, (trace w).response t k = (trace w').response t k) →
    (stop w ≤ n ↔ stop w' ≤ n)
  active_batch : ∀ w t, t.val < stop w →
    1 ≤ batchSize (trace w) t ∧ batchSize (trace w) t ≤ K
  inactive_query : ∀ w t, stop w ≤ t.val → ∀ k, (trace w).query t k = none

namespace StoppedStandardRun

variable {T H K : ℕ} {O : StochasticOracle T Bool}

def toPair (A : StoppedStandardRun T H K O) : BernoulliRun T H K O :=
  A.toStandardBernoulliRun.toPair

theorem inactive_response (A : StoppedStandardRun T H K O) (w : RoundWorld H)
    (t : Fin H) (ht : A.stop w ≤ t.val) (k : Fin K) : (A.trace w).response t k = none := by
  rw [A.response_consistent w t k, A.inactive_query w t ht k]

theorem inactive_batch (A : StoppedStandardRun T H K O) (w : RoundWorld H)
    (t : Fin H) (ht : A.stop w ≤ t.val) : batchSize (A.trace w) t = 0 := by
  classical
  simp [batchSize, A.inactive_query w t ht]

/-- No padded slot changes the output or either finite-oracle risk: `toPair` keeps the trace. -/
theorem output_preserved (A : StoppedStandardRun T H K O) (w : RoundWorld H) :
    (A.toPair.trace w).output = (A.trace w).output := rfl

theorem count_preserved (A : StoppedStandardRun T H K O) (w : RoundWorld H) :
    returnedGradientCount (A.toPair.trace w) = returnedGradientCount (A.trace w) := rfl

/-- Presampling unused gates cannot change the stopping time or the reported output. -/
theorem unused_seeds_irrelevant (A : StoppedStandardRun T H K O) (w w' : RoundWorld H)
    (hw : ∀ t : Fin H, t.val < A.stop w → w t = w' t) :
    A.stop w = A.stop w' ∧ (A.trace w).output = (A.trace w').output := by
  have hr := A.toStandardBernoulliRun.responses_eq_before w w' (A.stop w) hw
  have hs : A.stop w' ≤ A.stop w :=
    (A.causal_stop w w' (A.stop w) (A.stop_le w) hr).mp (Nat.le_refl _)
  have hs' : A.stop w ≤ A.stop w' :=
    (A.causal_stop w w' (A.stop w') (A.stop_le w') (by
      intro t ht k
      exact hr t (lt_of_lt_of_le ht hs) k)).mpr (Nat.le_refl _)
  have he := Nat.le_antisymm hs' hs
  refine ⟨he, A.causal_output w w' ?_⟩
  intro t k
  by_cases ht : t.val < A.stop w
  · exact hr t ht k
  · rw [A.inactive_response w t (Nat.le_of_not_gt ht) k,
      A.inactive_response w' t (by omega) k]

theorem count_active_rounds (A : StoppedStandardRun T H K O) (w : RoundWorld H) :
    A.stop w ≤ returnedGradientCount (A.trace w) ∧
      returnedGradientCount (A.trace w) ≤ K * A.stop w := by
  classical
  have hc : (∑ t : Fin H, if t.val < A.stop w then 1 else 0) = A.stop w := by
    simpa only [Fintype.card_subtype, Finset.card_filter] using
      (Fintype.card_fin_lt_of_le (A.stop_le w))
  constructor
  · rw [← hc]
    apply Finset.sum_le_sum
    intro t ht
    split_ifs with ha
    · exact (A.active_batch w t ha).1
    · exact Nat.zero_le _
  · calc
      _ ≤ ∑ t : Fin H, K * (if t.val < A.stop w then 1 else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs with ha
        · simpa using (A.active_batch w t ha).2
        · simp [A.inactive_batch w t (Nat.le_of_not_gt ha)]
      _ = K * A.stop w := by rw [← Finset.mul_sum, hc]

end StoppedStandardRun

/-- An at-most-N-call execution has at most N nonempty rounds; unused gates are padded.
The budget is pathwise, not an expected cost. -/
structure BudgetStandardRun (T N K : ℕ) (O : StochasticOracle T Bool)
    extends StoppedStandardRun T N K O where
  calls_le : ∀ w, returnedGradientCount (trace w) ≤ N

def BudgetStandardRun.toPair {T N K : ℕ} {O : StochasticOracle T Bool}
    (A : BudgetStandardRun T N K O) : BernoulliRun T N K O := A.toStoppedStandardRun.toPair

/-- The budget protocol is nonempty even at N=0: stop immediately and output the origin. -/
def BudgetStandardRun.stopImmediately (T N K : ℕ) (O : StochasticOracle T Bool) :
    BudgetStandardRun T N K O where
  trace := fun _ => ⟨fun _ _ => none, fun _ _ => none, 0⟩
  causal_queries := by intros; rfl
  causal_output := by intros; rfl
  response_consistent := by intros; intro t k; rfl
  zero_respecting := by
    intro w
    constructor
    · intro t k q h; cases h
    · intro c hc
      cases c <;> simp [jointSupport] at hc
  stop := fun _ => 0
  stop_le := by intro w; exact Nat.zero_le _
  causal_stop := by intros; rfl
  active_batch := by intro w t ht; omega
  inactive_query := by intros; rfl
  calls_le := by
    intro w
    simp [returnedGradientCount, batchSize]

/-- Both criteria share exactly the same independent internal-seed semantics. -/
inductive StationarityCriterion where
  | norm
  | squared

def StationarityCriterion.target (c : StationarityCriterion) (ε : ℝ) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ε
  | .squared => ENNReal.ofReal (ε ^ 2)

def StationarityCriterion.risk {Ω : Type u} [MeasurableSpace Ω]
    (c : StationarityCriterion) (ρ : Measure Ω) {T H K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T H K O) : ℝ≥0∞ :=
  match c with
  | .norm => internalRandomNormRisk ρ p g A
  | .squared => internalRandomStationarityRisk ρ p g A

theorem StationarityCriterion.success_cases {Ω : Type u} [MeasurableSpace Ω]
    (c : StationarityCriterion) (ρ : Measure Ω) {T H K : ℕ} {O : StochasticOracle T Bool}
    (p ε : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T H K O)
    (h : c.risk ρ p g A ≤ c.target ε) :
    internalRandomNormRisk ρ p g A ≤ ENNReal.ofReal ε ∨
      internalRandomStationarityRisk ρ p g A ≤ ENNReal.ofReal (ε ^ 2) := by
  cases c with
  | norm => exact Or.inl h
  | squared => exact Or.inr h

namespace ManuscriptBVProblem

/-- A lower bound on the pathwise call budget, allowing zero-cost padding after stopping. -/
theorem standard_budget_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → BudgetStandardRun P.T N K P.oracle) (c : StationarityCriterion)
    (h : c.risk ρ P.p P.population.gradPhi (fun ω => (A ω).toPair) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.randomized_rate_lower ρ _ (c.success_cases ρ P.p P.ε _ _ h)

theorem standard_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → BudgetStandardRun P.T N K P.oracle) (c : StationarityCriterion)
    (h : c.risk ρ P.p P.moreau.envelopeGrad (fun ω => (A ω).toPair) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.moreau_rate_lower ρ _ (c.success_cases ρ P.p P.ε _ _ h)

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem standard_budget_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → BudgetStandardRun P.T N K P.oracle) (c : StationarityCriterion)
    (h : c.risk ρ P.p P.population.gradPhi (fun ω => (A ω).toPair) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.randomized_rate_lower ρ _ (c.success_cases ρ P.p P.ε _ _ h)

theorem standard_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → BudgetStandardRun P.T N K P.oracle) (c : StationarityCriterion)
    (h : c.risk ρ P.p P.moreau.envelopeGrad (fun ω => (A ω).toPair) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) :=
  P.moreau_rate_lower ρ _ (c.success_cases ρ P.p P.ε _ _ h)

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
