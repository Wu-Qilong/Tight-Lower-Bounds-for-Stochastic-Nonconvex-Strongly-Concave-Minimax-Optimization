import ManuscriptAlgorithms

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u v w

/-- Worst-case risk over the admissible instances, with values in the extended nonnegative reals. -/
def worstCaseBudgetRisk {Instance : Type w} {Algorithm : ℕ → Type v}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (N : ℕ) (A : Algorithm N) : ℝ≥0∞ := ⨆ I : {I // valid I}, risk N A I.val

/-- The budget-infimum form of (12), not the legacy inf-sup-first-success definition.
`Algorithm N` is the caller's class of protocols using at most N calls on every run. -/
def uniformBudgetComplexity {Instance : Type w} {Algorithm : ℕ → Type v}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (target : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {b | ∃ N : ℕ, b = (N : ℝ≥0∞) ∧ ∃ A : Algorithm N, worstCaseBudgetRisk valid risk N A ≤ target}

theorem worstCaseBudgetRisk_le_iff {Instance : Type w} {Algorithm : ℕ → Type v}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (N : ℕ) (A : Algorithm N) (target : ℝ≥0∞) :
    worstCaseBudgetRisk valid risk N A ≤ target ↔ ∀ I, valid I → risk N A I ≤ target := by
  simp only [worstCaseBudgetRisk, iSup_le_iff]
  exact ⟨fun h I hI => h ⟨I, hI⟩, fun h I => h I.val I.property⟩

theorem uniformBudgetComplexity_eq_top_of_no_success {Instance : Type w} {Algorithm : ℕ → Type v}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (target : ℝ≥0∞)
    (h : ∀ N (A : Algorithm N), ¬worstCaseBudgetRisk valid risk N A ≤ target) :
    uniformBudgetComplexity valid risk target = ⊤ := by
  have hs : {b : ℝ≥0∞ | ∃ N : ℕ, b = (N : ℝ≥0∞) ∧ ∃ A : Algorithm N,
      worstCaseBudgetRisk valid risk N A ≤ target} = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    rintro b ⟨N, hb, A, hA⟩
    exact h N A hA
  simp [uniformBudgetComplexity, hs]

/-- A single admissible instance obstructing every budgeted protocol suffices for minimax.
No interchange of infimum and supremum is used. -/
theorem uniformBudgetComplexity_lower_of_fixed_instance
    {Instance : Type w} {Algorithm : ℕ → Type v}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (target : ℝ≥0∞) (b : ℝ) (I : Instance) (hI : valid I)
    (hlower : ∀ N (A : Algorithm N), risk N A I ≤ target → b < (N : ℝ)) :
    ENNReal.ofReal b ≤ uniformBudgetComplexity valid risk target := by
  apply le_sInf
  rintro z ⟨N, rfl, A, hA⟩
  have h := hlower N A ((worstCaseBudgetRisk_le_iff valid risk N A target).mp hA I hI)
  calc
    ENNReal.ofReal b ≤ ENNReal.ofReal (N : ℝ) := ENNReal.ofReal_le_ofReal (le_of_lt h)
    _ = (N : ℝ≥0∞) := by simp

namespace ManuscriptBVProblem

/-- Transfer to any uniform algorithm/instance interface whose hard-instance execution
and risk are identified explicitly. The analytic lower bound is proved, not a hypothesis. -/
theorem uniform_complexity_lower (P : ManuscriptBVProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Instance : Type w} {Algorithm : ℕ → Type v} {K : ℕ}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (I : Instance) (hI : valid I) (c : StationarityCriterion)
    (execute : ∀ N, Algorithm N → Ω → BudgetStandardRun P.T N K P.oracle)
    (risk_at_hard : ∀ N (A : Algorithm N), risk N A I =
      c.risk ρ P.p P.population.gradPhi (fun ω => (execute N A ω).toPair)) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformBudgetComplexity valid risk (c.target P.ε) := by
  apply uniformBudgetComplexity_lower_of_fixed_instance valid risk (c.target P.ε) _ I hI
  intro N A h
  rw [risk_at_hard] at h
  exact P.standard_budget_lower ρ (execute N A) c h

theorem uniform_moreau_complexity_lower (P : ManuscriptBVProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Instance : Type w} {Algorithm : ℕ → Type v} {K : ℕ}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (I : Instance) (hI : valid I) (c : StationarityCriterion)
    (execute : ∀ N, Algorithm N → Ω → BudgetStandardRun P.T N K P.oracle)
    (risk_at_hard : ∀ N (A : Algorithm N), risk N A I =
      c.risk ρ P.p P.moreau.envelopeGrad (fun ω => (execute N A ω).toPair)) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformBudgetComplexity valid risk (c.target P.ε) := by
  apply uniformBudgetComplexity_lower_of_fixed_instance valid risk (c.target P.ε) _ I hI
  intro N A h
  rw [risk_at_hard] at h
  exact P.standard_moreau_budget_lower ρ (execute N A) c h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem uniform_complexity_lower (P : ManuscriptASProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Instance : Type w} {Algorithm : ℕ → Type v} {K : ℕ}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (I : Instance) (hI : valid I) (c : StationarityCriterion)
    (execute : ∀ N, Algorithm N → Ω → BudgetStandardRun P.T N K P.oracle)
    (risk_at_hard : ∀ N (A : Algorithm N), risk N A I =
      c.risk ρ P.p P.population.gradPhi (fun ω => (execute N A ω).toPair)) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformBudgetComplexity valid risk (c.target P.ε) := by
  apply uniformBudgetComplexity_lower_of_fixed_instance valid risk (c.target P.ε) _ I hI
  intro N A h
  rw [risk_at_hard] at h
  exact P.standard_budget_lower ρ (execute N A) c h

theorem uniform_moreau_complexity_lower (P : ManuscriptASProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Instance : Type w} {Algorithm : ℕ → Type v} {K : ℕ}
    (valid : Instance → Prop) (risk : ∀ N, Algorithm N → Instance → ℝ≥0∞)
    (I : Instance) (hI : valid I) (c : StationarityCriterion)
    (execute : ∀ N, Algorithm N → Ω → BudgetStandardRun P.T N K P.oracle)
    (risk_at_hard : ∀ N (A : Algorithm N), risk N A I =
      c.risk ρ P.p P.moreau.envelopeGrad (fun ω => (execute N A ω).toPair)) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformBudgetComplexity valid risk (c.target P.ε) := by
  apply uniformBudgetComplexity_lower_of_fixed_instance valid risk (c.target P.ε) _ I hI
  intro N A h
  rw [risk_at_hard] at h
  exact P.standard_moreau_budget_lower ρ (execute N A) c h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
