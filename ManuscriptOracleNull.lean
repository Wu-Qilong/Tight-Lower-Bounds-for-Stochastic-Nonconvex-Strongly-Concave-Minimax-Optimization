import ManuscriptCausalRepair

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u

/-- Almost-sure legality in the finite weighted oracle world: zero-mass worlds impose
no constraint. Internal exceptional sets may initially depend on the oracle world. -/
def AEOracleLegal {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (A : Ω → OnlinePolicy T K N) : Prop :=
  ∀ w : RoundWorld N, 0 < roundWeight p w → ∀ᵐ ω ∂ρ,
    StandardZeroRespectingTrace ((A ω).execute O w) ∧
      returnedGradientCount ((A ω).execute O w) ≤ N

def trueOracleWorld (N : ℕ) : RoundWorld N := fun _ => true

theorem roundWeight_one_pos_iff {N : ℕ} (w : RoundWorld N) :
    0 < roundWeight 1 w ↔ w = trueOracleWorld N := by
  classical
  by_cases hw : w = trueOracleWorld N
  · subst w
    simp [roundWeight, trueOracleWorld]
  · have hf : ∃ t, w t = false := by
      by_contra hn
      apply hw
      funext t
      cases ht : w t
      · exact (hn ⟨t, ht⟩).elim
      · rfl
    obtain ⟨t, ht⟩ := hf
    have hz : roundWeight 1 w = 0 := by
      unfold roundWeight
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [ht]
    simp [hz, hw]

/-- At the degenerate endpoint only the actual all-true oracle path is constrained. -/
theorem AEOracleLegal_one_iff {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (A : Ω → OnlinePolicy T K N) :
    AEOracleLegal ρ O 1 A ↔ ∀ᵐ ω ∂ρ,
      StandardZeroRespectingTrace ((A ω).execute O (trueOracleWorld N)) ∧
        returnedGradientCount ((A ω).execute O (trueOracleWorld N)) ≤ N := by
  constructor
  · intro h
    exact h _ ((roundWeight_one_pos_iff _).mpr rfl)
  · intro h w hw
    have he := (roundWeight_one_pos_iff w).mp hw
    simpa [he] using h

theorem AEOracleLegal.eventually_all {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (A : Ω → OnlinePolicy T K N)
    (h : AEOracleLegal ρ O p A) :
    ∀ᵐ ω ∂ρ, ∀ w : RoundWorld N, 0 < roundWeight p w →
      StandardZeroRespectingTrace ((A ω).execute O w) ∧
        returnedGradientCount ((A ω).execute O w) ≤ N := by
  apply (ae_all_iff).2
  intro w
  by_cases hw : 0 < roundWeight p w
  · filter_upwards [h w hw] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall (fun ω h' => (hw h').elim)

/-- Zero-weight worlds disappear from the finite expectation, even at p=1. -/
theorem OnlinePolicy.repair_expectation_eq {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : OnlinePolicy T K N) (loss : Vec T → ℝ)
    (h : ∀ w : RoundWorld N, 0 < roundWeight p w →
      StandardZeroRespectingTrace (P.execute O w) ∧ returnedGradientCount (P.execute O w) ≤ N) :
    roundExpect p (fun w => loss (P.execute O w).output) =
      roundExpect p (fun w => loss (P.repairBudget.execute O w).output) := by
  unfold roundExpect
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hz : roundWeight p w = 0
  · simp [hz]
  · have hp : 0 < roundWeight p w := lt_of_le_of_ne (roundWeight_nonneg p hp0 hp1 w) (Ne.symm hz)
    dsimp only
    rw [P.repairBudget_preserves O w (h w hp).1 (h w hp).2]

theorem onlineRisk_eq_repair {Ω : Type u} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N)
    (h : AEOracleLegal ρ O p A) :
    onlineRisk c ρ O p g A = onlineRisk c ρ O p g (fun ω => (A ω).repairBudget) := by
  have hall := h.eventually_all ρ O p A
  cases c <;> apply lintegral_congr_ae <;> filter_upwards [hall] with ω hω
  · exact congrArg ENNReal.ofReal ((A ω).repair_expectation_eq O p hp0 hp1 (fun x => ‖g x‖) hω)
  · exact congrArg ENNReal.ofReal ((A ω).repair_expectation_eq O p hp0 hp1 (fun x => ‖g x‖ ^ 2) hω)

namespace ManuscriptBVProblem

theorem ae_online_budget_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : AEOracleLegal ρ P.oracle P.p A)
    (h : onlineRisk c ρ P.oracle P.p P.population.gradPhi A ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_repair c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hlegal] at h
  exact P.online_budget_lower ρ (fun ω => (A ω).repairBudget) c
    (Filter.Eventually.of_forall (fun ω => (A ω).repairBudget_legal P.oracle)) h

theorem ae_online_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : AEOracleLegal ρ P.oracle P.p A)
    (h : onlineRisk c ρ P.oracle P.p P.moreau.envelopeGrad A ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_repair c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hlegal] at h
  exact P.online_moreau_budget_lower ρ (fun ω => (A ω).repairBudget) c
    (Filter.Eventually.of_forall (fun ω => (A ω).repairBudget_legal P.oracle)) h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem ae_online_budget_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : AEOracleLegal ρ P.oracle P.p A)
    (h : onlineRisk c ρ P.oracle P.p P.population.gradPhi A ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_repair c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hlegal] at h
  exact P.online_budget_lower ρ (fun ω => (A ω).repairBudget) c
    (Filter.Eventually.of_forall (fun ω => (A ω).repairBudget_legal P.oracle)) h

theorem ae_online_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : AEOracleLegal ρ P.oracle P.p A)
    (h : onlineRisk c ρ P.oracle P.p P.moreau.envelopeGrad A ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_repair c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hlegal] at h
  exact P.online_moreau_budget_lower ρ (fun ω => (A ω).repairBudget) c
    (Filter.Eventually.of_forall (fun ω => (A ω).repairBudget_legal P.oracle)) h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
