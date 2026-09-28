import ManuscriptOnline

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u

theorem roundWeight_pos_of_non_degenerate (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    {N : ℕ} (w : RoundWorld N) : 0 < roundWeight p w := by
  unfold roundWeight
  apply Finset.prod_pos
  intro t ht
  split
  · exact hp
  · linarith

/-- On a finite non-degenerate Bernoulli world, taking the union of the finitely many
internal-seed null sets yields one null set outside which every oracle world is legal. -/
theorem OnlinePolicy.ae_legal_of_worldwise {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (A : Ω → OnlinePolicy T K N)
    (h : ∀ w : RoundWorld N, 0 < roundWeight p w → ∀ᵐ ω ∂ρ,
      StandardZeroRespectingTrace ((A ω).execute O w) ∧
        returnedGradientCount ((A ω).execute O w) ≤ N) :
    ∀ᵐ ω ∂ρ, (A ω).LegalOn O N := by
  exact (ae_all_iff).2 (fun w => h w (roundWeight_pos_of_non_degenerate p hp hp1 w))

/-- Risk of the directly executed online policy, without first assuming legality. -/
def onlineRisk {Ω : Type u} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N) : ℝ≥0∞ :=
  match c with
  | .norm => ∫⁻ ω, ENNReal.ofReal (roundExpect p (fun w => ‖g ((A ω).execute O w).output‖)) ∂ρ
  | .squared => ∫⁻ ω, ENNReal.ofReal (roundExpect p (fun w => ‖g ((A ω).execute O w).output‖ ^ 2)) ∂ρ

namespace OnlinePolicy

variable {T N K : ℕ}

/-- Replace bad internal-seed realizations by the origin-output policy. This selection
depends on the entire policy and fixed instance, never on the realized oracle seed. -/
def normalize (O : StochasticOracle T Bool) (P : OnlinePolicy T K N) : OnlinePolicy T K N := by
  classical
  exact if P.LegalOn O N then P else .halt 0

theorem normalize_legal (O : StochasticOracle T Bool) (P : OnlinePolicy T K N) :
    (P.normalize O).LegalOn O N := by
  classical
  by_cases h : P.LegalOn O N
  · simpa [normalize, h] using h
  · simp [normalize, h, halt_zero_legal O N N K]

theorem normalize_eq (O : StochasticOracle T Bool) (P : OnlinePolicy T K N)
    (h : P.LegalOn O N) : P.normalize O = P := by simp [normalize, h]

def normalizedRun (O : StochasticOracle T Bool) (P : OnlinePolicy T K N) :
    BudgetStandardRun T N K O := (P.normalize O).toBudgetRun O (P.normalize_legal O)

end OnlinePolicy

/-- Removing a null set of bad internal random choices preserves the actual risk.
Legality is still required on every finite oracle world for each remaining internal seed. -/
theorem onlineRisk_eq_normalized {Ω : Type u} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N)
    (hlegal : ∀ᵐ ω ∂ρ, (A ω).LegalOn O N) :
    onlineRisk c ρ O p g A = c.risk ρ p g (fun ω => ((A ω).normalizedRun O).toPair) := by
  cases c <;> apply lintegral_congr_ae <;>
    filter_upwards [hlegal] with ω hω <;>
    simp [StationarityCriterion.risk, internalRandomNormRisk, internalRandomStationarityRisk,
      stationarityNormRisk, stationarityRisk, BudgetStandardRun.toPair,
      StoppedStandardRun.toPair, StandardBernoulliRun.toPair, OnlinePolicy.normalizedRun,
      OnlinePolicy.toBudgetRun, OnlinePolicy.normalize_eq O (A ω) hω]

namespace ManuscriptBVProblem

theorem online_budget_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → OnlinePolicy P.T K N) (c : StationarityCriterion)
    (hlegal : ∀ᵐ ω ∂ρ, (A ω).LegalOn P.oracle N)
    (h : onlineRisk c ρ P.oracle P.p P.population.gradPhi A ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_normalized c ρ P.oracle P.p _ A hlegal] at h
  exact P.standard_budget_lower ρ (fun ω => (A ω).normalizedRun P.oracle) c h

theorem online_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → OnlinePolicy P.T K N) (c : StationarityCriterion)
    (hlegal : ∀ᵐ ω ∂ρ, (A ω).LegalOn P.oracle N)
    (h : onlineRisk c ρ P.oracle P.p P.moreau.envelopeGrad A ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_normalized c ρ P.oracle P.p _ A hlegal] at h
  exact P.standard_moreau_budget_lower ρ (fun ω => (A ω).normalizedRun P.oracle) c h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem online_budget_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → OnlinePolicy P.T K N) (c : StationarityCriterion)
    (hlegal : ∀ᵐ ω ∂ρ, (A ω).LegalOn P.oracle N)
    (h : onlineRisk c ρ P.oracle P.p P.population.gradPhi A ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_normalized c ρ P.oracle P.p _ A hlegal] at h
  exact P.standard_budget_lower ρ (fun ω => (A ω).normalizedRun P.oracle) c h

theorem online_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ}
    (A : Ω → OnlinePolicy P.T K N) (c : StationarityCriterion)
    (hlegal : ∀ᵐ ω ∂ρ, (A ω).LegalOn P.oracle N)
    (h : onlineRisk c ρ P.oracle P.p P.moreau.envelopeGrad A ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  rw [onlineRisk_eq_normalized c ρ P.oracle P.p _ A hlegal] at h
  exact P.standard_moreau_budget_lower ρ (fun ω => (A ω).normalizedRun P.oracle) c h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
