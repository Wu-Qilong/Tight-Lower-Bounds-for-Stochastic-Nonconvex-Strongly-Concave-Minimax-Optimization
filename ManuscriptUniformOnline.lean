import ManuscriptOracleNull

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u

/-- A concrete subclass of the paper's instances, sufficient to contain every hard instance.
Both blocks have dimension T and the fresh seed is Bernoulli. -/
structure BernoulliInstance where
  T : ℕ
  population : PopulationObjective T
  oracle : StochasticOracle T Bool
  p : ℝ
  p_pos : 0 < p
  p_le_one : p ≤ 1

namespace BernoulliInstance

def ValidBV (M μ Δ σ : ℝ) (I : BernoulliInstance) : Prop :=
  InNCSCClass I.population M μ Δ ∧
  OracleUnbiased I.population (bernoulliLaw I.p) I.oracle ∧
  OracleBoundedVariance I.population (bernoulliLaw I.p) I.oracle σ

def ValidAS (M μ Δ σ : ℝ) (I : BernoulliInstance) : Prop :=
  I.ValidBV M μ Δ σ ∧ OracleAveragedSmooth (bernoulliLaw I.p) I.oracle M

def moreauValue (I : BernoulliInstance) (M : ℝ) (x : Vec I.T) : ℝ :=
  sInf (Set.range (fun v => I.population.Phi v + M * ‖v - x‖ ^ 2))

end BernoulliInstance

inductive StationarityObjective where
  | primal
  | moreau

/-- The Moreau branch uses Mathlib's derivative, not an unconstrained supplied vector field.
Differentiability is proved at the hard instances below. -/
def StationarityObjective.field (m : StationarityObjective) (M : ℝ) (I : BernoulliInstance) :
    Vec I.T → Vec I.T :=
  match m with
  | .primal => I.population.gradPhi
  | .moreau => gradient (I.moreauValue M)

/-- One policy per dimension and internal seed, with no objective/oracle argument. -/
abbrev UniformOnlineAlgorithm (Ω : Type u) (K N : ℕ) := ∀ T, Ω → OnlinePolicy T K N

def UniformOnlineLegal {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (valid : BernoulliInstance → Prop) {K N : ℕ} (A : UniformOnlineAlgorithm Ω K N) : Prop :=
  ∀ I, valid I → AEOracleLegal ρ I.oracle I.p (A I.T)

abbrev UniformBudgetAlgorithm {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (valid : BernoulliInstance → Prop) (K N : ℕ) :=
  {A : UniformOnlineAlgorithm Ω K N // UniformOnlineLegal ρ valid A}

def uniformOnlineRisk {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (c : StationarityCriterion) (m : StationarityObjective) (M : ℝ)
    {valid : BernoulliInstance → Prop} {K N : ℕ}
    (A : UniformBudgetAlgorithm ρ valid K N) (I : BernoulliInstance) : ℝ≥0∞ :=
  onlineRisk c ρ I.oracle I.p (m.field M I) (A.val I.T)

/-- A fully instantiated budget-infimum for the concrete Bernoulli online class.
No caller-supplied execution map or risk-identification hypothesis remains. -/
def uniformOnlineComplexity {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (valid : BernoulliInstance → Prop) (K : ℕ) (c : StationarityCriterion)
    (m : StationarityObjective) (M ε : ℝ) : ℝ≥0∞ :=
  uniformBudgetComplexity valid
    (fun N (A : UniformBudgetAlgorithm ρ valid K N) I => uniformOnlineRisk ρ c m M A I)
    (c.target ε)

/-- The concrete class is nonempty, including budget zero. -/
def originUniformAlgorithm {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (valid : BernoulliInstance → Prop) (K N : ℕ) : UniformBudgetAlgorithm ρ valid K N :=
  ⟨fun _ _ => .halt 0, fun I _ w _ => Filter.Eventually.of_forall (fun _ =>
    OnlinePolicy.halt_zero_legal I.oracle N N K w)⟩

/-- The same causal guard works simultaneously at every instance; it takes no oracle input. -/
def repairedUniformAlgorithm {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (valid : BernoulliInstance → Prop) {K N : ℕ} (A : UniformOnlineAlgorithm Ω K N) :
    UniformBudgetAlgorithm ρ valid K N :=
  ⟨fun T ω => (A T ω).repairBudget, fun I _ w _ => Filter.Eventually.of_forall
    (fun ω => (A I.T ω).repairBudget_legal I.oracle w)⟩

theorem uniformOnlineRisk_repair_eq {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω)
    (c : StationarityCriterion) (m : StationarityObjective) (M : ℝ)
    {valid : BernoulliInstance → Prop} {K N : ℕ} (A : UniformBudgetAlgorithm ρ valid K N)
    (I : BernoulliInstance) (hI : valid I) :
    uniformOnlineRisk ρ c m M A I =
      uniformOnlineRisk ρ c m M (repairedUniformAlgorithm ρ valid A.val) I :=
  onlineRisk_eq_repair c ρ I.oracle I.p (le_of_lt I.p_pos) I.p_le_one _ _ (A.property I hI)

namespace ManuscriptBVProblem

def onlineInstance (P : ManuscriptBVProblem) : BernoulliInstance :=
  ⟨P.T, P.population, P.oracle, P.p, P.p_pos, P.p_le_one⟩

theorem onlineInstance_valid (P : ManuscriptBVProblem) : P.onlineInstance.ValidBV P.M P.μ P.Δ P.σ :=
  ⟨P.in_class, P.unbiased, P.variance⟩

theorem online_moreau_gradient (P : ManuscriptBVProblem) :
    gradient (P.onlineInstance.moreauValue P.M) = P.moreau.envelopeGrad := by
  have hf : P.onlineInstance.moreauValue P.M = P.moreau.envelope := by
    funext x
    exact (P.moreau_is_envelope x).symm
  rw [hf]
  funext x
  exact (P.moreau_hasGradient x).gradient

/-- Both criteria and both gradients, with concrete uniform algorithms and no execution adapter. -/
theorem concrete_online_complexity_lower (P : ManuscriptBVProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (K : ℕ) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformOnlineComplexity ρ (BernoulliInstance.ValidBV P.M P.μ P.Δ P.σ) K c m P.M P.ε := by
  apply uniformBudgetComplexity_lower_of_fixed_instance _ _ _ _ P.onlineInstance P.onlineInstance_valid
  intro N A h
  have hl := A.property P.onlineInstance P.onlineInstance_valid
  cases m with
  | primal => exact P.ae_online_budget_lower ρ (A.val P.T) c hl h
  | moreau =>
    change onlineRisk c ρ P.oracle P.p (gradient (P.onlineInstance.moreauValue P.M))
      (A.val P.T) ≤ c.target P.ε at h
    rw [P.online_moreau_gradient] at h
    exact P.ae_online_moreau_budget_lower ρ (A.val P.T) c hl h

end ManuscriptBVProblem

namespace ManuscriptASProblem

def onlineInstance (P : ManuscriptASProblem) : BernoulliInstance :=
  ⟨P.T, P.population, P.oracle, P.p, P.p_pos, P.p_le_one⟩

theorem onlineInstance_valid (P : ManuscriptASProblem) : P.onlineInstance.ValidAS P.M P.μ P.Δ P.σ :=
  ⟨⟨P.in_class, P.unbiased, P.variance⟩, P.averaged_smooth⟩

theorem online_moreau_gradient (P : ManuscriptASProblem) :
    gradient (P.onlineInstance.moreauValue P.M) = P.moreau.envelopeGrad := by
  have hf : P.onlineInstance.moreauValue P.M = P.moreau.envelope := by
    funext x
    exact (P.moreau_is_envelope x).symm
  rw [hf]
  funext x
  exact (P.moreau_hasGradient x).gradient

theorem concrete_online_complexity_lower (P : ManuscriptASProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (K : ℕ) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      uniformOnlineComplexity ρ (BernoulliInstance.ValidAS P.M P.μ P.Δ P.σ) K c m P.M P.ε := by
  apply uniformBudgetComplexity_lower_of_fixed_instance _ _ _ _ P.onlineInstance P.onlineInstance_valid
  intro N A h
  have hl := A.property P.onlineInstance P.onlineInstance_valid
  cases m with
  | primal => exact P.ae_online_budget_lower ρ (A.val P.T) c hl h
  | moreau =>
    change onlineRisk c ρ P.oracle P.p (gradient (P.onlineInstance.moreauValue P.M))
      (A.val P.T) ≤ c.target P.ε at h
    rw [P.online_moreau_gradient] at h
    exact P.ae_online_moreau_budget_lower ρ (A.val P.T) c hl h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
