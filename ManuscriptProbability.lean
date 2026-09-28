import ManuscriptUniformOnline

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- The finite Bernoulli oracle-world law, expressed as a genuine measure. -/
def roundMeasure (p : ℝ) (N : ℕ) : Measure (RoundWorld N) :=
  Measure.sum (fun w => ENNReal.ofReal (roundWeight p w) • Measure.dirac w)

theorem roundMeasure_univ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    roundMeasure p N Set.univ = 1 := by
  simp only [roundMeasure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  · simp [roundWeight_total]
  · intro w hw
    exact roundWeight_nonneg p hp0 hp1 w

theorem roundMeasure_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    IsProbabilityMeasure (roundMeasure p N) := ⟨roundMeasure_univ p hp0 hp1 N⟩

theorem lintegral_roundMeasure (p : ℝ) {N : ℕ} (f : RoundWorld N → ℝ≥0∞) :
    (∫⁻ w, f w ∂roundMeasure p N) = ∑ w, ENNReal.ofReal (roundWeight p w) * f w := by
  simp [roundMeasure, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac, tsum_fintype]

theorem ofReal_roundExpect_eq_lintegral (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {N : ℕ} (f : RoundWorld N → ℝ) (hf : ∀ w, 0 ≤ f w) :
    ENNReal.ofReal (roundExpect p f) = ∫⁻ w, ENNReal.ofReal (f w) ∂roundMeasure p N := by
  rw [lintegral_roundMeasure, roundExpect, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro w hw
    exact ENNReal.ofReal_mul (roundWeight_nonneg p hp0 hp1 w)
  · intro w hw
    exact mul_nonneg (roundWeight_nonneg p hp0 hp1 w) (hf w)

theorem ae_roundMeasure_iff (p : ℝ) {N : ℕ} (q : RoundWorld N → Prop) :
    (∀ᵐ w ∂roundMeasure p N, q w) ↔ ∀ w, 0 < roundWeight p w → q w := by
  rw [roundMeasure, Measure.ae_sum_iff]
  apply forall_congr'
  intro w
  by_cases h : 0 < roundWeight p w
  · have hn : ENNReal.ofReal (roundWeight p w) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr h)
    simp [Measure.ae_smul_measure_iff hn, ae_dirac_eq, h]
  · have hz : ENNReal.ofReal (roundWeight p w) = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h)
    simp [hz, h]

/-- The previous finite-world legality condition is precisely iterated almost-sure legality. -/
theorem aeOracleLegal_iff_iterated {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (A : Ω → OnlinePolicy T K N) :
    AEOracleLegal ρ O p A ↔ ∀ᵐ ω ∂ρ, ∀ᵐ w ∂roundMeasure p N,
      StandardZeroRespectingTrace ((A ω).execute O w) ∧
        returnedGradientCount ((A ω).execute O w) ≤ N := by
  simp only [ae_roundMeasure_iff]
  constructor
  · exact fun h => h.eventually_all ρ O p A
  · intro h w hw
    filter_upwards [h] with ω hω
    exact hω w hw

theorem aeOracleLegal_iff_product {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Ω → OnlinePolicy T K N)
    (hm : MeasurableSet {z : Ω × RoundWorld N |
      StandardZeroRespectingTrace ((A z.1).execute O z.2) ∧
        returnedGradientCount ((A z.1).execute O z.2) ≤ N}) :
    AEOracleLegal ρ O p A ↔ ∀ᵐ z ∂ρ.prod (roundMeasure p N),
      StandardZeroRespectingTrace ((A z.1).execute O z.2) ∧
        returnedGradientCount ((A z.1).execute O z.2) ≤ N := by
  letI := roundMeasure_probability p hp0 hp1 N
  rw [Measure.ae_prod_iff_ae_ae hm]
  exact aeOracleLegal_iff_iterated ρ O p A

def onlineLoss {Ω : Type*} (c : StationarityCriterion) {T N K : ℕ}
    (O : StochasticOracle T Bool) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N)
    (z : Ω × RoundWorld N) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g ((A z.1).execute O z.2).output‖
  | .squared => ENNReal.ofReal (‖g ((A z.1).execute O z.2).output‖ ^ 2)

theorem onlineRisk_eq_iterated {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N) :
    onlineRisk c ρ O p g A = ∫⁻ ω, ∫⁻ w, onlineLoss c O g A (ω, w) ∂roundMeasure p N ∂ρ := by
  cases c <;> apply lintegral_congr <;> intro ω
  · exact ofReal_roundExpect_eq_lintegral p hp0 hp1 _ (fun w => norm_nonneg _)
  · exact ofReal_roundExpect_eq_lintegral p hp0 hp1 _ (fun w => sq_nonneg _)

/-- Tonelli's standard product-space expectation, with its measurability hypothesis explicit. -/
theorem onlineRisk_eq_product {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N)
    (hm : AEMeasurable (onlineLoss c O g A) (ρ.prod (roundMeasure p N))) :
    onlineRisk c ρ O p g A = ∫⁻ z, onlineLoss c O g A z ∂ρ.prod (roundMeasure p N) := by
  letI := roundMeasure_probability p hp0 hp1 N
  rw [onlineRisk_eq_iterated c ρ O p hp0 hp1 g A, lintegral_prod _ hm]

theorem measurable_onlineLoss {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    {T N K : ℕ} (O : StochasticOracle T Bool) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N)
    (hg : Measurable g) (hA : ∀ w, Measurable (fun ω => ((A ω).execute O w).output)) :
    Measurable (onlineLoss c O g A) := by
  apply measurable_from_prod_countable
  intro w
  cases c
  · exact (hg.comp (hA w)).norm.ennreal_ofReal
  · exact ((hg.comp (hA w)).norm.pow_const 2).ennreal_ofReal

/-- A product-space formulation of legality; measurability is not silently assumed. -/
def ProductLegal {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (A : Ω → OnlinePolicy T K N) : Prop :=
  MeasurableSet {z : Ω × RoundWorld N |
    StandardZeroRespectingTrace ((A z.1).execute O z.2) ∧
      returnedGradientCount ((A z.1).execute O z.2) ≤ N} ∧
  ∀ᵐ z ∂ρ.prod (roundMeasure p N),
    StandardZeroRespectingTrace ((A z.1).execute O z.2) ∧
      returnedGradientCount ((A z.1).execute O z.2) ≤ N

theorem ProductLegal.toAEOracleLegal {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Ω → OnlinePolicy T K N) (h : ProductLegal ρ O p A) : AEOracleLegal ρ O p A :=
  (aeOracleLegal_iff_product ρ O p hp0 hp1 A h.1).mpr h.2

namespace ManuscriptBVProblem

theorem product_online_budget_lower (P : ManuscriptBVProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : ProductLegal ρ P.oracle P.p A)
    (hm : AEMeasurable (onlineLoss c P.oracle P.population.gradPhi A) (ρ.prod (roundMeasure P.p N)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  apply P.ae_online_budget_lower ρ A c
    (hlegal.toAEOracleLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A)
  rwa [onlineRisk_eq_product c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hm]

theorem product_online_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : ProductLegal ρ P.oracle P.p A)
    (hm : AEMeasurable (onlineLoss c P.oracle P.moreau.envelopeGrad A) (ρ.prod (roundMeasure P.p N)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  apply P.ae_online_moreau_budget_lower ρ A c
    (hlegal.toAEOracleLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A)
  rwa [onlineRisk_eq_product c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hm]

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem product_online_budget_lower (P : ManuscriptASProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : ProductLegal ρ P.oracle P.p A)
    (hm : AEMeasurable (onlineLoss c P.oracle P.population.gradPhi A) (ρ.prod (roundMeasure P.p N)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  apply P.ae_online_budget_lower ρ A c
    (hlegal.toAEOracleLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A)
  rwa [onlineRisk_eq_product c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hm]

theorem product_online_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (hlegal : ProductLegal ρ P.oracle P.p A)
    (hm : AEMeasurable (onlineLoss c P.oracle P.moreau.envelopeGrad A) (ρ.prod (roundMeasure P.p N)))
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  apply P.ae_online_moreau_budget_lower ρ A c
    (hlegal.toAEOracleLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A)
  rwa [onlineRisk_eq_product c ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one _ A hm]

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
