import ManuscriptASRate

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u

/-- Nonnegative admissible constants for the population gradient. -/
def populationSmoothConstants {T : ℕ} (I : PopulationObjective T) : Set ℝ :=
  {L | 0 ≤ L ∧ JointSmooth I L}

/-- Admissible uniform inner strong-concavity moduli. -/
def innerStrongConstants {T : ℕ} (I : PopulationObjective T) : Set ℝ :=
  {m | StronglyConcaveY I m}

def averagedSmoothConstants {T : ℕ} {Seed : Type}
    (E : Law Seed) (O : StochasticOracle T Seed) : Set ℝ :=
  {L | 0 ≤ L ∧ OracleAveragedSmooth E O L}

def actualPopulationSmoothness {T : ℕ} (I : PopulationObjective T) : ℝ := sInf (populationSmoothConstants I)
def actualInnerConcavity {T : ℕ} (I : PopulationObjective T) : ℝ := sSup (innerStrongConstants I)
def actualAveragedSmoothness {T : ℕ} {Seed : Type} (E : Law Seed) (O : StochasticOracle T Seed) : ℝ :=
  sInf (averagedSmoothConstants E O)

theorem populationSmoothConstants_closed {T : ℕ} (I : PopulationObjective T) :
    IsClosed (populationSmoothConstants I) := by
  change IsClosed ({L : ℝ | 0 ≤ L} ∩ {L : ℝ | JointSmooth I L})
  apply IsClosed.inter (isClosed_le continuous_const continuous_id)
  simp only [JointSmooth, Set.setOf_forall]
  repeat' (apply isClosed_iInter; intro)
  apply isClosed_le <;> fun_prop

theorem innerStrongConstants_closed {T : ℕ} (I : PopulationObjective T) :
    IsClosed (innerStrongConstants I) := by
  simp only [innerStrongConstants, StronglyConcaveY, Set.setOf_forall]
  repeat' (apply isClosed_iInter; intro)
  apply isClosed_le <;> fun_prop

theorem averagedSmoothConstants_closed {T : ℕ} {Seed : Type}
    (E : Law Seed) (O : StochasticOracle T Seed) : IsClosed (averagedSmoothConstants E O) := by
  change IsClosed ({L : ℝ | 0 ≤ L} ∩ {L : ℝ | OracleAveragedSmooth E O L})
  apply IsClosed.inter (isClosed_le continuous_const continuous_id)
  simp only [OracleAveragedSmooth, Set.setOf_forall]
  repeat' (apply isClosed_iInter; intro)
  apply isClosed_le <;> fun_prop

namespace ActualConditionNumberCertificate

variable {T : ℕ} {I : PopulationObjective T} (A : ActualConditionNumberCertificate I)
include A

theorem smooth_nonempty : (populationSmoothConstants I).Nonempty :=
  ⟨A.Mhi, le_of_lt A.Mhi_pos, A.smooth_upper⟩
theorem smooth_bddBelow : BddBelow (populationSmoothConstants I) :=
  ⟨A.Mlo, fun _ h => A.smooth_lower _ h.1 h.2⟩
theorem strong_nonempty : (innerStrongConstants I).Nonempty := ⟨A.muLo, A.strong_lower⟩
theorem strong_bddAbove : BddAbove (innerStrongConstants I) := ⟨A.muHi, fun _ h => A.strong_upper _ h⟩

theorem optimal_bounds :
    (A.Mlo ≤ actualPopulationSmoothness I ∧ actualPopulationSmoothness I ≤ A.Mhi) ∧
    (A.muLo ≤ actualInnerConcavity I ∧ actualInnerConcavity I ≤ A.muHi) := by
  exact ⟨⟨le_csInf A.smooth_nonempty (fun _ h => A.smooth_lower _ h.1 h.2),
    csInf_le A.smooth_bddBelow ⟨le_of_lt A.Mhi_pos, A.smooth_upper⟩⟩,
    ⟨le_csSup A.strong_bddAbove A.strong_lower,
    csSup_le A.strong_nonempty (fun _ h => A.strong_upper _ h)⟩⟩

/-- The extremal constants are attained, so infimum/supremum agree with smallest/largest. -/
theorem optimal_attained : JointSmooth I (actualPopulationSmoothness I) ∧
    StronglyConcaveY I (actualInnerConcavity I) := by
  exact ⟨((populationSmoothConstants_closed I).csInf_mem A.smooth_nonempty A.smooth_bddBelow).2,
    (innerStrongConstants_closed I).csSup_mem A.strong_nonempty A.strong_bddAbove⟩

theorem optimal_pos : 0 < actualPopulationSmoothness I ∧ 0 < actualInnerConcavity I :=
  ⟨A.Mlo_pos.trans_le A.optimal_bounds.1.1, A.muLo_pos.trans_le A.optimal_bounds.2.1⟩

theorem optimal_extremal :
    (∀ L, 0 ≤ L → JointSmooth I L → actualPopulationSmoothness I ≤ L) ∧
    (∀ m, StronglyConcaveY I m → m ≤ actualInnerConcavity I) :=
  ⟨fun _ hL h => csInf_le A.smooth_bddBelow ⟨hL, h⟩,
    fun _ h => le_csSup A.strong_bddAbove h⟩

end ActualConditionNumberCertificate

namespace ActualAveragedConditionNumberCertificate

variable {T : ℕ} {Seed : Type} {I : PopulationObjective T} {E : Law Seed}
  {O : StochasticOracle T Seed} (A : ActualAveragedConditionNumberCertificate I E O)
include A

theorem smooth_nonempty : (averagedSmoothConstants E O).Nonempty :=
  ⟨A.LbarHi, le_of_lt A.LbarHi_pos, A.averaged_smooth_upper⟩
theorem smooth_bddBelow : BddBelow (averagedSmoothConstants E O) :=
  ⟨A.LbarLo, fun _ h => A.averaged_smooth_lower _ h.1 h.2⟩

theorem optimal_bounds : A.LbarLo ≤ actualAveragedSmoothness E O ∧ actualAveragedSmoothness E O ≤ A.LbarHi :=
  ⟨le_csInf A.smooth_nonempty (fun _ h => A.averaged_smooth_lower _ h.1 h.2),
    csInf_le A.smooth_bddBelow ⟨le_of_lt A.LbarHi_pos, A.averaged_smooth_upper⟩⟩

theorem optimal_attained : OracleAveragedSmooth E O (actualAveragedSmoothness E O) :=
  ((averagedSmoothConstants_closed E O).csInf_mem A.smooth_nonempty A.smooth_bddBelow).2

theorem optimal_pos : 0 < actualAveragedSmoothness E O := A.LbarLo_pos.trans_le A.optimal_bounds.1

theorem optimal_extremal : ∀ L, 0 ≤ L → OracleAveragedSmooth E O L → actualAveragedSmoothness E O ≤ L :=
  fun _ hL h => csInf_le A.smooth_bddBelow ⟨hL, h⟩

end ActualAveragedConditionNumberCertificate

namespace ManuscriptCalibration

theorem primal_curvature_lower (P : ManuscriptCalibration) : P.M / 4 ≤ P.lift.ν * P.lift.γ ^ 2 := by
  have hn : P.μ ≤ P.lift.ν := by rw [P.nu_eq]; linarith [P.h_pos]
  have hm := mul_le_mul_of_nonneg_right hn (sq_nonneg P.gamma)
  have he : P.μ * P.gamma ^ 2 = P.M / 4 := by
    rw [P.gamma_sq]; field_simp [ne_of_gt P.μ_pos]
    ring
  rw [he] at hm
  exact hm

theorem dual_curvature_upper (P : ManuscriptCalibration) : P.lift.ν + ℓ₀ * P.lift.h ≤ 3 * P.μ / 2 := by
  have hh : ℓ₀ * P.lift.h ≤ P.μ / 4 := by
    change 152 * P.h ≤ P.μ / 4
    linarith [P.ell_h_le, P.h_pos]
  linarith [P.nu_le]

/-- Uniform population brackets for either manuscript calibration. -/
def actualCertificate {T : ℕ} (P : ManuscriptCalibration) (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (hk : 8 ≤ P.M / P.μ) : ActualConditionNumberCertificate (P.population C B) where
  Mlo := P.M / 4
  Mhi := P.M / 2
  muLo := P.μ
  muHi := 3 * P.μ / 2
  Mlo_pos := div_pos P.M_pos (by norm_num)
  Mhi_pos := div_pos P.M_pos (by norm_num)
  muLo_pos := P.μ_pos
  muHi_pos := by have := P.μ_pos; positivity
  smooth_upper := populationFromLift_jointSmooth_of_bound C B P.lift
    (canonicalLiftPropertiesCertificate C B P.lift) (P.M / 2) (P.smooth_budget hk)
  smooth_lower := fun L _ h => P.primal_curvature_lower.trans
    (populationFromLift_jointSmooth_lower_primal C B P.lift
      (canonicalLiftPropertiesCertificate C B P.lift) L h)
  strong_lower := P.stronglyConcave C
  strong_upper := fun m h => (populationFromLift_strong_modulus_upper C B P.lift
    (canonicalLiftPropertiesCertificate C B P.lift) m h).trans P.dual_curvature_upper

end ManuscriptCalibration

/-- Scalar conversion from the sharp coefficient brackets to manuscript (38). -/
theorem condition_ratio_of_brackets (M μ L m : ℝ) (hM : 0 < M) (hμ : 0 < μ)
    (hLlo : M / 4 ≤ L) (hLhi : L ≤ M) (hmlo : μ ≤ m) (hmhi : m ≤ 3 * μ / 2) :
    (M / μ) / 6 ≤ L / m ∧ L / m ≤ M / μ := by
  have hmpos : 0 < m := hμ.trans_le hmlo
  have hk : 0 ≤ (M / μ) / 6 := by positivity
  have hlower := mul_le_mul_of_nonneg_left hmhi hk
  have he : ((M / μ) / 6) * (3 * μ / 2) = M / 4 := by field_simp [ne_of_gt hμ]; ring
  rw [he] at hlower
  constructor
  · exact (le_div_iff₀ hmpos).2 (hlower.trans hLlo)
  · exact (div_le_div_of_nonneg_right hLhi (le_of_lt hmpos)).trans
      (div_le_div_of_nonneg_left (le_of_lt hM) hμ hmlo)

namespace ManuscriptBVProblem

def actualCertificate (P : ManuscriptBVProblem) : ActualConditionNumberCertificate P.population :=
  P.calibration.actualCertificate P.chain P.base P.kappa_ge

theorem actual_constants (P : ManuscriptBVProblem) :
    (P.M / 4 ≤ actualPopulationSmoothness P.population ∧ actualPopulationSmoothness P.population ≤ P.M / 2) ∧
    (P.μ ≤ actualInnerConcavity P.population ∧ actualInnerConcavity P.population ≤ 3 * P.μ / 2) :=
  P.actualCertificate.optimal_bounds

theorem actual_condition_number (P : ManuscriptBVProblem) :
    (P.M / P.μ) / 6 ≤ actualPopulationSmoothness P.population / actualInnerConcavity P.population ∧
      actualPopulationSmoothness P.population / actualInnerConcavity P.population ≤ P.M / P.μ := by
  have h := P.actual_constants
  exact condition_ratio_of_brackets _ _ _ _ P.M_pos P.μ_pos h.1.1
    (h.1.2.trans (by linarith [P.M_pos])) h.2.1 h.2.2

theorem actual_constants_attained (P : ManuscriptBVProblem) :
    JointSmooth P.population (actualPopulationSmoothness P.population) ∧
    StronglyConcaveY P.population (actualInnerConcavity P.population) := P.actualCertificate.optimal_attained

/-- One export combines the same fixed hard instance's rate and actual condition number. -/
theorem fixed_instance_with_actual_condition (P : ManuscriptBVProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
    ((P.M / P.μ) / 6 ≤ actualPopulationSmoothness P.population / actualInnerConcavity P.population ∧
      actualPopulationSmoothness P.population / actualInnerConcavity P.population ≤ P.M / P.μ) ∧
    InNCSCClass P.population P.M P.μ P.Δ ∧
    OracleUnbiased P.population (bernoulliLaw P.p) P.oracle ∧
    OracleBoundedVariance P.population (bernoulliLaw P.p) P.oracle P.σ ∧
    ∀ (R K : ℕ) (A : Ω → BernoulliRun P.T R K P.oracle),
      (internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
       internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) →
      (∀ ω w, ValidBatchSizes ((A ω).trace w)) →
      ∀ ω w, manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
        (returnedGradientCount ((A ω).trace w) : ℝ) :=
  ⟨P.actual_condition_number, P.fixed_instance_lower_bound ρ⟩

end ManuscriptBVProblem

namespace ManuscriptASProblem

def actualCertificate (P : ManuscriptASProblem) : ActualConditionNumberCertificate P.population :=
  P.calibration.actualCertificate P.chain P.base P.kappa_ge

def actualAveragedCertificate (P : ManuscriptASProblem) :
    ActualAveragedConditionNumberCertificate P.population (bernoulliLaw P.p) P.oracle where
  LbarLo := P.M / 4
  LbarHi := P.M
  muLo := P.μ
  muHi := 3 * P.μ / 2
  LbarLo_pos := div_pos P.M_pos (by norm_num)
  LbarHi_pos := P.M_pos
  muLo_pos := P.μ_pos
  muHi_pos := by have := P.μ_pos; positivity
  averaged_smooth_upper := P.averaged_smooth
  averaged_smooth_lower := fun L hL h => P.calibration.primal_curvature_lower.trans
    (liftedOracle_averagedSmooth_lower_primal P.chain P.base P.calibration.lift P.p L
      (le_of_lt P.p_pos) P.p_le_one hL h)
  strong_lower := P.actualCertificate.strong_lower
  strong_upper := P.actualCertificate.strong_upper

theorem actual_constants (P : ManuscriptASProblem) :
    (P.M / 4 ≤ actualPopulationSmoothness P.population ∧ actualPopulationSmoothness P.population ≤ P.M / 2) ∧
    (P.μ ≤ actualInnerConcavity P.population ∧ actualInnerConcavity P.population ≤ 3 * P.μ / 2) ∧
    (P.M / 4 ≤ actualAveragedSmoothness (bernoulliLaw P.p) P.oracle ∧
      actualAveragedSmoothness (bernoulliLaw P.p) P.oracle ≤ P.M) :=
  ⟨P.actualCertificate.optimal_bounds.1, P.actualCertificate.optimal_bounds.2, P.actualAveragedCertificate.optimal_bounds⟩

theorem actual_condition_numbers (P : ManuscriptASProblem) :
    ((P.M / P.μ) / 6 ≤ actualPopulationSmoothness P.population / actualInnerConcavity P.population ∧
      actualPopulationSmoothness P.population / actualInnerConcavity P.population ≤ P.M / P.μ) ∧
    ((P.M / P.μ) / 6 ≤ actualAveragedSmoothness (bernoulliLaw P.p) P.oracle / actualInnerConcavity P.population ∧
      actualAveragedSmoothness (bernoulliLaw P.p) P.oracle / actualInnerConcavity P.population ≤ P.M / P.μ) := by
  have h := P.actual_constants
  exact ⟨condition_ratio_of_brackets _ _ _ _ P.M_pos P.μ_pos h.1.1
    (h.1.2.trans (by linarith [P.M_pos])) h.2.1.1 h.2.1.2,
    condition_ratio_of_brackets _ _ _ _ P.M_pos P.μ_pos h.2.2.1 h.2.2.2 h.2.1.1 h.2.1.2⟩

theorem actual_constants_attained (P : ManuscriptASProblem) :
    JointSmooth P.population (actualPopulationSmoothness P.population) ∧
    StronglyConcaveY P.population (actualInnerConcavity P.population) ∧
    OracleAveragedSmooth (bernoulliLaw P.p) P.oracle (actualAveragedSmoothness (bernoulliLaw P.p) P.oracle) :=
  ⟨P.actualCertificate.optimal_attained.1, P.actualCertificate.optimal_attained.2,
    P.actualAveragedCertificate.optimal_attained⟩

/-- Both actual condition numbers belong to the very same AS instance used in the rate bound. -/
theorem fixed_instance_with_actual_conditions (P : ManuscriptASProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
    (((P.M / P.μ) / 6 ≤ actualPopulationSmoothness P.population / actualInnerConcavity P.population ∧
      actualPopulationSmoothness P.population / actualInnerConcavity P.population ≤ P.M / P.μ) ∧
    ((P.M / P.μ) / 6 ≤ actualAveragedSmoothness (bernoulliLaw P.p) P.oracle / actualInnerConcavity P.population ∧
      actualAveragedSmoothness (bernoulliLaw P.p) P.oracle / actualInnerConcavity P.population ≤ P.M / P.μ)) ∧
    InNCSCClass P.population P.M P.μ P.Δ ∧
    OracleUnbiased P.population (bernoulliLaw P.p) P.oracle ∧
    OracleBoundedVariance P.population (bernoulliLaw P.p) P.oracle P.σ ∧
    OracleAveragedSmooth (bernoulliLaw P.p) P.oracle P.M ∧
    ∀ (R K : ℕ) (A : Ω → BernoulliRun P.T R K P.oracle),
      (internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
       internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) →
      (∀ ω w, ValidBatchSizes ((A ω).trace w)) →
      ∀ ω w, manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
        (returnedGradientCount ((A ω).trace w) : ℝ) :=
  ⟨P.actual_condition_numbers, P.fixed_instance_lower_bound ρ⟩

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
