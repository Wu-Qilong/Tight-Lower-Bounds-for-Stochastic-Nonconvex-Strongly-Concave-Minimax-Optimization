import ManuscriptInstances

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

def manuscriptBVAccuracyConstant : ℝ := 1 / (65536 * 12 * 155)
def manuscriptBVRateConstant : ℝ := 1 / (32768 * 12 * 155 * (256 * 23 ^ 2))

/-- External assumptions of Theorem 4.1 with an explicit admissible universal constant. -/
structure ManuscriptBVProblem where
  M : ℝ
  μ : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ
  M_pos : 0 < M
  μ_pos : 0 < μ
  Δ_pos : 0 < Δ
  σ_nonneg : 0 ≤ σ
  ε_pos : 0 < ε
  kappa_ge : 8 ≤ M / μ
  accuracy : ε ^ 2 ≤ manuscriptBVAccuracyConstant * M * Δ

namespace ManuscriptBVProblem

def calibration (P : ManuscriptBVProblem) : ManuscriptCalibration :=
  manuscriptBVCalibration P.M P.μ P.ε P.M_pos P.μ_pos P.ε_pos

def p (P : ManuscriptBVProblem) : ℝ :=
  if P.σ = 0 then 1 else min 1 (P.calibration.q ^ 2 * g₀ ^ 2 / P.σ ^ 2)

theorem p_pos (P : ManuscriptBVProblem) : 0 < P.p := by
  unfold p
  split
  · norm_num
  · rename_i hs
    exact lt_min (by norm_num)
      (div_pos (mul_pos (sq_pos_of_pos P.calibration.q_pos) (by norm_num [g₀]))
        (sq_pos_of_ne_zero hs))

theorem p_le_one (P : ManuscriptBVProblem) : P.p ≤ 1 := by
  unfold p
  split
  · exact le_rfl
  · exact min_le_left _ _

theorem noise_budget (P : ManuscriptBVProblem) :
    P.calibration.q ^ 2 * g₀ ^ 2 * (1 - P.p) / P.p ≤ P.σ ^ 2 := by
  by_cases hs : P.σ = 0
  · simp [p, hs]
  · let a := P.calibration.q ^ 2 * g₀ ^ 2
    have ha : 0 < a := mul_pos (sq_pos_of_pos P.calibration.q_pos) (by norm_num [g₀])
    change a * (1 - P.p) / P.p ≤ _
    by_cases h : 1 ≤ a / P.σ ^ 2
    · have hp : P.p = 1 := by simp only [p, hs, if_false]; exact min_eq_left h
      rw [hp]; simpa using sq_nonneg P.σ
    · have hp : P.p = a / P.σ ^ 2 := by
        simp only [p, hs, if_false]; exact min_eq_right (le_of_not_ge h)
      rw [hp]
      have he : a * (1 - a / P.σ ^ 2) / (a / P.σ ^ 2) = P.σ ^ 2 - a := by
        field_simp [ne_of_gt ha, hs]
      rw [he]
      exact sub_le_self _ (le_of_lt ha)

def scale (P : ManuscriptBVProblem) : ℝ := P.M * P.Δ / (4096 * 12 * 155 * P.ε ^ 2)
def T (P : ManuscriptBVProblem) : ℕ := ⌊P.scale⌋₊

theorem scale_ge_sixteen (P : ManuscriptBVProblem) : 16 ≤ P.scale := by
  have h := P.accuracy
  norm_num [manuscriptBVAccuracyConstant] at h
  unfold scale
  apply (le_div_iff₀ (by have := P.ε_pos; positivity)).2
  nlinarith

theorem floor_interval (P : ManuscriptBVProblem) :
    (P.T : ℝ) ≤ P.scale ∧ P.scale < (P.T : ℝ) + 1 := by
  exact ⟨Nat.floor_le (by linarith [P.scale_ge_sixteen]), Nat.lt_floor_add_one _⟩

theorem T_ge_eight (P : ManuscriptBVProblem) : 8 ≤ P.T :=
  floor_interval_ge_eight P.floor_interval P.scale_ge_sixteen

theorem scale_half_le_T (P : ManuscriptBVProblem) : P.scale / 2 ≤ (P.T : ℝ) :=
  floor_interval_ge_half P.floor_interval (by linarith [P.scale_ge_sixteen])

theorem chain_gap (P : ManuscriptBVProblem) :
    P.calibration.lift.α * Δ₀ * P.T ≤ P.Δ / 4 := by
  have hα : 0 ≤ P.calibration.lift.α := lift_alpha_nonneg _
  have hm := mul_le_mul_of_nonneg_left P.floor_interval.1
    (mul_nonneg hα (show 0 ≤ Δ₀ by norm_num [Δ₀]))
  have he : P.calibration.lift.α * Δ₀ * P.scale = P.Δ / 4 := by
    change (P.calibration.q ^ 2 / (P.μ / (4 * 155))) * Δ₀ * P.scale = _
    rw [P.calibration.q_sq]
    change (256 * P.ε ^ 2 / (P.M / P.μ) / (P.μ / (4 * 155))) * Δ₀ * P.scale = _
    unfold scale
    norm_num [Δ₀]
    field_simp [ne_of_gt P.M_pos, ne_of_gt P.μ_pos, ne_of_gt P.ε_pos]
    <;> ring
  rw [he] at hm
  exact hm

theorem origin_gap (P : ManuscriptBVProblem) :
    P.calibration.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ / 2 := by
  have he : P.calibration.q ^ 2 * g₀ ^ 2 / (2 * P.μ) = 128 * g₀ ^ 2 * P.ε ^ 2 / P.M := by
    rw [P.calibration.q_sq]
    change (256 * P.ε ^ 2 / (P.M / P.μ)) * g₀ ^ 2 / (2 * P.μ) = _
    field_simp [ne_of_gt P.M_pos, ne_of_gt P.μ_pos]
    <;> ring
  rw [he]
  apply (div_le_iff₀ P.M_pos).2
  have h := P.accuracy
  norm_num [manuscriptBVAccuracyConstant, g₀] at h ⊢
  nlinarith [sq_nonneg P.ε]

def chain (P : ManuscriptBVProblem) : ExplicitZeroChainCertificate P.T :=
  Classical.choice (importedLemma21Certificate P.T (by have := P.T_ge_eight; omega))

def base (P : ManuscriptBVProblem) : BaseOracle P.T := manuscriptBVBase P.chain P.p
def population (P : ManuscriptBVProblem) : PopulationObjective P.T :=
  P.calibration.population P.chain P.base
def oracle (P : ManuscriptBVProblem) : StochasticOracle P.T Bool := liftedOracle P.base P.calibration.lift

theorem in_class (P : ManuscriptBVProblem) : InNCSCClass P.population P.M P.μ P.Δ := by
  apply P.calibration.in_class P.chain P.base P.Δ P.kappa_ge
  change P.calibration.lift.α * Δ₀ * P.T + P.calibration.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ _
  linarith [P.chain_gap, P.origin_gap, P.Δ_pos]

theorem unbiased (P : ManuscriptBVProblem) : OracleUnbiased P.population (bernoulliLaw P.p) P.oracle := by
  apply liftedOracle_unbiased P.chain P.base P.calibration.lift
    (canonicalLiftPropertiesCertificate P.chain P.base P.calibration.lift) P.p
  intro u
  exact bvBaseOracle_unbiased P.chain P.p (ne_of_gt P.p_pos) u

theorem variance (P : ManuscriptBVProblem) :
    OracleBoundedVariance P.population (bernoulliLaw P.p) P.oracle P.σ := by
  apply liftedOracle_boundedVariance_of_base P.chain P.base P.calibration.lift
    (canonicalLiftPropertiesCertificate P.chain P.base P.calibration.lift) P.p g₀ P.σ
  · intro u; exact bvBaseOracle_variance P.chain P.p P.p_pos P.p_le_one u
  · exact P.noise_budget

/-- Both moment bounds now use the concrete new-calibration instance and its constructed support proof. -/
theorem moments (P : ManuscriptBVProblem) {R K : ℕ}
    (A : BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    5 * P.ε ≤ stationarityNormRisk P.p P.population.gradPhi A ∧
      (100 / 3 : ℝ) * P.ε ^ 2 ≤ stationarityRisk P.p P.population.gradPhi A :=
  P.calibration.bv_moments P.chain P.p P.p_pos P.p_le_one P.T_ge_eight A hR

theorem inverse_probability_factor (P : ManuscriptBVProblem) :
    (1 / (256 * g₀ ^ 2)) * max 1 ((P.M / P.μ) * P.σ ^ 2 / P.ε ^ 2) ≤ 1 / P.p := by
  have hnoise : P.p * P.σ ^ 2 ≤ P.calibration.q ^ 2 * g₀ ^ 2 := by
    by_cases hs : P.σ = 0
    · rw [hs]; have := sq_nonneg P.calibration.q
      norm_num [g₀] at *; positivity
    · have hp : P.p ≤ P.calibration.q ^ 2 * g₀ ^ 2 / P.σ ^ 2 := by
        simp only [p, hs, if_false]; exact min_le_right _ _
      exact (le_div_iff₀ (sq_pos_of_ne_zero hs)).1 hp
  have hq : P.calibration.q ^ 2 * (P.M / P.μ) = 256 * P.ε ^ 2 := by
    rw [P.calibration.q_sq]
    change (256 * P.ε ^ 2 / (P.M / P.μ)) * (P.M / P.μ) = _
    exact div_mul_cancel₀ _ (ne_of_gt (div_pos P.M_pos P.μ_pos))
  have hx : P.p * ((P.M / P.μ) * P.σ ^ 2 / P.ε ^ 2) ≤ 256 * g₀ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hnoise (le_of_lt (div_pos P.M_pos P.μ_pos))
    calc
      _ = (P.p * P.σ ^ 2 * (P.M / P.μ)) / P.ε ^ 2 := by ring
      _ ≤ (P.calibration.q ^ 2 * (P.M / P.μ) * g₀ ^ 2) / P.ε ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg P.ε)
        nlinarith [hm]
      _ = 256 * g₀ ^ 2 := by
        rw [hq]
        field_simp [ne_of_gt P.ε_pos]
        <;> ring
  have hm : P.p * max 1 ((P.M / P.μ) * P.σ ^ 2 / P.ε ^ 2) ≤ 256 * g₀ ^ 2 := by
    rw [mul_max_of_nonneg _ _ (le_of_lt P.p_pos)]
    apply max_le
    · have := P.p_le_one; norm_num [g₀] at *; linarith
    · exact hx
  apply (le_div_iff₀ P.p_pos).2
  norm_num [g₀] at hm ⊢
  nlinarith

/-- The explicit manuscript rate is bounded by the support-propagation threshold. -/
theorem rate_threshold (P : ManuscriptBVProblem) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ ≤
      (P.T : ℝ) / (4 * P.p) := by
  have hm := mul_le_mul_of_nonneg_left P.inverse_probability_factor
    (show 0 ≤ P.scale / 8 by linarith [P.scale_ge_sixteen])
  calc
    _ = (P.scale / 8) * ((1 / (256 * g₀ ^ 2)) *
        max 1 ((P.M / P.μ) * P.σ ^ 2 / P.ε ^ 2)) := by
      unfold manuscriptBVRateConstant bvRate scale
      norm_num [g₀]; ring
    _ ≤ (P.scale / 8) * (1 / P.p) := hm
    _ = (P.scale / 2) / (4 * P.p) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right P.scale_half_le_T (by linarith [P.p_pos])

universe u

/-- The instance is fixed before the independent internal seed and the algorithm. -/
theorem randomized_moments (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal (5 * P.ε) ≤ internalRandomNormRisk ρ P.p P.population.gradPhi A ∧
      ENNReal.ofReal ((100 / 3 : ℝ) * P.ε ^ 2) ≤
        internalRandomStationarityRisk ρ P.p P.population.gradPhi A := by
  exact ⟨internalRandomNormRisk_lower ρ P.p _ A _ (fun ω => (P.moments (A ω) hR).1),
    internalRandomStationarityRisk_lower ρ P.p _ A _ (fun ω => (P.moments (A ω) hR).2)⟩

/-- Either stationarity success criterion forces more rounds than the hard threshold. -/
theorem randomized_round_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) :
    (P.T : ℝ) / (4 * P.p) < (R : ℝ) := by
  by_contra hn
  have hm := P.randomized_moments ρ A (le_of_not_gt hn)
  rcases hsuccess with h | h
  · have hs : ENNReal.ofReal P.ε < ENNReal.ofReal (5 * P.ε) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith [P.ε_pos])).2 (by linarith [P.ε_pos])
    exact (not_lt_of_ge (hm.1.trans h)) hs
  · have hs : ENNReal.ofReal (P.ε ^ 2) < ENNReal.ofReal ((100 / 3 : ℝ) * P.ε ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) (sq_pos_of_pos P.ε_pos))).2
        (by nlinarith [sq_pos_of_pos P.ε_pos])
    exact (not_lt_of_ge (hm.2.trans h)) hs

theorem randomized_rate_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (R : ℝ) :=
  P.rate_threshold.trans_lt (P.randomized_round_lower ρ A hsuccess)

theorem randomized_gradient_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2))
    (hbatch : ∀ ω w, ValidBatchSizes ((A ω).trace w)) :
    ∀ ω w, manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
      (returnedGradientCount ((A ω).trace w) : ℝ) := by
  intro ω w
  have hc := (gradientCountAccounting P.T R K ((A ω).trace w) (hbatch ω w)).1
  have hcast : (R : ℝ) ≤ (returnedGradientCount ((A ω).trace w) : ℝ) := by exact_mod_cast hc
  exact (P.randomized_rate_lower ρ A hsuccess).trans_le hcast

/-- Paper-facing fixed-instance BV conclusion, for the formal bounded-round trace model.
The population and oracle depend only on the problem parameters, not on the algorithm.
This does not yet implement the separate early-stopping reduction or a minimax infimum. -/
theorem fixed_instance_lower_bound (P : ManuscriptBVProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
    InNCSCClass P.population P.M P.μ P.Δ ∧
    OracleUnbiased P.population (bernoulliLaw P.p) P.oracle ∧
    OracleBoundedVariance P.population (bernoulliLaw P.p) P.oracle P.σ ∧
    ∀ (R K : ℕ) (A : Ω → BernoulliRun P.T R K P.oracle),
      (internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
       internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) →
      (∀ ω w, ValidBatchSizes ((A ω).trace w)) →
      ∀ ω w, manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
        (returnedGradientCount ((A ω).trace w) : ℝ) :=
  ⟨P.in_class, P.unbiased, P.variance, fun _ _ A hs hb => P.randomized_gradient_lower ρ A hs hb⟩

end ManuscriptBVProblem
end NCSCPureStochasticLB.PaperExact
