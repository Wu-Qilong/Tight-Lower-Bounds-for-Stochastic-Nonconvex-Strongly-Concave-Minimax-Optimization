import ManuscriptBV
import ManuscriptExactGate

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- Literal manuscript (52), using the actual derivative supremum from Appendix B.3. -/
def manuscriptS : ℝ := max 336 (Real.sqrt (4 * g₀ ^ 2 * paperMGamma ^ 4 + 3 * 155 ^ 2))

theorem manuscriptS_pos : 0 < manuscriptS := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem universalS0_le_manuscriptS : universalS0 paperMGamma ≤ manuscriptS := by
  apply le_trans (Real.sqrt_le_sqrt ?_) (le_max_right _ _)
  norm_num [ℓ₀]

def manuscriptASAccuracyConstant : ℝ := 1 / (65536 * 12 * max 155 manuscriptS)
def manuscriptASNoiseAccuracyConstant : ℝ := g₀ / (4096 * 12 * manuscriptS)
def manuscriptASRateConstant : ℝ := 1 / (32768 * 12 * max 155 manuscriptS * (256 * g₀ ^ 2))

theorem manuscriptAS_constants_pos : 0 < manuscriptASAccuracyConstant ∧
    0 < manuscriptASNoiseAccuracyConstant ∧ 0 < manuscriptASRateConstant := by
  have hs := manuscriptS_pos
  have hm : 0 < max 155 manuscriptS := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  unfold manuscriptASAccuracyConstant manuscriptASNoiseAccuracyConstant manuscriptASRateConstant
  norm_num [g₀]
  exact hs

/-- Only external numerical assumptions; the construction and all certificates are derived. -/
structure ManuscriptASProblem extends ManuscriptBVProblem where
  accuracy_as : ε ^ 2 ≤ manuscriptASAccuracyConstant * M * Δ
  accuracy_noise : ε * σ ≤ manuscriptASNoiseAccuracyConstant * M * Δ * Real.sqrt (M / μ)

theorem manuscriptASAccuracyConstant_le_BV : manuscriptASAccuracyConstant ≤ manuscriptBVAccuracyConstant := by
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [le_max_left (155 : ℝ) manuscriptS]

/-- Construct the parameter block from exactly the two manuscript accuracy restrictions;
the inherited BV accuracy field is a consequence, not an extra assumption. -/
def manuscriptASProblem (M μ Δ σ ε : ℝ) (hM : 0 < M) (hμ : 0 < μ) (hΔ : 0 < Δ)
    (hσ : 0 ≤ σ) (hε : 0 < ε) (hk : 8 ≤ M / μ)
    (h0 : ε ^ 2 ≤ manuscriptASAccuracyConstant * M * Δ)
    (h1 : ε * σ ≤ manuscriptASNoiseAccuracyConstant * M * Δ * Real.sqrt (M / μ)) :
    ManuscriptASProblem where
  M := M
  μ := μ
  Δ := Δ
  σ := σ
  ε := ε
  M_pos := hM
  μ_pos := hμ
  Δ_pos := hΔ
  σ_nonneg := hσ
  ε_pos := hε
  kappa_ge := hk
  accuracy := h0.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right manuscriptASAccuracyConstant_le_BV (le_of_lt hM)) (le_of_lt hΔ))
  accuracy_as := h0
  accuracy_noise := h1

namespace ManuscriptASProblem

def p (P : ManuscriptASProblem) : ℝ := P.toManuscriptBVProblem.p
theorem p_pos (P : ManuscriptASProblem) : 0 < P.p := P.toManuscriptBVProblem.p_pos
theorem p_le_one (P : ManuscriptASProblem) : P.p ≤ 1 := P.toManuscriptBVProblem.p_le_one

def calibration (P : ManuscriptASProblem) : ManuscriptCalibration :=
  manuscriptASCalibration P.M P.μ P.ε P.p manuscriptS P.M_pos P.μ_pos P.ε_pos P.p_pos manuscriptS_pos

theorem q_eq (P : ManuscriptASProblem) : P.calibration.q = P.toManuscriptBVProblem.calibration.q := rfl

theorem sqrt_kappa (P : ManuscriptASProblem) : Real.sqrt (P.M / P.μ) = 2 * P.calibration.gamma := by
  have hs := Real.sq_sqrt (le_of_lt (div_pos P.M_pos P.μ_pos))
  have hg := P.calibration.gamma_sq
  change P.calibration.gamma ^ 2 = P.M / (4 * P.μ) at hg
  have he : P.M / (4 * P.μ) = (P.M / P.μ) / 4 := by ring
  rw [he] at hg
  nlinarith [P.calibration.gamma_pos, Real.sqrt_nonneg (P.M / P.μ)]

theorem q_sqrt_kappa (P : ManuscriptASProblem) :
    P.calibration.q * Real.sqrt (P.M / P.μ) = 16 * P.ε := by
  rw [P.sqrt_kappa]
  have h := P.calibration.gamma_q
  change P.calibration.gamma * P.calibration.q = 8 * P.ε at h
  nlinarith

theorem sqrt_p_sigma (P : ManuscriptASProblem) (hp : P.p < 1) :
    Real.sqrt P.p * P.σ = P.calibration.q * g₀ := by
  have hs : P.σ ≠ 0 := by
    intro hz
    have he : P.p = 1 := by simp [p, ManuscriptBVProblem.p, hz]
    linarith
  have hprob : P.p = P.calibration.q ^ 2 * g₀ ^ 2 / P.σ ^ 2 := by
    change (if P.σ = 0 then 1 else min 1 _) = _
    rw [if_neg hs]
    apply min_eq_right
    have hmin : min 1 (P.calibration.q ^ 2 * g₀ ^ 2 / P.σ ^ 2) < 1 := by
      simpa only [p, ManuscriptBVProblem.p, hs, if_false] using hp
    exact le_of_lt ((min_lt_iff).1 hmin |>.resolve_left (lt_irrefl _))
  have he : P.p * P.σ ^ 2 = P.calibration.q ^ 2 * g₀ ^ 2 := by
    rw [hprob]; exact div_mul_cancel₀ _ (pow_ne_zero _ hs)
  have hroot := Real.sq_sqrt (le_of_lt P.p_pos)
  have hn : 0 ≤ Real.sqrt P.p * P.σ := mul_nonneg (Real.sqrt_nonneg _) P.σ_nonneg
  have hq : 0 < P.calibration.q * g₀ := mul_pos P.calibration.q_pos (by norm_num [g₀])
  nlinarith [sq_nonneg (Real.sqrt P.p * P.σ - P.calibration.q * g₀)]

def scale (P : ManuscriptASProblem) : ℝ := P.Δ * P.calibration.h / (4 * Δ₀ * P.calibration.q ^ 2)
def T (P : ManuscriptASProblem) : ℕ := ⌊P.scale⌋₊

theorem scale_ge_sixteen (P : ManuscriptASProblem) : 16 ≤ P.scale := by
  have hqpos := sq_pos_of_pos P.calibration.q_pos
  have hd : 0 < 4 * Δ₀ * P.calibration.q ^ 2 := by norm_num [Δ₀]; positivity
  apply (le_div_iff₀ hd).2
  change 16 * (4 * Δ₀ * P.calibration.q ^ 2) ≤
    P.Δ * min (P.μ / (4 * 155)) (P.M * Real.sqrt P.p / (4 * manuscriptS))
  rw [mul_min_of_nonneg _ _ (le_of_lt P.Δ_pos)]
  apply le_min
  · have hb := P.toManuscriptBVProblem.scale_ge_sixteen
    have hid : P.toManuscriptBVProblem.scale =
        P.Δ * (P.μ / (4 * 155)) / (4 * Δ₀ * P.calibration.q ^ 2) := by
      rw [P.calibration.q_sq]
      change P.M * P.Δ / (4096 * 12 * 155 * P.ε ^ 2) = _
      change P.M * P.Δ / (4096 * 12 * 155 * P.ε ^ 2) =
        P.Δ * (P.μ / (4 * 155)) / (4 * Δ₀ * (256 * P.ε ^ 2 / (P.M / P.μ)))
      norm_num [Δ₀]
      field_simp [ne_of_gt P.M_pos, ne_of_gt P.μ_pos, ne_of_gt P.ε_pos]
      <;> ring_nf
      <;> field_simp [ne_of_gt P.μ_pos, ne_of_gt P.ε_pos]
      <;> ring
    rw [hid] at hb
    exact (le_div_iff₀ hd).1 hb
  · by_cases hp : P.p = 1
    · rw [hp, Real.sqrt_one]
      have ha := P.accuracy_as
      have hmax : 0 < max 155 manuscriptS := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have ha' : 65536 * 12 * max 155 manuscriptS * P.ε ^ 2 ≤ P.M * P.Δ := by
        have he : manuscriptASAccuracyConstant * P.M * P.Δ =
            P.M * P.Δ / (65536 * 12 * max 155 manuscriptS) := by unfold manuscriptASAccuracyConstant; ring
        rw [he] at ha
        have hh := (le_div_iff₀ (by positivity : 0 < 65536 * 12 * max 155 manuscriptS)).1 ha
        nlinarith [hh]
      have hsmall : 65536 * 12 * manuscriptS * P.ε ^ 2 ≤ P.M * P.Δ := by
        have hm := mul_le_mul_of_nonneg_right (le_max_right 155 manuscriptS) (sq_nonneg P.ε)
        nlinarith
      rw [P.calibration.q_sq]
      change 16 * (4 * Δ₀ * (256 * P.ε ^ 2 / (P.M / P.μ))) ≤ _
      have hk := P.kappa_ge
      have hkpos := div_pos P.M_pos P.μ_pos
      simp only [mul_one, ← mul_div_assoc]
      apply (div_le_div_iff₀ hkpos (mul_pos (by norm_num) manuscriptS_pos)).2
      norm_num [Δ₀] at *
      nlinarith [mul_nonneg (le_of_lt manuscriptS_pos) (sq_nonneg P.ε),
        mul_nonneg (sub_nonneg.mpr hk) (le_of_lt (mul_pos P.M_pos P.Δ_pos))]
    · have hps := P.sqrt_p_sigma (lt_of_le_of_ne P.p_le_one hp)
      have hs : 0 < P.σ := by
        have := P.calibration.q_pos
        have := Real.sqrt_nonneg P.p
        norm_num [g₀] at hps
        nlinarith [P.σ_nonneg]
      have ha := P.accuracy_noise
      have he : manuscriptASNoiseAccuracyConstant * P.M * P.Δ * Real.sqrt (P.M / P.μ) =
          g₀ * P.M * P.Δ * Real.sqrt (P.M / P.μ) / (4096 * 12 * manuscriptS) := by
        unfold manuscriptASNoiseAccuracyConstant; ring
      rw [he] at ha
      have ha' := (le_div_iff₀ (mul_pos (by norm_num) manuscriptS_pos)).1 ha
      have hm := mul_le_mul_of_nonneg_right ha' (le_of_lt P.calibration.q_pos)
      have hqs := P.q_sqrt_kappa
      have haux : 4096 * 12 * manuscriptS * P.calibration.q * P.σ ≤ 16 * g₀ * P.M * P.Δ := by
        have hre : (g₀ * P.M * P.Δ * Real.sqrt (P.M / P.μ)) * P.calibration.q =
            16 * g₀ * P.M * P.Δ * P.ε := by
          calc
            _ = g₀ * P.M * P.Δ * (P.calibration.q * Real.sqrt (P.M / P.μ)) := by ring
            _ = _ := by rw [hqs]; ring
        rw [hre] at hm
        nlinarith [P.ε_pos]
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (mul_pos (by norm_num) manuscriptS_pos)).2
      have hh := mul_le_mul_of_nonneg_right haux (le_of_lt P.calibration.q_pos)
      apply (mul_le_mul_right hs).1
      have hre : 16 * g₀ * P.M * P.Δ * P.calibration.q =
          16 * P.Δ * P.M * Real.sqrt P.p * P.σ := by
        calc
          _ = 16 * P.Δ * P.M * (P.calibration.q * g₀) := by ring
          _ = _ := by rw [← hps]; ring
      rw [hre] at hh
      norm_num [Δ₀] at *
      nlinarith only [hh]

theorem floor_interval (P : ManuscriptASProblem) : (P.T : ℝ) ≤ P.scale ∧ P.scale < (P.T : ℝ) + 1 :=
  ⟨Nat.floor_le (by linarith [P.scale_ge_sixteen]), Nat.lt_floor_add_one _⟩
theorem T_ge_eight (P : ManuscriptASProblem) : 8 ≤ P.T :=
  floor_interval_ge_eight P.floor_interval P.scale_ge_sixteen
theorem scale_half_le_T (P : ManuscriptASProblem) : P.scale / 2 ≤ (P.T : ℝ) :=
  floor_interval_ge_half P.floor_interval (by linarith [P.scale_ge_sixteen])

def chain (P : ManuscriptASProblem) : ExplicitZeroChainCertificate P.T :=
  Classical.choice (importedLemma21Certificate P.T (by have := P.T_ge_eight; omega))
def base (P : ManuscriptASProblem) : BaseOracle P.T := manuscriptASBase P.chain P.p
def population (P : ManuscriptASProblem) : PopulationObjective P.T :=
  P.calibration.population P.chain P.base
def oracle (P : ManuscriptASProblem) : StochasticOracle P.T Bool := liftedOracle P.base P.calibration.lift

theorem chain_gap (P : ManuscriptASProblem) : P.calibration.lift.α * Δ₀ * P.T ≤ P.Δ / 4 := by
  have hm := mul_le_mul_of_nonneg_left P.floor_interval.1
    (mul_nonneg (lift_alpha_nonneg P.calibration.lift) (show 0 ≤ Δ₀ by norm_num [Δ₀]))
  have he : P.calibration.lift.α * Δ₀ * P.scale = P.Δ / 4 := by
    change (P.calibration.q ^ 2 / P.calibration.h) * Δ₀ *
      (P.Δ * P.calibration.h / (4 * Δ₀ * P.calibration.q ^ 2)) = _
    field_simp [ne_of_gt P.calibration.h_pos, ne_of_gt P.calibration.q_pos, Δ₀]
    <;> ring
  rw [he] at hm
  exact hm

theorem in_class (P : ManuscriptASProblem) : InNCSCClass P.population P.M P.μ P.Δ := by
  apply P.calibration.in_class P.chain P.base P.Δ P.kappa_ge
  change P.calibration.lift.α * Δ₀ * P.T + P.calibration.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ P.Δ
  have hg := P.toManuscriptBVProblem.origin_gap
  rw [← P.q_eq] at hg
  linarith [P.chain_gap, P.Δ_pos]

theorem unbiased (P : ManuscriptASProblem) : OracleUnbiased P.population (bernoulliLaw P.p) P.oracle := by
  apply liftedOracle_unbiased P.chain P.base P.calibration.lift
    (canonicalLiftPropertiesCertificate P.chain P.base P.calibration.lift) P.p
  intro u
  exact asBaseOracle_unbiased P.chain P.p (ne_of_gt P.p_pos) u

theorem variance (P : ManuscriptASProblem) :
    OracleBoundedVariance P.population (bernoulliLaw P.p) P.oracle P.σ := by
  apply liftedOracle_boundedVariance_of_base P.chain P.base P.calibration.lift
    (canonicalLiftPropertiesCertificate P.chain P.base P.calibration.lift) P.p g₀ P.σ
  · intro u; exact asBaseOracle_variance P.chain paperSmoothGateCertificate P.p P.p_pos P.p_le_one u
  · exact P.toManuscriptBVProblem.noise_budget

theorem base_averaged_smooth (P : ManuscriptASProblem) : BaseAveragedSmoothHypothesis P.base P.p manuscriptS := by
  intro u v
  have h := (lemma41_full_certificate P.chain paperSmoothGateCertificate P.p P.p_pos P.p_le_one).averaged_smooth u v
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u - v‖)
  apply div_le_div_of_nonneg_right _ (le_of_lt P.p_pos)
  have hs := universalS0_le_manuscriptS
  have hn := le_of_lt (universalS0_pos paperMGamma)
  nlinarith [manuscriptS_pos]

theorem averaged_root_budget (P : ManuscriptASProblem) :
    P.calibration.lift.ν * (1 + P.calibration.lift.γ ^ 2) +
      P.calibration.h * manuscriptS / Real.sqrt P.p ≤ P.M := by
  have hb := P.calibration.smooth_budget P.kappa_ge
  have hh : P.calibration.h ≤ P.M * Real.sqrt P.p / (4 * manuscriptS) := min_le_right _ _
  have hh' := (le_div_iff₀ (mul_pos (by norm_num) manuscriptS_pos)).1 hh
  have hnoise : P.calibration.h * manuscriptS / Real.sqrt P.p ≤ P.M / 4 := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 P.p_pos)).2
    nlinarith
  have hn : 0 ≤ ℓ₀ * P.calibration.lift.h := mul_nonneg (by norm_num [ℓ₀]) (le_of_lt P.calibration.h_pos)
  change P.calibration.lift.ν * (1 + P.calibration.lift.γ ^ 2) + ℓ₀ * P.calibration.lift.h ≤ P.M / 2 at hb
  linarith [P.M_pos]

theorem averaged_smooth (P : ManuscriptASProblem) :
    OracleAveragedSmooth (bernoulliLaw P.p) P.oracle P.M := by
  intro x y x' y'
  have ht := lifted_averaged_smooth_transfer P.base P.calibration.lift P.p manuscriptS
    P.p_pos P.p_le_one (le_of_lt manuscriptS_pos) P.base_averaged_smooth x y x' y'
  have hb := P.averaged_root_budget
  have hn : 0 ≤ P.calibration.lift.ν * (1 + P.calibration.lift.γ ^ 2) +
      P.calibration.h * manuscriptS / Real.sqrt P.p := by
    have := lift_nu_pos P.calibration.lift
    have := P.calibration.h_pos
    have := manuscriptS_pos
    positivity
  have hsq : (P.calibration.lift.ν * (1 + P.calibration.lift.γ ^ 2) +
      P.calibration.h * manuscriptS / Real.sqrt P.p) ^ 2 ≤ P.M ^ 2 := by nlinarith [P.M_pos]
  exact ht.trans (mul_le_mul_of_nonneg_right hsq (by positivity))

theorem moments (P : ManuscriptASProblem) {R K : ℕ} (A : BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    5 * P.ε ≤ stationarityNormRisk P.p P.population.gradPhi A ∧
      (100 / 3 : ℝ) * P.ε ^ 2 ≤ stationarityRisk P.p P.population.gradPhi A :=
  P.calibration.as_moments P.chain P.p P.p_pos P.p_le_one paperSmoothGateCertificate P.T_ge_eight A hR

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
