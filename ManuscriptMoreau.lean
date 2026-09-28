import ManuscriptConditionNumbers

noncomputable section
open scoped NNReal
namespace NCSCPureStochasticLB.PaperExact

/-- Analytic data proved below for the calibrated hard family. No proximal oracle is assumed. -/
structure CalibratedPrimal (T : ℕ) where
  F : Vec T → ℝ
  g : Vec T → Vec T
  M : ℝ
  M_pos : 0 < M
  grad_spec : ∀ x, HasGradientAt F (g x) x
  grad_lip : ∀ x y, ‖g x - g y‖ ≤ (5 * M / 64) * ‖x - y‖
  lower_model : ∀ u v, F u + @inner ℝ (Vec T) _ (g u) (v - u) -
    (M / 2) * ‖v - u‖ ^ 2 ≤ F v

namespace CalibratedPrimal

variable {T : ℕ}

def proxStep (P : CalibratedPrimal T) (x u : Vec T) : Vec T := x - (1 / (2 * P.M)) • P.g u

theorem proxStep_contracting (P : CalibratedPrimal T) (x : Vec T) :
    ContractingWith (5 / 128 : ℝ≥0) (P.proxStep x) := by
  constructor
  · exact_mod_cast (show (5 / 128 : ℝ) < 1 by norm_num)
  · rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    rw [dist_eq_norm, dist_eq_norm]
    have he : P.proxStep x u - P.proxStep x v = -(1 / (2 * P.M)) • (P.g u - P.g v) := by
      unfold proxStep; module
    have hc : 0 < (1 : ℝ) / (2 * P.M) := by have := P.M_pos; positivity
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hc]
    calc
      _ ≤ (1 / (2 * P.M)) * ((5 * P.M / 64) * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (P.grad_lip u v) (le_of_lt hc)
      _ = _ := by norm_num; field_simp [ne_of_gt P.M_pos]; ring

def prox (P : CalibratedPrimal T) (x : Vec T) : Vec T :=
  (P.proxStep_contracting x).fixedPoint (P.proxStep x)

theorem prox_first_order (P : CalibratedPrimal T) (x : Vec T) :
    P.g (P.prox x) = (2 * P.M) • (x - P.prox x) := by
  have hf : x - (1 / (2 * P.M)) • P.g (P.prox x) = P.prox x :=
    (P.proxStep_contracting x).fixedPoint_isFixedPt
  have hv : x - P.prox x = (1 / (2 * P.M)) • P.g (P.prox x) := by
    calc
      _ = x - (x - (1 / (2 * P.M)) • P.g (P.prox x)) := by rw [hf]
      _ = _ := by module
  rw [hv, smul_smul]
  have hc : (2 * P.M) * (1 / (2 * P.M)) = 1 := by field_simp [ne_of_gt P.M_pos]
  rw [hc, one_smul]

theorem prox_lipschitz (P : CalibratedPrimal T) (x y : Vec T) : ‖P.prox x - P.prox y‖ ≤ 2 * ‖x - y‖ := by
  have hh : ∀ z, dist (P.proxStep x z) (P.proxStep y z) ≤ ‖x - y‖ := by
    intro z
    rw [dist_eq_norm]
    have he : P.proxStep x z - P.proxStep y z = x - y := by unfold proxStep; module
    rw [he]
  have h := (P.proxStep_contracting x).fixedPoint_lipschitz_in_map (P.proxStep_contracting y) hh
  change dist (P.prox x) (P.prox y) ≤ ‖x - y‖ / (1 - ((5 / 128 : ℝ≥0) : ℝ)) at h
  rw [dist_eq_norm] at h
  norm_num at h
  linarith [norm_nonneg (x - y)]

def cost (P : CalibratedPrimal T) (x u : Vec T) : ℝ := P.F u + P.M * ‖u - x‖ ^ 2
def envelope (P : CalibratedPrimal T) (x : Vec T) : ℝ := P.cost x (P.prox x)
def envelopeGrad (P : CalibratedPrimal T) (x : Vec T) : Vec T := (2 * P.M) • (x - P.prox x)

theorem envelopeGrad_eq (P : CalibratedPrimal T) (x : Vec T) : P.envelopeGrad x = P.g (P.prox x) :=
  (P.prox_first_order x).symm

/-- Quadratic growth proves global minimality and uniqueness of the analytically constructed prox. -/
theorem prox_quadratic_growth (P : CalibratedPrimal T) (x u : Vec T) :
    P.envelope x + (P.M / 2) * ‖u - P.prox x‖ ^ 2 ≤ P.cost x u := by
  have hl := P.lower_model (P.prox x) u
  have hv : u - x = (P.prox x - x) + (u - P.prox x) := by module
  have hn : ‖u - x‖ ^ 2 = ‖P.prox x - x‖ ^ 2 +
      2 * @inner ℝ (Vec T) _ (P.prox x - x) (u - P.prox x) + ‖u - P.prox x‖ ^ 2 := by
    rw [hv, norm_add_sq_real]
  have hi : @inner ℝ (Vec T) _ (P.g (P.prox x)) (u - P.prox x) =
      -(2 * P.M) * @inner ℝ (Vec T) _ (P.prox x - x) (u - P.prox x) := by
    rw [P.prox_first_order, real_inner_smul_left]
    have he : x - P.prox x = -(P.prox x - x) := by module
    rw [he, inner_neg_left]; ring
  rw [hi] at hl
  unfold envelope cost
  rw [hn]
  nlinarith

theorem prox_minimizes (P : CalibratedPrimal T) (x u : Vec T) : P.envelope x ≤ P.cost x u := by
  have h := P.prox_quadratic_growth x u
  have hn : 0 ≤ (P.M / 2) * ‖u - P.prox x‖ ^ 2 := by have := P.M_pos; positivity
  linarith

theorem prox_unique (P : CalibratedPrimal T) (x u : Vec T)
    (hu : ∀ v, P.cost x u ≤ P.cost x v) : u = P.prox x := by
  have h := P.prox_quadratic_growth x u
  have hm := hu (P.prox x)
  change P.cost x (P.prox x) + (P.M / 2) * ‖u - P.prox x‖ ^ 2 ≤ P.cost x u at h
  have hs : ‖u - P.prox x‖ ^ 2 = 0 := by nlinarith [P.M_pos, sq_nonneg ‖u - P.prox x‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

theorem existsUnique_minimizer (P : CalibratedPrimal T) (x : Vec T) :
    ∃! u, ∀ v, P.cost x u ≤ P.cost x v :=
  ⟨P.prox x, P.prox_minimizes x, fun u hu => P.prox_unique x u hu⟩

theorem envelope_eq_inf (P : CalibratedPrimal T) (x : Vec T) : P.envelope x = sInf (Set.range (P.cost x)) := by
  have hb : BddBelow (Set.range (P.cost x)) := ⟨P.envelope x, by rintro _ ⟨u, rfl⟩; exact P.prox_minimizes x u⟩
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨u, rfl⟩
    exact P.prox_minimizes x u
  · exact csInf_le hb ⟨P.prox x, rfl⟩

theorem cost_increment (P : CalibratedPrimal T) (x y u : Vec T) :
    P.cost y u - P.cost x u =
      @inner ℝ (Vec T) _ ((2 * P.M) • (x - u)) (y - x) + P.M * ‖y - x‖ ^ 2 := by
  have hv : y - u = (x - u) + (y - x) := by module
  have hn : ‖y - u‖ ^ 2 = ‖x - u‖ ^ 2 + 2 * @inner ℝ (Vec T) _ (x - u) (y - x) + ‖y - x‖ ^ 2 := by
    rw [hv, norm_add_sq_real]
  unfold cost
  rw [norm_sub_rev u y, norm_sub_rev u x, hn, real_inner_smul_left]
  ring

theorem envelope_remainder (P : CalibratedPrimal T) (x y : Vec T) :
    ‖P.envelope y - P.envelope x - @inner ℝ (Vec T) _ (P.envelopeGrad x) (y - x)‖ ≤
      (4 * P.M) * ‖y - x‖ ^ 2 := by
  have hup := P.prox_minimizes y (P.prox x)
  have hlo := P.prox_minimizes x (P.prox y)
  have hinc := P.cost_increment x y (P.prox x)
  have hinc' := P.cost_increment x y (P.prox y)
  have hi : @inner ℝ (Vec T) _ (P.envelopeGrad x) (y - x) -
      @inner ℝ (Vec T) _ ((2 * P.M) • (x - P.prox y)) (y - x) =
      @inner ℝ (Vec T) _ ((2 * P.M) • (P.prox y - P.prox x)) (y - x) := by
    rw [← inner_sub_left]
    congr 1
    unfold envelopeGrad
    module
  have hb : @inner ℝ (Vec T) _ ((2 * P.M) • (P.prox y - P.prox x)) (y - x) ≤
      4 * P.M * ‖y - x‖ ^ 2 := by
    have hh := real_inner_le_norm ((2 * P.M) • (P.prox y - P.prox x)) (y - x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by have := P.M_pos; positivity)] at hh
    have hm := mul_le_mul_of_nonneg_left (P.prox_lipschitz y x) (show 0 ≤ 2 * P.M by have := P.M_pos; positivity)
    have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (y - x))
    nlinarith [hh]
  change P.envelope y ≤ P.cost y (P.prox x) at hup
  change P.envelope x ≤ P.cost x (P.prox y) at hlo
  change P.cost y (P.prox x) - P.envelope x = _ at hinc
  change P.envelope y - P.cost x (P.prox y) = _ at hinc'
  change P.cost y (P.prox x) - P.envelope x =
    @inner ℝ (Vec T) _ (P.envelopeGrad x) (y - x) + P.M * ‖y - x‖ ^ 2 at hinc
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hn : 0 ≤ P.M * ‖y - x‖ ^ 2 := mul_nonneg (le_of_lt P.M_pos) (sq_nonneg _)
  constructor <;> nlinarith

theorem envelope_hasGradient (P : CalibratedPrimal T) (x : Vec T) :
    HasGradientAt P.envelope (P.envelopeGrad x) x := by
  rw [hasGradientAt_iff_tendsto]
  have ht : Filter.Tendsto (fun y : Vec T => ‖y - x‖) (nhds x) (nhds 0) := by
    have hc : ContinuousAt (fun y : Vec T => ‖y - x‖) x := (continuousAt_id.sub continuousAt_const).norm
    simpa only [ContinuousAt, sub_self, norm_zero] using hc
  have hKt : Filter.Tendsto (fun y : Vec T => (4 * P.M) * ‖y - x‖) (nhds x) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ht)
  apply squeeze_zero
  · intro y; exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · intro y
    have hr := P.envelope_remainder x y
    change ‖y - x‖⁻¹ * ‖P.envelope y - P.envelope x -
      @inner ℝ (Vec T) _ (P.envelopeGrad x) (y - x)‖ ≤ (4 * P.M) * ‖y - x‖
    by_cases hd : ‖y - x‖ = 0
    · simp [hd]
    · have hm := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg (y - x)))
      calc
        _ ≤ ‖y - x‖⁻¹ * ((4 * P.M) * ‖y - x‖ ^ 2) := hm
        _ = (4 * P.M) * ‖y - x‖ := by field_simp [hd]; ring
  · exact hKt

theorem same_output_transfer (P : CalibratedPrimal T) (x : Vec T) :
    ‖P.g x‖ ≤ (133 / 128 : ℝ) * ‖P.envelopeGrad x‖ := by
  rw [P.envelopeGrad_eq]
  exact same_output_envelope_transfer P.g P.M P.M_pos P.grad_lip x (P.prox x) (P.prox_first_order x)

end CalibratedPrimal

namespace ManuscriptCalibration

/-- The extra analytic inputs above are proved from the existing lift, not postulated. -/
def primal {T : ℕ} (P : ManuscriptCalibration) (C : ExplicitZeroChainCertificate T) : CalibratedPrimal T where
  F := canonicalLiftPhi C P.lift
  g := canonicalLiftGradPhi C P.lift
  M := P.M
  M_pos := P.M_pos
  grad_spec := canonicalLiftPhi_grad C P.lift
  grad_lip := P.primal_lipschitz C
  lower_model := by
    intro u v
    have h := canonicalLiftPhi_remainder_lower C P.lift u v
    have hb : P.lift.ν * P.lift.γ ^ 2 ≤ 5 * P.M / 16 := by
      have hh := mul_le_mul_of_nonneg_right P.nu_le (sq_nonneg P.gamma)
      have he : (5 * P.μ / 4) * P.gamma ^ 2 = 5 * P.M / 16 := by
        rw [P.gamma_sq]; field_simp [ne_of_gt P.μ_pos]; ring
      rw [he] at hh
      exact hh
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v - u‖)
    have hn := mul_nonneg (le_of_lt P.M_pos) (sq_nonneg ‖v - u‖)
    nlinarith

end ManuscriptCalibration
end NCSCPureStochasticLB.PaperExact
