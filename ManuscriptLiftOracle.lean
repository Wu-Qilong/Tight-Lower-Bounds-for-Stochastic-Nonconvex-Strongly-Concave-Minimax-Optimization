import ManuscriptGeneralLift

/-! Proposition 3.1's oracle reduction for arbitrary probability spaces and base vector fields. -/
noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact.GeneralLift

section MomentBounds
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
variable (ρ : Measure Ω) [IsProbabilityMeasure ρ]

theorem mean_norm_le_of_second_moment {V : Ω → E} (hV : MemLp V 2 ρ)
    {B : ℝ} (hB : 0 ≤ B) (h2 : (∫ ξ, ‖V ξ‖ ^ 2 ∂ρ) ≤ B ^ 2) :
    (∫ ξ, ‖V ξ‖ ∂ρ) ≤ B := by
  let m : ℝ := ∫ ξ, ‖V ξ‖ ∂ρ
  have hi : Integrable (fun ξ => ‖V ξ‖) ρ := hV.norm.integrable (by norm_num)
  have hi2 : Integrable (fun ξ => ‖V ξ‖ ^ 2) ρ := hV.integrable_norm_pow (by decide)
  have hn := integral_nonneg (μ := ρ) (fun ξ => sq_nonneg (‖V ξ‖ - m))
  have he : (∫ ξ, (‖V ξ‖ - m) ^ 2 ∂ρ) = (∫ ξ, ‖V ξ‖ ^ 2 ∂ρ) - m ^ 2 := by
    have hf : (fun ξ => (‖V ξ‖ - m) ^ 2) =
        (fun ξ => (‖V ξ‖ ^ 2 - (2 * m) * ‖V ξ‖) + m ^ 2) := by funext ξ; ring
    have ha := integral_add (hi2.sub (hi.const_mul (2 * m))) (integrable_const (m ^ 2))
    have hb := integral_sub hi2 (hi.const_mul (2 * m))
    simp only [Pi.sub_apply] at ha
    rw [hf, ha, hb, integral_const_mul]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    dsimp [m]
    ring
  rw [he] at hn
  have hm : 0 ≤ m := integral_nonneg (fun ξ => norm_nonneg (V ξ))
  change m ≤ B
  nlinarith

theorem second_moment_add_const {V : Ω → E} (hV : MemLp V 2 ρ)
    (c : E) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ‖c‖ ≤ A) (h2 : (∫ ξ, ‖V ξ‖ ^ 2 ∂ρ) ≤ B ^ 2) :
    (∫ ξ, ‖c + V ξ‖ ^ 2 ∂ρ) ≤ (A + B) ^ 2 := by
  have hi : Integrable (fun ξ => ‖V ξ‖) ρ := hV.norm.integrable (by norm_num)
  have hi2 : Integrable (fun ξ => ‖V ξ‖ ^ 2) ρ := hV.integrable_norm_pow (by decide)
  have hs : MemLp (fun ξ => c + V ξ) 2 ρ := (memLp_const c).add hV
  have hsi : Integrable (fun ξ => ‖c + V ξ‖ ^ 2) ρ := hs.integrable_norm_pow (by decide)
  have hr : Integrable (fun ξ => A ^ 2 + (2 * A) * ‖V ξ‖ + ‖V ξ‖ ^ 2) ρ :=
    ((integrable_const _).add (hi.const_mul _)).add hi2
  have hm := integral_mono hsi hr (fun ξ => by
    have ht := (norm_add_le c (V ξ)).trans (add_le_add_right hc _)
    nlinarith [norm_nonneg (c + V ξ), norm_nonneg (V ξ)])
  have he : (∫ ξ, A ^ 2 + (2 * A) * ‖V ξ‖ + ‖V ξ‖ ^ 2 ∂ρ) =
      A ^ 2 + (2 * A) * (∫ ξ, ‖V ξ‖ ∂ρ) + (∫ ξ, ‖V ξ‖ ^ 2 ∂ρ) := by
    have ha := integral_add ((integrable_const (A ^ 2)).add (hi.const_mul (2 * A))) hi2
    have hb := integral_add (integrable_const (A ^ 2)) (hi.const_mul (2 * A))
    simp only [Pi.add_apply] at ha
    rw [ha, hb, integral_const_mul]
    simp
  rw [he] at hm
  have hmean := mean_norm_le_of_second_moment ρ hV hB h2
  nlinarith
end MomentBounds

variable {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
variable {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
variable (G : Vec T → Ω → Vec T)

/-- One evaluation of the base oracle at `βy` supplies the only random term. -/
def liftedField (z : JointSpace T T) (ξ : Ω) : JointSpace T T :=
  jointPoint ((P.ν * P.γ) • (z.snd - P.γ • z.fst))
    (P.q • G (P.β • z.snd) ξ - P.ν • (z.snd - P.γ • z.fst))

omit [MeasurableSpace Ω] in
theorem liftedField_error (z : JointSpace T T) (ξ : Ω) :
    liftedField P G z ξ - (primitive P C).jointGradient z =
      jointPoint 0 (P.q • (G (P.β • z.snd) ξ - C.gradF (P.β • z.snd))) := by
  apply (WithLp.equiv 2 _).injective
  change (_, _) = (_, _)
  simp [liftedField, SmoothStronglyConcave.jointGradient, primitive, jointPoint]
  module

omit [MeasurableSpace Ω] in
theorem liftedField_error_norm_sq (z : JointSpace T T) (ξ : Ω) :
    ‖liftedField P G z ξ - (primitive P C).jointGradient z‖ ^ 2 =
      P.q ^ 2 * ‖G (P.β • z.snd) ξ - C.gradF (P.β • z.snd)‖ ^ 2 := by
  rw [liftedField_error, WithLp.prod_norm_sq_eq_of_L2]
  simp only [jointPoint, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos P.q_pos]
  ring

omit [IsProbabilityMeasure ρ] in
theorem lifted_variance {v : ℝ}
    (hv : ∀ u, (∫ ξ, ‖G u ξ - C.gradF u‖ ^ 2 ∂ρ) ≤ v ^ 2)
    (z : JointSpace T T) :
    (∫ ξ, ‖liftedField P G z ξ - (primitive P C).jointGradient z‖ ^ 2 ∂ρ) ≤ P.q ^ 2 * v ^ 2 := by
  simp_rw [liftedField_error_norm_sq]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hv _) (sq_nonneg _)

def quadraticField (z : JointSpace T T) : JointSpace T T :=
  jointPoint ((P.ν * P.γ) • (z.snd - P.γ • z.fst)) ((-P.ν) • (z.snd - P.γ • z.fst))

omit [MeasurableSpace Ω] in
theorem liftedField_decomposition (z : JointSpace T T) (ξ : Ω) :
    liftedField P G z ξ = quadraticField P z + jointInr T T (P.q • G (P.β • z.snd) ξ) := by
  apply (WithLp.equiv 2 _).injective
  change (_, _) = (_, _)
  simp [liftedField, quadraticField, jointPoint, jointInr, sub_eq_add_neg, add_comm]

theorem liftedField_memLp (hG : ∀ u, MemLp (G u) 2 ρ) (z : JointSpace T T) :
    MemLp (liftedField P G z) 2 ρ := by
  have h := (jointInr T T).comp_memLp' ((hG (P.β • z.snd)).const_smul P.q)
  have he : liftedField P G z = fun ξ => quadraticField P z + jointInr T T (P.q • G (P.β • z.snd) ξ) :=
    funext (liftedField_decomposition P G z)
  rw [he]
  exact (memLp_const _).add h

theorem liftedField_unbiased (hG : ∀ u, MemLp (G u) 2 ρ)
    (hu : ∀ u, (∫ ξ, G u ξ ∂ρ) = C.gradF u) (z : JointSpace T T) :
    (∫ ξ, liftedField P G z ξ ∂ρ) = (primitive P C).jointGradient z := by
  have he : liftedField P G z = fun ξ => quadraticField P z + jointInr T T (P.q • G (P.β • z.snd) ξ) :=
    funext (liftedField_decomposition P G z)
  have hi : Integrable (fun ξ => P.q • G (P.β • z.snd) ξ) ρ :=
    ((hG (P.β • z.snd)).const_smul P.q).integrable (by norm_num)
  rw [he, integral_add (integrable_const _) ((jointInr T T).integrable_comp hi),
    (jointInr T T).integral_comp_comm hi, integral_smul, hu]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  apply (WithLp.equiv 2 _).injective
  change (_, _) = (_, _)
  simp [quadraticField, jointInr, jointPoint, SmoothStronglyConcave.jointGradient,
    primitive, sub_eq_add_neg, add_comm]

theorem quadraticField_bound (z w : JointSpace T T) :
    ‖quadraticField P z - quadraticField P w‖ ≤ P.ν * (1 + P.γ ^ 2) * ‖z - w‖ := by
  have he : quadraticField P z - quadraticField P w =
      jointPoint ((P.ν * P.γ) • ((z.snd - w.snd) - P.γ • (z.fst - w.fst)))
        ((-P.ν) • ((z.snd - w.snd) - P.γ • (z.fst - w.fst))) := by
    apply (WithLp.equiv 2 _).injective
    change (_, _) = (_, _)
    dsimp [quadraticField, jointPoint]
    congr 1 <;> module
  rw [he]
  simpa only [WithLp.prod_norm_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd, jointPoint,
    WithLp.equiv_symm_fst, WithLp.equiv_symm_snd, pairNorm, pairNormSq] using
    lift_quadratic_pair_bound P (z.fst - w.fst) (z.snd - w.snd)

/-- Same-seed averaged smoothness with the exact constant `ν(1+γ²)+hS`. -/
theorem liftedField_averaged_smooth (hG : ∀ u, MemLp (G u) 2 ρ)
    (S : ℝ) (hS : 0 ≤ S)
    (hAS : ∀ u v, (∫ ξ, ‖G u ξ - G v ξ‖ ^ 2 ∂ρ) ≤ S ^ 2 * ‖u - v‖ ^ 2)
    (z w : JointSpace T T) :
    (∫ ξ, ‖liftedField P G z ξ - liftedField P G w ξ‖ ^ 2 ∂ρ) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * S) ^ 2 * ‖z - w‖ ^ 2 := by
  let V : Ω → JointSpace T T := fun ξ =>
    jointInr T T (P.q • (G (P.β • z.snd) ξ - G (P.β • w.snd) ξ))
  have hV : MemLp V 2 ρ :=
    (jointInr T T).comp_memLp' (((hG (P.β • z.snd)).sub (hG (P.β • w.snd))).const_smul P.q)
  have hn : ∀ ξ, ‖V ξ‖ ^ 2 = P.q ^ 2 * ‖G (P.β • z.snd) ξ - G (P.β • w.snd) ξ‖ ^ 2 := by
    intro ξ
    change ‖jointPoint 0 (P.q • (G (P.β • z.snd) ξ - G (P.β • w.snd) ξ))‖ ^ 2 = _
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [jointPoint, norm_smul, Real.norm_eq_abs, abs_of_pos P.q_pos, mul_pow]
  have hsecond : (∫ ξ, ‖V ξ‖ ^ 2 ∂ρ) ≤ (P.h * S * ‖z - w‖) ^ 2 := by
    simp_rw [hn]
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (hAS (P.β • z.snd) (P.β • w.snd)) (sq_nonneg P.q)
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < P.β from div_pos P.h_pos P.q_pos)] at hb
    have hc : P.q ^ 2 * (S ^ 2 * (P.β * ‖z.snd - w.snd‖) ^ 2) =
        (P.h * S) ^ 2 * ‖z.snd - w.snd‖ ^ 2 := by
      calc
        _ = (P.q * P.β) ^ 2 * S ^ 2 * ‖z.snd - w.snd‖ ^ 2 := by ring
        _ = _ := by rw [P.q_mul_beta]; ring
    rw [hc] at hb
    have hl : ‖z.snd - w.snd‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.sub_fst, WithLp.sub_snd]
      nlinarith [sq_nonneg ‖z.fst - w.fst‖]
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg (P.h * S))])
  have hm := second_moment_add_const ρ hV (quadraticField P z - quadraticField P w)
    (A := P.ν * (1 + P.γ ^ 2) * ‖z - w‖) (B := P.h * S * ‖z - w‖)
    (by have := lift_nu_pos P; positivity) (by have := P.h_pos; positivity)
    (quadraticField_bound P z w) hsecond
  have he : ∀ ξ, liftedField P G z ξ - liftedField P G w ξ =
      (quadraticField P z - quadraticField P w) + V ξ := by
    intro ξ
    rw [liftedField_decomposition, liftedField_decomposition]
    dsimp [V]
    rw [smul_sub, map_sub]
    abel
  simp_rw [he]
  convert hm using 1
  ring

/-- Deterministic postprocessing of a single returned base gradient vector. -/
def simulateResponse (z : JointSpace T T) (r : Vec T) : JointSpace T T :=
  jointPoint ((P.ν * P.γ) • (z.snd - P.γ • z.fst)) (P.q • r - P.ν • (z.snd - P.γ • z.fst))

omit [MeasurableSpace Ω] in
theorem single_query_simulation (z : JointSpace T T) (ξ : Ω) :
    liftedField P G z ξ = simulateResponse P z (G (P.β • z.snd) ξ) := rfl

omit [MeasurableSpace Ω] in
/-- A preselected batch forwards exactly one base query per slot, using the common seed. -/
theorem same_seed_batch_simulation {K : ℕ} (z : Fin K → JointSpace T T) (ξ : Ω) :
    (fun k => liftedField P G (z k) ξ) =
      (fun k => simulateResponse P (z k) (G (P.β • (z k).snd) ξ)) := rfl

omit [IsProbabilityMeasure ρ] in
theorem same_seed_batch_law {K : ℕ} (z : Fin K → JointSpace T T) :
    Measure.map (fun ξ k => liftedField P G (z k) ξ) ρ =
      Measure.map (fun ξ k => simulateResponse P (z k) (G (P.β • (z k).snd) ξ)) ρ := rfl

theorem quadraticField_continuous : Continuous (quadraticField P (T := T)) := by
  have hx : Continuous (fun z : JointSpace T T => z.fst) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec T) (Vec T)).continuous.fst
  have hy : Continuous (fun z : JointSpace T T => z.snd) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec T) (Vec T)).continuous.snd
  have hr := hy.sub (hx.const_smul P.γ)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec T) (Vec T)).symm.continuous.comp
    ((hr.const_smul (P.ν * P.γ)).prodMk (hr.const_smul (-P.ν)))

theorem liftedField_jointlyMeasurable
    (hG : Measurable (fun z : Vec T × Ω => G z.1 z.2)) :
    Measurable (fun z : JointSpace T T × Ω => liftedField P G z.1 z.2) := by
  have hy : Continuous (fun z : JointSpace T T => P.β • z.snd) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec T) (Vec T)).continuous.snd.const_smul P.β
  have hquery : Measurable (fun z : JointSpace T T × Ω => (P.β • z.1.snd, z.2)) :=
    (hy.measurable.comp measurable_fst).prodMk measurable_snd
  have he : (fun z : JointSpace T T × Ω => liftedField P G z.1 z.2) =
      fun z => quadraticField P z.1 + jointInr T T (P.q • G (P.β • z.1.snd) z.2) := by
    funext z
    exact liftedField_decomposition P G z.1 z.2
  rw [he]
  exact ((quadraticField_continuous P).measurable.comp measurable_fst).add
    ((jointInr T T).continuous.measurable.comp ((hG.comp hquery).const_smul P.q))

/-- The complete measurable finite-second-moment oracle reduction in Proposition 3.1. -/
theorem proposition31_oracle
    (hGm : Measurable (fun z : Vec T × Ω => G z.1 z.2))
    (hG : ∀ u, MemLp (G u) 2 ρ)
    (hu : ∀ u, (∫ ξ, G u ξ ∂ρ) = C.gradF u)
    (v S : ℝ) (hS : 0 ≤ S)
    (hv : ∀ u, (∫ ξ, ‖G u ξ - C.gradF u‖ ^ 2 ∂ρ) ≤ v ^ 2)
    (hAS : ∀ u w, (∫ ξ, ‖G u ξ - G w ξ‖ ^ 2 ∂ρ) ≤ S ^ 2 * ‖u - w‖ ^ 2) :
    Measurable (fun z : JointSpace T T × Ω => liftedField P G z.1 z.2) ∧
    (∀ z, MemLp (liftedField P G z) 2 ρ) ∧
    (∀ z, (∫ ξ, liftedField P G z ξ ∂ρ) = gradient (primitive P C).jointFunction z) ∧
    (∀ z, (∫ ξ, ‖liftedField P G z ξ - gradient (primitive P C).jointFunction z‖ ^ 2 ∂ρ) ≤
      P.q ^ 2 * v ^ 2) ∧
    (∀ z w, (∫ ξ, ‖liftedField P G z ξ - liftedField P G w ξ‖ ^ 2 ∂ρ) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * S) ^ 2 * ‖z - w‖ ^ 2) := by
  refine ⟨liftedField_jointlyMeasurable P G hGm, liftedField_memLp P ρ G hG, ?_, ?_,
    liftedField_averaged_smooth P ρ G hG S hS hAS⟩
  · intro z
    rw [(primitive P C).joint_gradient]
    exact liftedField_unbiased P C ρ G hG hu z
  · intro z
    rw [(primitive P C).joint_gradient]
    exact lifted_variance P C ρ G hv z

end NCSCPureStochasticLB.PaperExact.GeneralLift
