import ManuscriptGeneralLift

/-! Appendix F.1: the actual derivative of the actual primal gradient.
The inverse is a constructed continuous linear equivalence, with no invertibility axiom. -/
noncomputable section
namespace NCSCPureStochasticLB.PaperExact.GeneralLift

variable {T : ℕ} (P : LiftParameters) (C : Base T P.ell)

def baseHessian (u : Vec T) : Vec T →L[ℝ] Vec T := fderiv ℝ C.gradF u

theorem baseHessian_bound (u : Vec T) : ‖baseHessian P C u‖ ≤ P.ell := by
  have hl : LipschitzWith ⟨P.ell, P.ell_nonneg⟩ C.gradF := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa [dist_eq_norm] using C.grad_lipschitz v w
  exact norm_fderiv_le_of_lipschitz ℝ hl

def resolvent (u : Vec T) : Vec T →L[ℝ] Vec T :=
  P.ν • (1 : Vec T →L[ℝ] Vec T) - P.h • baseHessian P C u

theorem resolvent_lower (u v : Vec T) : P.μ * ‖v‖ ≤ ‖resolvent P C u v‖ := by
  have hb := (baseHessian P C u).le_opNorm v
  have ha := mul_le_mul_of_nonneg_right (baseHessian_bound P C u) (norm_nonneg v)
  have ht := norm_add_le (resolvent P C u v) (P.h • baseHessian P C u v)
  have he : resolvent P C u v + P.h • baseHessian P C u v = P.ν • v := by
    simp [resolvent]
  rw [he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (lift_nu_pos P), abs_of_pos P.h_pos] at ht
  have hc := mul_le_mul_of_nonneg_left (hb.trans ha) P.h_pos.le
  dsimp [LiftParameters.ν] at ht
  nlinarith

theorem resolvent_ker (u : Vec T) : LinearMap.ker (resolvent P C u) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro v w hvw
  change resolvent P C u v = resolvent P C u w at hvw
  have hz : resolvent P C u (v - w) = 0 := by simp [map_sub, hvw]
  have hb := resolvent_lower P C u (v - w)
  rw [hz, norm_zero] at hb
  have hn : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w), P.μ_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

def resolventEquiv (u : Vec T) : Vec T ≃L[ℝ] Vec T :=
  ContinuousLinearEquiv.ofBijective (resolvent P C u) (resolvent_ker P C u)
    (LinearMap.ker_eq_bot_iff_range_eq_top.mp (resolvent_ker P C u))

def resolventInv (u : Vec T) : Vec T →L[ℝ] Vec T :=
  (resolventEquiv P C u).symm.toContinuousLinearMap

theorem resolvent_inv_left (u v : Vec T) : resolventInv P C u (resolvent P C u v) = v :=
  (resolventEquiv P C u).symm_apply_apply v

theorem resolvent_inv_right (u v : Vec T) : resolvent P C u (resolventInv P C u v) = v :=
  (resolventEquiv P C u).apply_symm_apply v

theorem resolventInv_bound (u v : Vec T) : ‖resolventInv P C u v‖ ≤ P.μ⁻¹ * ‖v‖ := by
  have h := resolvent_lower P C u (resolventInv P C u v)
  rw [resolvent_inv_right] at h
  have hdiv : ‖resolventInv P C u v‖ ≤ ‖v‖ / P.μ :=
    (le_div_iff₀ P.μ_pos).mpr (by simpa only [mul_comm] using h)
  simpa [div_eq_mul_inv, mul_comm] using hdiv

def normalizedResolventEquiv (u : Vec T) : Vec T ≃L[ℝ] Vec T where
  toFun v := (P.ν * P.γ)⁻¹ • resolventEquiv P C u v
  invFun v := (resolventEquiv P C u).symm ((P.ν * P.γ) • v)
  map_add' := by intros; simp [smul_add]
  map_smul' := by
    intro c v
    change (P.ν * P.γ)⁻¹ • (resolventEquiv P C u (c • v)) =
      c • ((P.ν * P.γ)⁻¹ • resolventEquiv P C u v)
    rw [map_smul, smul_comm]
  left_inv := by
    intro v
    dsimp only
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (mul_pos (lift_nu_pos P) P.γ_pos)),
      one_smul, ContinuousLinearEquiv.symm_apply_apply]
  right_inv := by
    intro v
    dsimp only
    rw [ContinuousLinearEquiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (mul_pos (lift_nu_pos P) P.γ_pos)), one_smul]
  continuous_toFun := (resolventEquiv P C u).continuous.const_smul _
  continuous_invFun := (resolventEquiv P C u).symm.continuous.comp (continuous_const.smul continuous_id)

def inverseStationarity (y : Vec T) : Vec T :=
  (P.ν * P.γ)⁻¹ • (P.ν • y - P.q • C.gradF (P.β • y))

theorem inverseStationarity_yStar (x : Vec T) :
    inverseStationarity P C (canonicalLiftYStar P C x) = x := by
  have h := sub_eq_zero.mp (canonicalLiftYStar_dual_stationary P C x)
  unfold inverseStationarity
  rw [h]
  have he : P.ν • canonicalLiftYStar P C x -
      P.ν • (canonicalLiftYStar P C x - P.γ • x) = (P.ν * P.γ) • x := by module
  rw [he, smul_smul, inv_mul_cancel₀ (ne_of_gt (mul_pos (lift_nu_pos P) P.γ_pos)), one_smul]

theorem inverseStationarity_hasFDeriv (hd : Differentiable ℝ C.gradF) (y : Vec T) :
    HasFDerivAt (inverseStationarity P C)
      (normalizedResolventEquiv P C (P.β • y)).toContinuousLinearMap y := by
  have hg := (hd (P.β • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul P.β)
  have hf := (((hasFDerivAt_id y).const_smul P.ν).sub (hg.const_smul P.q)).const_smul (P.ν * P.γ)⁻¹
  change HasFDerivAt (inverseStationarity P C) _ y at hf
  apply hf.congr_fderiv
  ext v : 1
  change (P.ν * P.γ)⁻¹ • (P.ν • v - P.q • ((fderiv ℝ C.gradF (P.β • y)) (P.β • v))) =
    (P.ν * P.γ)⁻¹ • (P.ν • v - P.h • baseHessian P C (P.β • y) v)
  rw [map_smul, smul_smul, P.q_mul_beta]
  rfl

/-- The derivative of the unique maximizer, derived using the inverse-function derivative theorem. -/
theorem yStar_hasFDeriv (hd : Differentiable ℝ C.gradF) (x : Vec T) :
    HasFDerivAt (canonicalLiftYStar P C)
      ((P.ν * P.γ) • resolventInv P C (P.β • canonicalLiftYStar P C x)) x := by
  have hi := HasFDerivAt.of_local_left_inverse
    ((primitive P C).yStar_continuous.continuousAt)
    (inverseStationarity_hasFDeriv P C hd (canonicalLiftYStar P C x))
    (Filter.Eventually.of_forall (inverseStationarity_yStar P C))
  change HasFDerivAt (canonicalLiftYStar P C) _ x at hi
  apply hi.congr_fderiv
  ext v : 1
  change (resolventEquiv P C (P.β • canonicalLiftYStar P C x)).symm ((P.ν * P.γ) • v) =
    (P.ν * P.γ) • (resolventEquiv P C (P.β • canonicalLiftYStar P C x)).symm v
  exact map_smul _ _ _

/-- Equation (63) as an identity of continuous linear operators (hence in every orthonormal basis). -/
theorem primal_hessian_formula (hd : Differentiable ℝ C.gradF) (x : Vec T) :
    fderiv ℝ (gradient (canonicalLiftPhi P C)) x =
      (P.ν * P.γ ^ 2 * P.h) •
        (baseHessian P C (P.β • canonicalLiftYStar P C x)).comp
          (resolventInv P C (P.β • canonicalLiftYStar P C x)) := by
  have hg : gradient (canonicalLiftPhi P C) = canonicalLiftGradPhi P C :=
    funext (fun z => (canonicalLiftPhi_grad P C z).gradient)
  rw [hg]
  have hy := yStar_hasFDeriv P C hd x
  have hchain := (hd (P.β • canonicalLiftYStar P C x)).hasFDerivAt.comp x (hy.const_smul P.β)
  have hf := hchain.const_smul (P.γ * P.q)
  change HasFDerivAt (fun z => (P.γ * P.q) • C.gradF (P.β • canonicalLiftYStar P C z)) _ x at hf
  have he : canonicalLiftGradPhi P C = fun z =>
      (P.γ * P.q) • C.gradF (P.β • canonicalLiftYStar P C z) :=
    funext (canonicalLiftGradPhi_eq_scaled_chain P C)
  rw [he, hf.fderiv]
  ext v : 1
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  change (P.γ * P.q * (P.β * (P.ν * P.γ))) •
    (baseHessian P C (P.β • canonicalLiftYStar P C x))
      (resolventInv P C (P.β • canonicalLiftYStar P C x) v) =
    (P.ν * P.γ ^ 2 * P.h) •
    (baseHessian P C (P.β • canonicalLiftYStar P C x))
      (resolventInv P C (P.β • canonicalLiftYStar P C x) v)
  congr 1
  calc
    _ = P.ν * P.γ ^ 2 * (P.q * P.β) := by ring
    _ = _ := by rw [P.q_mul_beta]

theorem base_gradient_differentiable_of_C2 (hC : ContDiff ℝ 2 C.H) : Differentiable ℝ C.gradF := by
  have he : C.gradF = fun x => (InnerProductSpace.toDual ℝ (Vec T)).symm (fderiv ℝ C.H x) := by
    funext x
    rw [(C.grad_is_gradient x).hasFDerivAt.fderiv]
    simp
  rw [he]
  exact (InnerProductSpace.toDual ℝ (Vec T)).symm.toContinuousLinearEquiv.differentiable.comp
    ((hC.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num))

theorem primal_hessian_formula_of_C2 (hC : ContDiff ℝ 2 C.H) (x : Vec T) :
    fderiv ℝ (gradient (canonicalLiftPhi P C)) x =
      (P.ν * P.γ ^ 2 * P.h) •
        (baseHessian P C (P.β • canonicalLiftYStar P C x)).comp
          (resolventInv P C (P.β • canonicalLiftYStar P C x)) :=
  primal_hessian_formula P C (base_gradient_differentiable_of_C2 P C hC) x

theorem baseHessian_eq_actual (u : Vec T) : baseHessian P C u = fderiv ℝ (gradient C.H) u := by
  have he : C.gradF = gradient C.H := funext (fun z => (C.grad_is_gradient z).gradient.symm)
  simp only [baseHessian, he]

theorem resolventInv_opNorm (u : Vec T) : ‖resolventInv P C u‖ ≤ P.μ⁻¹ := by
  exact (resolventInv P C u).opNorm_le_bound (inv_nonneg.mpr P.μ_pos.le)
    (resolventInv_bound P C u)

/-- Both assertions of Proposition F.1, with the Hessian and gradient of the actual value function. -/
theorem propositionF1 (hC : ContDiff ℝ 2 C.H) :
    (∀ x, fderiv ℝ (gradient (canonicalLiftPhi P C)) x =
      (P.ν * P.γ ^ 2 * P.h) •
        (fderiv ℝ (gradient C.H) (P.β • canonicalLiftYStar P C x)).comp
          (resolventInv P C (P.β • canonicalLiftYStar P C x))) ∧
    (∀ x x', ‖gradient (canonicalLiftPhi P C) x - gradient (canonicalLiftPhi P C) x'‖ ≤
      (P.ν * P.γ ^ 2 * P.ell * P.h / P.μ) * ‖x - x'‖) := by
  constructor
  · intro x
    simpa only [baseHessian_eq_actual] using primal_hessian_formula_of_C2 P C hC x
  · intro x x'
    rw [(canonicalLiftPhi_grad P C x).gradient, (canonicalLiftPhi_grad P C x').gradient]
    exact canonicalLiftGradPhi_lipschitz P C x x'

end NCSCPureStochasticLB.PaperExact.GeneralLift
