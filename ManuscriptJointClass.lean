import ManuscriptPopulationConstruction
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The Euclidean joint `C¹` formulation of the manuscript's primitive function class. -/
noncomputable section
namespace NCSCPureStochasticLB.PaperExact

abbrev JointSpace (dx dy : ℕ) := WithLp 2 (Vec dx × Vec dy)

instance (dx dy : ℕ) : MeasurableSpace (JointSpace dx dy) := borel _
instance (dx dy : ℕ) : BorelSpace (JointSpace dx dy) := ⟨rfl⟩

def jointPoint {dx dy : ℕ} (x : Vec dx) (y : Vec dy) : JointSpace dx dy :=
  (WithLp.equiv 2 _).symm (x, y)

theorem gradient_remainder_bound {d : ℕ} (f : Vec d → ℝ) (g : Vec d → Vec d) (M : ℝ)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x - g y‖ ≤ M * ‖x - y‖) (x y : Vec d) :
    |f y - f x - @inner ℝ _ _ (g x) (y - x)| ≤ M / 2 * ‖y - x‖ ^ 2 := by
  have hlow := gradient_lower_model f g M hg hl x y
  have hneg : ∀ z, HasGradientAt (fun w => -f w) (-g z) z := by
    intro z
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa only [map_neg] using (hg z).hasFDerivAt.neg
  have hln : ∀ u v, ‖-g u - -g v‖ ≤ M * ‖u - v‖ := by
    intro u v
    simpa only [neg_sub_neg, norm_sub_rev] using hl u v
  have hu := gradient_lower_model (fun w => -f w) (fun w => -g w) M hneg hln x y
  simp only [inner_neg_left] at hu
  rw [abs_le]
  constructor <;> linarith

namespace SmoothStronglyConcave
variable {dx dy : ℕ}

def jointFunction (P : SmoothStronglyConcave dx dy) (z : JointSpace dx dy) : ℝ := P.f z.fst z.snd
def jointGradient (P : SmoothStronglyConcave dx dy) (z : JointSpace dx dy) : JointSpace dx dy :=
  jointPoint (P.gradX z.fst z.snd) (P.gradY z.fst z.snd)

theorem jointGradient_lipschitz (P : SmoothStronglyConcave dx dy) (z w : JointSpace dx dy) :
    ‖P.jointGradient z - P.jointGradient w‖ ≤ P.M * ‖z - w‖ := by
  simpa only [WithLp.prod_norm_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd,
    jointGradient, jointPoint, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd] using
    P.smooth z.fst z.snd w.fst w.snd

theorem joint_remainder (P : SmoothStronglyConcave dx dy) (z w : JointSpace dx dy) :
    ‖P.jointFunction w - P.jointFunction z - @inner ℝ _ _ (P.jointGradient z) (w - z)‖ ≤
      P.M * ‖w - z‖ ^ 2 := by
  have hx := gradient_remainder_bound (fun x => P.f x z.snd) (fun x => P.gradX x z.snd)
    P.M (fun x => P.gradX_spec x _) (P.gradX_x_lipschitz _) z.fst w.fst
  have hyl : ∀ u v, ‖P.gradY w.fst u - P.gradY w.fst v‖ ≤ P.M * ‖u - v‖ := by
    intro u v
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
      Real.sqrt_sq (norm_nonneg _)] using P.gradY_bound w.fst w.fst u v
  have hy := gradient_remainder_bound (P.f w.fst) (P.gradY w.fst)
    P.M (P.gradY_spec w.fst) hyl z.snd w.snd
  have hi := abs_real_inner_le_norm (P.gradY w.fst z.snd - P.gradY z.fst z.snd) (w.snd - z.snd)
  have hb := mul_le_mul_of_nonneg_right (P.gradY_x_lipschitz z.snd w.fst z.fst)
    (norm_nonneg (w.snd - z.snd))
  have hh := hi.trans hb
  rw [inner_sub_left, abs_le] at hh
  rw [abs_le] at hx hy
  simp only [jointFunction, jointGradient, jointPoint, WithLp.prod_inner_apply,
    WithLp.equiv_symm_fst, WithLp.equiv_symm_snd, WithLp.sub_fst, WithLp.sub_snd,
    WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, abs_le]
  have hs := mul_nonneg P.M_pos.le (sq_nonneg (‖w.fst - z.fst‖ - ‖w.snd - z.snd‖))
  constructor <;> nlinarith

theorem joint_hasGradient (P : SmoothStronglyConcave dx dy) (z : JointSpace dx dy) :
    HasGradientAt P.jointFunction (P.jointGradient z) z := by
  rw [hasGradientAt_iff_tendsto]
  have ht : Filter.Tendsto (fun w : JointSpace dx dy => ‖w - z‖) (nhds z) (nhds 0) := by
    have hc : ContinuousAt (fun w : JointSpace dx dy => ‖w - z‖) z :=
      (continuousAt_id.sub continuousAt_const).norm
    simpa only [ContinuousAt, sub_self, norm_zero] using hc
  apply squeeze_zero (g := fun w => P.M * ‖w - z‖)
  · intro w; positivity
  · intro w
    have hr := P.joint_remainder z w
    by_cases hd : ‖w - z‖ = 0
    · simp [hd]
    · calc
        _ ≤ ‖w - z‖⁻¹ * (P.M * ‖w - z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg _))
        _ = P.M * ‖w - z‖ := by field_simp [hd]; ring
  · simpa using tendsto_const_nhds.mul ht

theorem joint_gradient (P : SmoothStronglyConcave dx dy) (z : JointSpace dx dy) :
    gradient P.jointFunction z = P.jointGradient z := (P.joint_hasGradient z).gradient

theorem joint_contDiff (P : SmoothStronglyConcave dx dy) : ContDiff ℝ 1 P.jointFunction := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun z => (P.joint_hasGradient z).differentiableAt, ?_⟩
  have hl : LipschitzWith ⟨P.M, P.M_pos.le⟩ P.jointGradient := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa [dist_eq_norm] using P.jointGradient_lipschitz z w
  have he : fderiv ℝ P.jointFunction = fun z => InnerProductSpace.toDual ℝ _ (P.jointGradient z) := by
    funext z
    exact (P.joint_hasGradient z).hasFDerivAt.fderiv
  rw [he]
  exact (InnerProductSpace.toDual ℝ _).continuous.comp hl.continuous

end SmoothStronglyConcave

def jointInl (dx dy : ℕ) : Vec dx →L[ℝ] JointSpace dx dy :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec dx) (Vec dy)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Vec dx) (Vec dy))

def jointInr (dx dy : ℕ) : Vec dy →L[ℝ] JointSpace dx dy :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec dx) (Vec dy)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (Vec dx) (Vec dy))

theorem joint_partialX {dx dy : ℕ} {F : JointSpace dx dy → ℝ} {g : JointSpace dx dy}
    {x : Vec dx} {y : Vec dy} (h : HasGradientAt F g (jointPoint x y)) :
    HasGradientAt (fun u => F (jointPoint u y)) g.fst x := by
  have hj : HasFDerivAt (fun u => jointPoint u y) (jointInl dx dy) x := by
    convert (jointInl dx dy).hasFDerivAt.add_const (jointPoint 0 y) using 1
    funext u
    change (WithLp.equiv 2 _).symm (u, y) = (WithLp.equiv 2 _).symm (u + 0, 0 + y)
    simp
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h.hasFDerivAt.comp x hj using 1
  ext u
  simp [jointInl, jointPoint, InnerProductSpace.toDual_apply, WithLp.prod_inner_apply]

theorem joint_partialY {dx dy : ℕ} {F : JointSpace dx dy → ℝ} {g : JointSpace dx dy}
    {x : Vec dx} {y : Vec dy} (h : HasGradientAt F g (jointPoint x y)) :
    HasGradientAt (fun v => F (jointPoint x v)) g.snd y := by
  have hj : HasFDerivAt (fun v => jointPoint x v) (jointInr dx dy) y := by
    convert (jointInr dx dy).hasFDerivAt.add_const (jointPoint x 0) using 1
    funext v
    change (WithLp.equiv 2 _).symm (x, v) = (WithLp.equiv 2 _).symm (0 + x, v + 0)
    simp
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h.hasFDerivAt.comp y hj using 1
  ext v
  simp [jointInr, jointPoint, InnerProductSpace.toDual_apply, WithLp.prod_inner_apply]

/-- The paper's joint Euclidean `C¹` smooth/strongly-concave primitive assumptions.
The gradient is Mathlib's actual gradient, not an independently supplied vector field. -/
def JointPrimitive {dx dy : ℕ} (F : JointSpace dx dy → ℝ) (M μ : ℝ) : Prop :=
  ContDiff ℝ 1 F ∧
  (∀ z w, ‖gradient F z - gradient F w‖ ≤ M * ‖z - w‖) ∧
  ∀ x y y', F (jointPoint x y') ≤ F (jointPoint x y) +
    @inner ℝ (Vec dy) _ (gradient F (jointPoint x y)).snd (y' - y) - μ / 2 * ‖y' - y‖ ^ 2

def ofJointPrimitive {dx dy : ℕ} (F : JointSpace dx dy → ℝ) (M μ : ℝ)
    (hM : 0 < M) (hμ : 0 < μ) (h : JointPrimitive F M μ) : SmoothStronglyConcave dx dy where
  f := fun x y => F (jointPoint x y)
  gradX := fun x y => (gradient F (jointPoint x y)).fst
  gradY := fun x y => (gradient F (jointPoint x y)).snd
  M := M
  μ := μ
  M_pos := hM
  μ_pos := hμ
  gradX_spec := fun x y => joint_partialX ((h.1.differentiable (by norm_num) _).hasGradientAt)
  gradY_spec := fun x y => joint_partialY ((h.1.differentiable (by norm_num) _).hasGradientAt)
  smooth := by
    intro x y x' y'
    simpa only [WithLp.prod_norm_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd,
      jointPoint, WithLp.equiv_symm_fst, WithLp.equiv_symm_snd] using h.2.1 (jointPoint x y) (jointPoint x' y')
  stronglyConcave := h.2.2

theorem SmoothStronglyConcave.jointPrimitive {dx dy : ℕ} (P : SmoothStronglyConcave dx dy) :
    JointPrimitive P.jointFunction P.M P.μ := by
  refine ⟨P.joint_contDiff, ?_, ?_⟩
  · intro z w
    rw [P.joint_gradient, P.joint_gradient]
    exact P.jointGradient_lipschitz z w
  · intro x y y'
    rw [P.joint_gradient]
    exact P.stronglyConcave x y y'

/-- Two-way class identification, retaining the same function and the same constants. -/
theorem jointPrimitive_iff {dx dy : ℕ} (F : JointSpace dx dy → ℝ) (M μ : ℝ)
    (hM : 0 < M) (hμ : 0 < μ) :
    JointPrimitive F M μ ↔ ∃ P : SmoothStronglyConcave dx dy,
      P.M = M ∧ P.μ = μ ∧ P.jointFunction = F := by
  constructor
  · intro h
    refine ⟨ofJointPrimitive F M μ hM hμ h, rfl, rfl, ?_⟩
    funext z
    rfl
  · rintro ⟨P, rfl, rfl, rfl⟩
    exact P.jointPrimitive

def jointPrimal {dx dy : ℕ} (F : JointSpace dx dy → ℝ) (x : Vec dx) : ℝ :=
  sSup (Set.range (fun y : Vec dy => F (jointPoint x y)))

/-- Equations (4)--(6), including the finite primal infimum, in the joint `C¹` formulation. -/
def JointFunctionClass {dx dy : ℕ} (F : JointSpace dx dy → ℝ) (M μ Δ : ℝ) : Prop :=
  JointPrimitive F M μ ∧ BddBelow (Set.range (jointPrimal F)) ∧
    jointPrimal F 0 - sInf (Set.range (jointPrimal F)) ≤ Δ

theorem SmoothStronglyConcave.jointPrimal_eq {dx dy : ℕ} (P : SmoothStronglyConcave dx dy) :
    jointPrimal P.jointFunction = P.Phi := by
  funext x
  exact (P.Phi_eq_sup x).symm

theorem jointFunctionClass_iff {dx dy : ℕ} (F : JointSpace dx dy → ℝ) (M μ Δ : ℝ)
    (hM : 0 < M) (hμ : 0 < μ) :
    JointFunctionClass F M μ Δ ↔ ∃ P : SmoothStronglyConcave dx dy,
      P.M = M ∧ P.μ = μ ∧ P.jointFunction = F ∧ BddBelow (Set.range P.Phi) ∧
        P.Phi 0 - sInf (Set.range P.Phi) ≤ Δ := by
  constructor
  · rintro ⟨h, hb, hg⟩
    obtain ⟨P, hM', hμ', hF⟩ := (jointPrimitive_iff F M μ hM hμ).mp h
    rw [← hF, P.jointPrimal_eq] at hb hg
    exact ⟨P, hM', hμ', hF, hb, hg⟩
  · rintro ⟨P, rfl, rfl, rfl, hb, hg⟩
    exact ⟨P.jointPrimitive, by rwa [P.jointPrimal_eq], by rwa [P.jointPrimal_eq]⟩

end NCSCPureStochasticLB.PaperExact
