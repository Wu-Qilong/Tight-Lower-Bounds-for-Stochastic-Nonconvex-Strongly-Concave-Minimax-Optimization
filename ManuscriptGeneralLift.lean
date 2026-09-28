import ManuscriptJointClass

/-! Proposition 3.1 for arbitrary smooth base functions, independent of the zero-chain axiom. -/
noncomputable section
namespace NCSCPureStochasticLB.PaperExact.GeneralLift

structure LiftParameters where
  μ : ℝ
  q : ℝ
  h : ℝ
  γ : ℝ
  ell : ℝ
  μ_pos : 0 < μ
  q_pos : 0 < q
  h_pos : 0 < h
  γ_pos : 0 < γ
  ell_nonneg : 0 ≤ ell

namespace LiftParameters
def α (P : LiftParameters) : ℝ := P.q ^ 2 / P.h
def β (P : LiftParameters) : ℝ := P.h / P.q
def ν (P : LiftParameters) : ℝ := P.μ + P.ell * P.h
theorem alpha_mul_beta (P : LiftParameters) : P.α * P.β = P.q := by
  unfold α β
  field_simp [ne_of_gt P.h_pos, ne_of_gt P.q_pos]
  ring
theorem q_mul_beta (P : LiftParameters) : P.q * P.β = P.h := by
  unfold β
  field_simp [ne_of_gt P.q_pos]
end LiftParameters

theorem lift_nu_pos (P : LiftParameters) : 0 < P.ν :=
  add_pos_of_pos_of_nonneg P.μ_pos (mul_nonneg P.ell_nonneg P.h_pos.le)

/-- Only genuine first-order analytic hypotheses; no lift conclusions are fields. -/
structure Base (T : ℕ) (ell : ℝ) where
  H : Vec T → ℝ
  gradF : Vec T → Vec T
  grad_is_gradient : ∀ u, HasGradientAt H (gradF u) u
  grad_lipschitz : ∀ u v, ‖gradF u - gradF v‖ ≤ ell * ‖u - v‖

def liftedF {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x y : Vec T) : ℝ :=
  P.α * C.H (P.β • y) - P.ν / 2 * ‖y - P.γ • x‖ ^ 2

def LiftStrongConcavity {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (μ : ℝ) : Prop :=
  ∀ x y y', liftedF P C x y' ≤ liftedF P C x y +
    @inner ℝ (Vec T) _ (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
    μ / 2 * ‖y' - y‖ ^ 2

theorem explicitFT_smooth_upper {T : ℕ} {ell : ℝ} (C : Base T ell) (u v : Vec T) :
    C.H v ≤ C.H u + @inner ℝ _ _ (C.gradF u) (v - u) + ell / 2 * ‖v - u‖ ^ 2 := by
  have hr := gradient_remainder_bound C.H C.gradF ell C.grad_is_gradient C.grad_lipschitz u v
  have := (abs_le.mp hr).2
  linarith

theorem lift_alpha_mul_beta_sq (P : LiftParameters) :
    P.α * P.β ^ 2 = P.h := by
  calc
    P.α * P.β ^ 2 = (P.α * P.β) * P.β := by ring
    _ = P.q * P.β := by rw [P.alpha_mul_beta]
    _ = P.h := P.q_mul_beta

/-- Exact square expansion for the quadratic coupling around the current dual point. -/
theorem lift_quadratic_norm_expansion {T : ℕ} (P : LiftParameters)
    (x y y' : Vec T) :
    ‖y' - P.γ • x‖ ^ 2 =
      ‖y - P.γ • x‖ ^ 2 +
        2 * @inner ℝ (Vec T) _ (y - P.γ • x) (y' - y) +
        ‖y' - y‖ ^ 2 := by
  have hvec : y' - P.γ • x = (y - P.γ • x) + (y' - y) := by
    module
  rw [hvec, norm_add_sq_real]

/-- Lemma 2.1's smooth upper inequality, after the lift scaling, becomes exactly the chain
part of the strong-concavity estimate used in Lemma 2.3(i). -/
theorem lift_chain_smooth_upper_scaled {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (y y' : Vec T) :
    P.α * C.H (P.β • y') ≤
      P.α * C.H (P.β • y) +
        P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
        (P.ell * P.h) / 2 * ‖y' - y‖ ^ 2 := by
  have hα0 : 0 ≤ P.α := by
    rw [LiftParameters.α]
    exact div_nonneg (sq_nonneg P.q) (le_of_lt P.h_pos)
  have hβpos : 0 < P.β := by
    exact div_pos P.h_pos P.q_pos
  have hs := explicitFT_smooth_upper C (P.β • y) (P.β • y')
  have hm := mul_le_mul_of_nonneg_left hs hα0
  have hdiff : P.β • y' - P.β • y = P.β • (y' - y) := by
    module
  have hinner :
      @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (P.β • y' - P.β • y) =
        P.β * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) := by
    rw [hdiff, real_inner_smul_right]
  have hnorm :
      ‖P.β • y' - P.β • y‖ ^ 2 = P.β ^ 2 * ‖y' - y‖ ^ 2 := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hβpos]
    ring
  rw [hinner, hnorm] at hm
  calc
    P.α * C.H (P.β • y')
        ≤ P.α * (C.H (P.β • y) +
          P.β * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
          P.ell / 2 * (P.β ^ 2 * ‖y' - y‖ ^ 2)) := hm
    _ = P.α * C.H (P.β • y) +
          (P.α * P.β) * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
          P.ell / 2 * (P.α * P.β ^ 2) * ‖y' - y‖ ^ 2 := by ring
    _ = P.α * C.H (P.β • y) +
          P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
          (P.ell * P.h) / 2 * ‖y' - y‖ ^ 2 := by
      rw [P.alpha_mul_beta, lift_alpha_mul_beta_sq]
      ring

/-- Paper Lemma 2.3(i), deterministic core: for every fixed primal point, the lifted dual
objective is `μ`-strongly concave.  This is derived directly from the imported chain smoothness
inequality and the quadratic block, rather than supplied as a certificate field. -/
theorem liftedF_mu_strong_concavity {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) :
    LiftStrongConcavity P C P.μ := by
  intro x y y'
  have hchain := lift_chain_smooth_upper_scaled P C y y'
  have hquad := lift_quadratic_norm_expansion P x y y'
  have hgradinner :
      @inner ℝ (Vec T) _
        (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) =
      P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) -
        P.ν * @inner ℝ (Vec T) _ (y - P.γ • x) (y' - y) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  have hsub := sub_le_sub_right hchain (P.ν / 2 * ‖y' - P.γ • x‖ ^ 2)
  unfold liftedF
  calc
    P.α * C.H (P.β • y') -
          P.ν / 2 * ‖y' - P.γ • x‖ ^ 2
        ≤ (P.α * C.H (P.β • y) +
            P.q * @inner ℝ (Vec T) _ (C.gradF (P.β • y)) (y' - y) +
            (P.ell * P.h) / 2 * ‖y' - y‖ ^ 2) -
          P.ν / 2 * ‖y' - P.γ • x‖ ^ 2 := hsub
    _ = P.α * C.H (P.β • y) -
          P.ν / 2 * ‖y - P.γ • x‖ ^ 2 +
          @inner ℝ (Vec T) _
            (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) (y' - y) -
          P.μ / 2 * ‖y' - y‖ ^ 2 := by
      rw [hquad, hgradinner]
      simp only [LiftParameters.ν]
      ring


theorem lift_quadratic_pair_bound {T : ℕ} (P : LiftParameters) (dx dy : Vec T) :
    pairNorm
        ((P.ν * P.γ) • (dy - P.γ • dx))
        ((-P.ν) • (dy - P.γ • dx)) ≤
      P.ν * (1 + P.γ ^ 2) * pairNorm dx dy := by
  let r : Vec T := dy - P.γ • dx
  have hnu : 0 < P.ν := lift_nu_pos P
  have hγ : 0 < P.γ := P.γ_pos
  have hr : ‖r‖ ≤ ‖dy‖ + P.γ * ‖dx‖ := by
    dsimp [r]
    calc
      ‖dy - P.γ • dx‖ ≤ ‖dy‖ + ‖P.γ • dx‖ := norm_sub_le _ _
      _ = ‖dy‖ + P.γ * ‖dx‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hr2 : ‖r‖ ^ 2 ≤ (1 + P.γ ^ 2) * pairNorm dx dy ^ 2 := by
    have hrsq : ‖r‖ ^ 2 ≤ (‖dy‖ + P.γ * ‖dx‖) ^ 2 := by
      have h0 := norm_nonneg r
      have h1 : 0 ≤ ‖dy‖ + P.γ * ‖dx‖ := by positivity
      nlinarith
    have hp := pairNorm_sq_eq dx dy
    calc
      ‖r‖ ^ 2 ≤ (‖dy‖ + P.γ * ‖dx‖) ^ 2 := hrsq
      _ ≤ (1 + P.γ ^ 2) * (‖dx‖ ^ 2 + ‖dy‖ ^ 2) := by
        nlinarith [sq_nonneg (‖dx‖ - P.γ * ‖dy‖)]
      _ = (1 + P.γ ^ 2) * pairNorm dx dy ^ 2 := by rw [hp]
  have hout :
      pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) ^ 2 =
        P.ν ^ 2 * (1 + P.γ ^ 2) * ‖r‖ ^ 2 := by
    rw [pairNorm_sq_eq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (mul_pos hnu hγ), abs_neg, abs_of_pos hnu]
    ring
  have htarget :
      pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) ^ 2 ≤
        (P.ν * (1 + P.γ ^ 2) * pairNorm dx dy) ^ 2 := by
    rw [hout]
    have hfac : 0 ≤ P.ν ^ 2 * (1 + P.γ ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hr2 hfac
    nlinarith [sq_nonneg P.γ]
  have hl : 0 ≤ pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) := pairNorm_nonneg _ _
  have hγfac : 0 ≤ 1 + P.γ ^ 2 := by nlinarith [sq_nonneg P.γ]
  have hright : 0 ≤ P.ν * (1 + P.γ ^ 2) * pairNorm dx dy :=
    mul_nonneg (mul_nonneg (le_of_lt hnu) hγfac) (pairNorm_nonneg dx dy)
  simpa [r] using (by nlinarith :
    pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) ≤
      P.ν * (1 + P.γ ^ 2) * pairNorm dx dy)

/-- The chain contribution to the lifted dual gradient is `P.ell h`-Lipschitz in the product norm. -/
theorem lift_chain_pair_bound {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (dx y y' : Vec T) :
    pairNorm 0 (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) ≤
      (P.ell * P.h) * pairNorm dx (y - y') := by
  have hq : 0 < P.q := P.q_pos
  have hβ : 0 < P.β := div_pos P.h_pos P.q_pos
  have hl0 : 0 ≤ P.ell := P.ell_nonneg
  have hgrad := C.grad_lipschitz (P.β • y) (P.β • y')
  have harg : ‖P.β • y - P.β • y'‖ = P.β * ‖y - y'‖ := by
    have hv : P.β • y - P.β • y' = P.β • (y - y') := by module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  rw [harg] at hgrad
  have hchain :
      ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ ≤
        (P.ell * P.h) * ‖y - y'‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    calc
      P.q * ‖C.gradF (P.β • y) - C.gradF (P.β • y')‖
          ≤ P.q * (P.ell * (P.β * ‖y - y'‖)) :=
            mul_le_mul_of_nonneg_left hgrad (le_of_lt hq)
      _ = (P.ell * P.h) * ‖y - y'‖ := by
        rw [← P.q_mul_beta]
        ring
  have hzero :
      pairNorm (0 : Vec T) (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))) =
        ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖ := by
    have hs := pairNorm_sq_eq (0 : Vec T)
      (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')))
    have hp := pairNorm_nonneg (0 : Vec T)
      (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')))
    have hn := norm_nonneg (P.q • (C.gradF (P.β • y) - C.gradF (P.β • y')))
    simp at hs
    nlinarith
  rw [hzero]
  calc
    ‖P.q • (C.gradF (P.β • y) - C.gradF (P.β • y'))‖
        ≤ (P.ell * P.h) * ‖y - y'‖ := hchain
    _ ≤ (P.ell * P.h) * pairNorm dx (y - y') := by
      exact mul_le_mul_of_nonneg_left (norm_le_pairNorm_right dx (y - y'))
        (mul_nonneg hl0 (le_of_lt P.h_pos))

/-- Paper equation (11): the displayed lifted gradient is jointly Lipschitz with constant
`ν(1+γ²)+P.ellh`. -/
theorem liftedF_joint_smoothness {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) :
    ∀ x y x' y',
      pairNorm
        ((P.ν * P.γ) • (y - P.γ • x) - (P.ν * P.γ) • (y' - P.γ • x'))
        ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
         (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x'))) ≤
        (P.ν * (1 + P.γ ^ 2) + P.ell * P.h) * pairNorm (x - x') (y - y') := by
  intro x y x' y'
  let dx : Vec T := x - x'
  let dy : Vec T := y - y'
  let r : Vec T := dy - P.γ • dx
  let dg : Vec T := C.gradF (P.β • y) - C.gradF (P.β • y')
  have hx :
      (P.ν * P.γ) • (y - P.γ • x) - (P.ν * P.γ) • (y' - P.γ • x') =
        (P.ν * P.γ) • r := by
    dsimp [r, dx, dy]
    module
  have hy :
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
          (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x')) =
        (-P.ν) • r + P.q • dg := by
    dsimp [r, dx, dy, dg]
    module
  rw [hx, hy]
  calc
    pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r + P.q • dg)
        ≤ pairNorm ((P.ν * P.γ) • r) ((-P.ν) • r) + pairNorm 0 (P.q • dg) := by
          simpa using pairNorm_triangle
            ((P.ν * P.γ) • r) ((-P.ν) • r) (0 : Vec T) (P.q • dg)
    _ ≤ P.ν * (1 + P.γ ^ 2) * pairNorm dx dy +
          (P.ell * P.h) * pairNorm dx dy := by
      apply add_le_add
      · simpa [r] using lift_quadratic_pair_bound P dx dy
      · simpa [dg, dy] using lift_chain_pair_bound P C dx y y'
    _ = (P.ν * (1 + P.γ ^ 2) + P.ell * P.h) * pairNorm dx dy := by ring
    _ = (P.ν * (1 + P.γ ^ 2) + P.ell * P.h) *
          pairNorm (x - x') (y - y') := by rfl

/-- Actual primal partial gradient of the lifted objective. -/
theorem liftedF_gradX_formula {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x y : Vec T) :
    IsEuclideanGradientAt (fun x' => liftedF P C x' y)
      ((P.ν * P.γ) • (y - P.γ • x)) x := by
  change HasGradientAt (fun x' => liftedF P C x' y)
    ((P.ν * P.γ) • (y - P.γ • x)) x
  rw [hasGradientAt_iff_hasFDerivAt]
  have haff0 :
      HasFDerivAt (fun x' : Vec T => y - P.γ • x')
        ((0 : Vec T →L[ℝ] Vec T) - P.γ • (1 : Vec T →L[ℝ] Vec T)) x :=
    (hasFDerivAt_const (𝕜 := ℝ) y x).sub
      ((hasFDerivAt_id x).const_smul P.γ)
  have haff :
      HasFDerivAt (fun x' : Vec T => y - P.γ • x')
        ((-P.γ) • (1 : Vec T →L[ℝ] Vec T)) x := by
    convert haff0 using 1
    · ext z
      simp
  have hsq := haff.norm_sq
  have hquad := hsq.const_smul (-P.ν / 2)
  have hconst := hasFDerivAt_const (𝕜 := ℝ)
    (P.α * C.H (P.β • y)) x
  have hsum := hconst.add hquad
  have hD :
      (0 : Vec T →L[ℝ] ℝ) +
          (-P.ν / 2) •
            (2 • (innerSL ℝ (y - P.γ • x)).comp
              ((-P.γ) • (1 : Vec T →L[ℝ] Vec T))) =
        InnerProductSpace.toDual ℝ (Vec T) ((P.ν * P.γ) • (y - P.γ • x)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hD] at hsum
  have hfun :
      (fun x' : Vec T => liftedF P C x' y) =
        (fun x' : Vec T =>
          P.α * C.H (P.β • y) +
            (-P.ν / 2) • ‖y - P.γ • x'‖ ^ 2) := by
    funext x'
    simp [liftedF, smul_eq_mul]
    ring
  rw [hfun]
  exact hsum

/-- Actual dual partial gradient of the lifted objective. -/
theorem liftedF_gradY_formula {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x y : Vec T) :
    IsEuclideanGradientAt (fun y' => liftedF P C x y')
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) y := by
  change HasGradientAt (fun y' => liftedF P C x y')
    (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) y
  rw [hasGradientAt_iff_hasFDerivAt]
  have hbase : HasGradientAt (C.H)
      (C.gradF (P.β • y)) (P.β • y) := by
    exact C.grad_is_gradient (P.β • y)
  have hlin :
      HasFDerivAt (fun y' : Vec T => P.β • y')
        (P.β • (1 : Vec T →L[ℝ] Vec T)) y := by
    simpa using (hasFDerivAt_id y).const_smul P.β
  have hchain0 := hbase.hasFDerivAt.comp y hlin
  have hchain := hchain0.const_smul P.α
  have hchainD :
      P.α • ((InnerProductSpace.toDual ℝ (Vec T) (C.gradF (P.β • y))).comp
        (P.β • (1 : Vec T →L[ℝ] Vec T))) =
        InnerProductSpace.toDual ℝ (Vec T) (P.q • C.gradF (P.β • y)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, P.alpha_mul_beta]
  rw [hchainD] at hchain
  have haff0 := (hasFDerivAt_id y).sub
    (hasFDerivAt_const (𝕜 := ℝ) (P.γ • x) y)
  have haff :
      HasFDerivAt (fun y' : Vec T => y' - P.γ • x)
        (1 : Vec T →L[ℝ] Vec T) y := by
    simpa using haff0
  have hsq := haff.norm_sq
  have hquad := hsq.const_smul (-P.ν / 2)
  have hquadD :
      (-P.ν / 2) •
          (2 • (innerSL ℝ (y - P.γ • x)).comp
            (1 : Vec T →L[ℝ] Vec T)) =
        InnerProductSpace.toDual ℝ (Vec T) ((-P.ν) • (y - P.γ • x)) := by
    ext z
    simp [ContinuousLinearMap.comp_apply, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hquadD] at hquad
  have hsum := hchain.add hquad
  have hsumD :
      InnerProductSpace.toDual ℝ (Vec T) (P.q • C.gradF (P.β • y)) +
          InnerProductSpace.toDual ℝ (Vec T) ((-P.ν) • (y - P.γ • x)) =
        InnerProductSpace.toDual ℝ (Vec T)
          (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) := by
    ext z
    simp [sub_eq_add_neg, real_inner_smul_left, add_comm]
  rw [hsumD] at hsum
  have hfun :
      (fun y' : Vec T => liftedF P C x y') =
        (fun y' : Vec T =>
          P.α • C.H (P.β • y') +
            (-P.ν / 2) • ‖y' - P.γ • x‖ ^ 2) := by
    funext y'
    simp [liftedF, smul_eq_mul]
    ring
  rw [hfun]
  exact hsum



def primitive {T : ℕ} (P : LiftParameters) (C : Base T P.ell) : SmoothStronglyConcave T T where
  f := liftedF P C
  gradX := fun x y => (P.ν * P.γ) • (y - P.γ • x)
  gradY := fun x y => P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)
  M := P.ν * (1 + P.γ ^ 2) + P.ell * P.h
  μ := P.μ
  M_pos := by have := lift_nu_pos P; have := P.ell_nonneg; have := P.h_pos; positivity
  μ_pos := P.μ_pos
  gradX_spec := liftedF_gradX_formula P C
  gradY_spec := liftedF_gradY_formula P C
  smooth := liftedF_joint_smoothness P C
  stronglyConcave := liftedF_mu_strong_concavity P C

def canonicalLiftYStar {T : ℕ} (P : LiftParameters) (C : Base T P.ell) : Vec T → Vec T :=
  (primitive P C).yStar

def canonicalLiftPhi {T : ℕ} (P : LiftParameters) (C : Base T P.ell) : Vec T → ℝ :=
  (primitive P C).Phi

def canonicalLiftGradPhi {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x : Vec T) : Vec T :=
  (P.ν * P.γ) • (canonicalLiftYStar P C x - P.γ • x)

theorem canonicalLiftPhi_grad {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    HasGradientAt (canonicalLiftPhi P C) (canonicalLiftGradPhi P C x) x :=
  (primitive P C).Phi_hasGradient x

theorem canonicalLiftPhi_eq_sup {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    canonicalLiftPhi P C x = sSup (Set.range (liftedF P C x)) := (primitive P C).Phi_eq_sup x

theorem canonicalLiftYStar_dual_stationary {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    P.q • C.gradF (P.β • canonicalLiftYStar P C x) -
      P.ν • (canonicalLiftYStar P C x - P.γ • x) = 0 := (primitive P C).yStar_stationary x

theorem canonicalLiftYStar_scaled_fixed_point {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    P.β • canonicalLiftYStar P C x - (P.β * P.γ) • x =
      (P.h / P.ν) • C.gradF (P.β • canonicalLiftYStar P C x) := by
  have h := sub_eq_zero.mp (canonicalLiftYStar_dual_stationary P C x)
  calc
    _ = P.β • (canonicalLiftYStar P C x - P.γ • x) := by module
    _ = (P.β / P.ν) • (P.ν • (canonicalLiftYStar P C x - P.γ • x)) := by
      rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt (lift_nu_pos P))]
    _ = (P.β / P.ν) • (P.q • C.gradF (P.β • canonicalLiftYStar P C x)) := by rw [h]
    _ = _ := by
      rw [smul_smul]
      congr 1
      calc
        _ = (P.q * P.β) / P.ν := by ring
        _ = _ := by rw [P.q_mul_beta]

theorem liftStrongConcavity_antimonotone {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (m : ℝ)
    (hm : LiftStrongConcavity P C m) (x y y' : Vec T) :
    @inner ℝ (Vec T) _
      ((P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
       (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x)))
      (y - y') ≤ -m * ‖y - y'‖ ^ 2 := by
  have h1 := hm x y y'
  have h2 := hm x y' y
  have hdiff : y' - y = -(y - y') := by
    module
  rw [hdiff] at h1
  simp only [inner_neg_right, norm_neg] at h1
  rw [inner_sub_left]
  nlinarith


theorem canonicalLiftYStar_lipschitz {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x x' : Vec T) :
    ‖canonicalLiftYStar P C x - canonicalLiftYStar P C x'‖ ≤
      (P.ν * P.γ / P.μ) * ‖x - x'‖ := by
  let y : Vec T := canonicalLiftYStar P C x
  let y' : Vec T := canonicalLiftYStar P C x'
  let d : Vec T := y - y'
  let dx : Vec T := x - x'
  have hy :
      P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x) = 0 := by
    simpa only [y] using canonicalLiftYStar_dual_stationary P C x
  have hy' :
      P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x') = 0 := by
    simpa only [y'] using canonicalLiftYStar_dual_stationary P C x'
  have hcross :
      P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x) =
        (P.ν * P.γ) • dx := by
    calc
      P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x) =
          (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x')) +
            (P.ν * P.γ) • (x - x') := by
              module
      _ = (P.ν * P.γ) • (x - x') := by rw [hy']; simp
      _ = (P.ν * P.γ) • dx := by rfl
  have hanti := liftStrongConcavity_antimonotone P C P.μ
    (liftedF_mu_strong_concavity P C) x y y'
  have hgradDiff :
      (P.q • C.gradF (P.β • y) - P.ν • (y - P.γ • x)) -
        (P.q • C.gradF (P.β • y') - P.ν • (y' - P.γ • x)) =
          -((P.ν * P.γ) • dx) := by
    rw [hy, hcross]
    module
  rw [hgradDiff] at hanti
  have hinner :
      @inner ℝ (Vec T) _ dx d ≤ ‖dx‖ * ‖d‖ :=
    real_inner_le_norm dx d
  have hk : 0 < P.ν * P.γ := mul_pos (lift_nu_pos P) P.γ_pos
  have hmuquad :
      P.μ * ‖d‖ ^ 2 ≤ (P.ν * P.γ) *
        @inner ℝ (Vec T) _ dx d := by
    rw [inner_neg_left, real_inner_smul_left] at hanti
    nlinarith
  have hmain :
      P.μ * ‖d‖ ^ 2 ≤ (P.ν * P.γ) * (‖dx‖ * ‖d‖) := by
    exact le_trans hmuquad
      (mul_le_mul_of_nonneg_left hinner (le_of_lt hk))
  by_cases hd0 : ‖d‖ = 0
  · have hcoef : 0 ≤ P.ν * P.γ / P.μ :=
      le_of_lt (div_pos hk P.μ_pos)
    have hleft :
        ‖canonicalLiftYStar P C x - canonicalLiftYStar P C x'‖ = 0 := by
      simpa only [d, y, y'] using hd0
    rw [hleft]
    exact mul_nonneg hcoef (norm_nonneg _)
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd0)
    have hcancel : P.μ * ‖d‖ ≤ (P.ν * P.γ) * ‖dx‖ := by
      nlinarith
    have hcancel' : ‖d‖ * P.μ ≤ (P.ν * P.γ) * ‖dx‖ := by
      nlinarith [hcancel]
    have hdiv : ‖d‖ ≤ ((P.ν * P.γ) * ‖dx‖) / P.μ :=
      (le_div_iff₀ P.μ_pos).2 hcancel'
    simpa [d, dx, y, y', div_mul_eq_mul_div, mul_assoc] using hdiv


theorem canonicalLiftGradPhi_eq_scaled_chain {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    canonicalLiftGradPhi P C x =
      (P.γ * P.q) • C.gradF (P.β • canonicalLiftYStar P C x) := by
  have hstat := canonicalLiftYStar_dual_stationary P C x
  have hqeq :
      P.q • C.gradF (P.β • canonicalLiftYStar P C x) =
        P.ν • (canonicalLiftYStar P C x - P.γ • x) :=
    sub_eq_zero.mp hstat
  unfold canonicalLiftGradPhi
  calc
    (P.ν * P.γ) • (canonicalLiftYStar P C x - P.γ • x) =
        P.γ • (P.ν • (canonicalLiftYStar P C x - P.γ • x)) := by
          module
    _ = P.γ • (P.q • C.gradF (P.β • canonicalLiftYStar P C x)) := by rw [← hqeq]
    _ = (P.γ * P.q) • C.gradF (P.β • canonicalLiftYStar P C x) := by
      module

/-- Fixed-point comparison between the chain gradient at the primal point
`w=(βγ)x` and at the dual maximizer `z*=βy*(x)`.  This is the quantitative core
of paper equation (15). -/
theorem canonicalLift_chain_gradient_comparison {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    ‖C.gradF ((P.β * P.γ) • x)‖ ≤
      (1 + P.ell * P.h / P.ν) *
        ‖C.gradF (P.β • canonicalLiftYStar P C x)‖ := by
  let z : Vec T := P.β • canonicalLiftYStar P C x
  let w : Vec T := (P.β * P.γ) • x
  let gz : Vec T := C.gradF z
  let gw : Vec T := C.gradF w
  have hfp := canonicalLiftYStar_scaled_fixed_point P C x
  have hzw : z - w = (P.h / P.ν) • gz := by
    simpa only [z, w, gz] using hfp
  have hwz : w - z = -(P.h / P.ν) • gz := by
    calc
      w - z = -(z - w) := by module
      _ = -((P.h / P.ν) • gz) := by rw [hzw]
      _ = -(P.h / P.ν) • gz := by module
  have hratio : 0 < P.h / P.ν := div_pos P.h_pos (lift_nu_pos P)
  have hnormdiff : ‖w - z‖ = (P.h / P.ν) * ‖gz‖ := by
    rw [hwz, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hratio]
  have hlip : ‖gw - gz‖ ≤ P.ell * ‖w - z‖ := by
    simpa only [gw, gz] using C.grad_lipschitz w z
  have htri : ‖gw‖ ≤ ‖gw - gz‖ + ‖gz‖ := by
    calc
      ‖gw‖ = ‖(gw - gz) + gz‖ := by
        congr 1
        module
      _ ≤ ‖gw - gz‖ + ‖gz‖ := norm_add_le _ _
  calc
    ‖C.gradF ((P.β * P.γ) • x)‖ = ‖gw‖ := by rfl
    _ ≤ ‖gw - gz‖ + ‖gz‖ := htri
    _ ≤ P.ell * ‖w - z‖ + ‖gz‖ := add_le_add_right hlip _
    _ = (1 + P.ell * P.h / P.ν) * ‖gz‖ := by
      rw [hnormdiff]
      ring
    _ = (1 + P.ell * P.h / P.ν) *
          ‖C.gradF (P.β • canonicalLiftYStar P C x)‖ := by rfl

/-- Paper equation (15) for the explicit envelope-gradient candidate.  Once
`canonicalLiftPhi_grad` proves that this candidate is the actual gradient of the value function,
this theorem fills `LiftPropertiesCertificate.stationarity_transfer` without any additional
analytic assumption. -/
theorem canonicalLift_stationarity_transfer_candidate {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    P.γ * P.q / (1 + P.ell * P.h / P.ν) *
      ‖C.gradF ((P.β * P.γ) • x)‖ ≤ ‖canonicalLiftGradPhi P C x‖ := by
  have hcomp := canonicalLift_chain_gradient_comparison P C x
  have hnu : 0 < P.ν := lift_nu_pos P
  have hden : 0 < 1 + P.ell * P.h / P.ν := by
    have hl0 : 0 ≤ P.ell := P.ell_nonneg
    have hfrac : 0 ≤ P.ell * P.h / P.ν :=
      div_nonneg (mul_nonneg hl0 (le_of_lt P.h_pos)) (le_of_lt hnu)
    linarith
  have hγq : 0 < P.γ * P.q := mul_pos P.γ_pos P.q_pos
  have hnorm :
      ‖canonicalLiftGradPhi P C x‖ =
        (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar P C x)‖ := by
    rw [canonicalLiftGradPhi_eq_scaled_chain P C x, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγq]
  rw [hnorm]
  have hscaled := mul_le_mul_of_nonneg_left hcomp (le_of_lt hγq)
  have hdiv :
      ((P.γ * P.q) * ‖C.gradF ((P.β * P.γ) • x)‖) /
          (1 + P.ell * P.h / P.ν) ≤
        (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar P C x)‖ := by
    apply (div_le_iff₀ hden).2
    calc
      (P.γ * P.q) * ‖C.gradF ((P.β * P.γ) • x)‖
          ≤ (P.γ * P.q) *
              ((1 + P.ell * P.h / P.ν) *
                ‖C.gradF (P.β • canonicalLiftYStar P C x)‖) := hscaled
      _ = (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar P C x)‖ *
            (1 + P.ell * P.h / P.ν) := by ring
  simpa [div_mul_eq_mul_div, mul_assoc] using hdiv



theorem canonicalLiftGradPhi_lipschitz {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (x x' : Vec T) :
    ‖canonicalLiftGradPhi P C x - canonicalLiftGradPhi P C x'‖ ≤
      (P.ν * P.γ ^ 2 * P.ell * P.h / P.μ) * ‖x - x'‖ := by
  have hb : 0 < P.β := div_pos P.h_pos P.q_pos
  have hq : 0 ≤ P.γ * P.q := le_of_lt (mul_pos P.γ_pos P.q_pos)
  have hl : 0 ≤ P.ell * P.β := mul_nonneg (P.ell_nonneg) (le_of_lt hb)
  rw [canonicalLiftGradPhi_eq_scaled_chain, canonicalLiftGradPhi_eq_scaled_chain,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  calc
    (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar P C x) -
        C.gradF (P.β • canonicalLiftYStar P C x')‖
      ≤ (P.γ * P.q) * (P.ell * ‖P.β • canonicalLiftYStar P C x -
          P.β • canonicalLiftYStar P C x'‖) :=
        mul_le_mul_of_nonneg_left (C.grad_lipschitz _ _) hq
    _ = (P.γ * P.q) * ((P.ell * P.β) *
        ‖canonicalLiftYStar P C x - canonicalLiftYStar P C x'‖) := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb]; ring
    _ ≤ (P.γ * P.q) * ((P.ell * P.β) *
        ((P.ν * P.γ / P.μ) * ‖x - x'‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (canonicalLiftYStar_lipschitz P C x x') hl) hq
    _ = (P.ν * P.γ ^ 2 * P.ell * P.h / P.μ) * ‖x - x'‖ := by
        calc
          _ = (P.ν * P.γ ^ 2 * P.ell * (P.q * P.β) / P.μ) * ‖x - x'‖ := by ring
          _ = _ := by rw [P.q_mul_beta]

/-- Equation (30)'s curvature constant under the displayed calibration bounds. -/
theorem canonicalLiftGradPhi_lipschitz_calibrated {T : ℕ}
    (P : LiftParameters) (C : Base T P.ell) (M : ℝ)
    (hν : P.ν ≤ 5 * P.μ / 4) (hh : P.ell * P.h ≤ P.μ / 4)
    (hγ : P.γ ^ 2 = M / (4 * P.μ)) (x x' : Vec T) :
    ‖canonicalLiftGradPhi P C x - canonicalLiftGradPhi P C x'‖ ≤
      (5 * M / 64) * ‖x - x'‖ := by
  have hcoeff : P.ν * P.γ ^ 2 * P.ell * P.h / P.μ ≤ 5 * M / 64 := by
    calc
      _ = P.ν * (P.ell * P.h) * P.γ ^ 2 / P.μ := by ring
      _ ≤ (5 * P.μ / 4) * (P.μ / 4) * P.γ ^ 2 / P.μ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt P.μ_pos)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul hν hh (mul_nonneg (P.ell_nonneg) (le_of_lt P.h_pos))
          (by have := P.μ_pos; positivity)
      _ = 5 * M / 64 := by rw [hγ]; field_simp [ne_of_gt P.μ_pos]; ring
  exact (canonicalLiftGradPhi_lipschitz P C x x').trans
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))


/-- Equation (18), in the manuscript's direction and with its literal output map. -/
theorem stationarity_transfer {T : ℕ} (P : LiftParameters) (C : Base T P.ell) (x : Vec T) :
    ‖C.gradF ((P.β * P.γ) • x)‖ ≤
      ((1 + P.ell * P.h / P.ν) / (P.γ * P.q)) * ‖gradient (canonicalLiftPhi P C) x‖ := by
  rw [(canonicalLiftPhi_grad P C x).gradient, canonicalLiftGradPhi_eq_scaled_chain]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos P.γ_pos P.q_pos)]
  convert canonicalLift_chain_gradient_comparison P C x using 1
  field_simp [ne_of_gt P.γ_pos, ne_of_gt P.q_pos]
  ring

theorem primal_lower_bound {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (hb : BddBelow (Set.range C.H)) (x : Vec T) :
    P.α * sInf (Set.range C.H) ≤ canonicalLiftPhi P C x := by
  have ha : 0 ≤ P.α := div_nonneg (sq_nonneg _) P.h_pos.le
  have hbase := mul_le_mul_of_nonneg_left
    (csInf_le hb (Set.mem_range_self ((P.β * P.γ) • x))) ha
  have hm := (primitive P C).yStar_maximizes x (P.γ • x)
  change liftedF P C x (P.γ • x) ≤ canonicalLiftPhi P C x at hm
  simpa [liftedF, smul_smul] using hbase.trans (by simpa [liftedF, smul_smul] using hm)

theorem primal_bddBelow {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (hb : BddBelow (Set.range C.H)) : BddBelow (Set.range (canonicalLiftPhi P C)) := by
  refine ⟨P.α * sInf (Set.range C.H), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact primal_lower_bound P C hb x

theorem primal_origin_upper {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (g : ℝ) (hg : ‖C.gradF 0‖ ≤ g) :
    canonicalLiftPhi P C 0 ≤ P.α * C.H 0 + P.q ^ 2 * g ^ 2 / (2 * P.μ) := by
  let y := canonicalLiftYStar P C 0
  have h := liftedF_mu_strong_concavity P C 0 0 y
  have hi := real_inner_le_norm (C.gradF 0) y
  have hb := mul_le_mul_of_nonneg_right hg (norm_nonneg y)
  have hq := mul_le_mul_of_nonneg_left (hi.trans hb) P.q_pos.le
  simp only [zero_smul, smul_zero, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, sub_zero, inner_sub_left, inner_zero_left,
    real_inner_smul_left] at h
  have hzero : liftedF P C 0 0 = P.α * C.H 0 := by simp [liftedF]
  rw [hzero] at h
  change canonicalLiftPhi P C 0 ≤ _ at h
  have he : (P.q ^ 2 * g ^ 2 / (2 * P.μ)) * (2 * P.μ) = P.q ^ 2 * g ^ 2 :=
    div_mul_cancel₀ _ (by have := P.μ_pos; positivity)
  have hsq := sq_nonneg (P.μ * ‖y‖ - P.q * g)
  have hc : P.q * g * ‖y‖ - P.μ / 2 * ‖y‖ ^ 2 ≤ P.q ^ 2 * g ^ 2 / (2 * P.μ) := by
    nlinarith [P.μ_pos]
  linarith

/-- Equation (17), with actual finite infima, for every bounded-below base function. -/
theorem primal_gap {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (D g : ℝ) (hb : BddBelow (Set.range C.H))
    (hD : C.H 0 - sInf (Set.range C.H) ≤ D) (hg : ‖C.gradF 0‖ ≤ g) :
    canonicalLiftPhi P C 0 - sInf (Set.range (canonicalLiftPhi P C)) ≤
      P.α * D + P.q ^ 2 * g ^ 2 / (2 * P.μ) := by
  have hlo : P.α * sInf (Set.range C.H) ≤ sInf (Set.range (canonicalLiftPhi P C)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact primal_lower_bound P C hb x
  have hu := primal_origin_upper P C g hg
  have hd := mul_le_mul_of_nonneg_left hD (show 0 ≤ P.α from div_nonneg (sq_nonneg _) P.h_pos.le)
  nlinarith

/-- Direct entry point from the manuscript's scalar `C²` function and its actual gradient. -/
def Base.ofC2 {T : ℕ} (ell : ℝ) (H : Vec T → ℝ) (hC : ContDiff ℝ 2 H)
    (hl : ∀ u v, ‖gradient H u - gradient H v‖ ≤ ell * ‖u - v‖) : Base T ell where
  H := H
  gradF := gradient H
  grad_is_gradient := fun u => (hC.differentiable (by norm_num) u).hasGradientAt
  grad_lipschitz := hl

/-- Equation (34), without a compact-domain or supplied-maximizer assumption. -/
theorem inner_initialization_gap {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (g : ℝ) (hg : ‖C.gradF 0‖ ≤ g) :
    0 ≤ canonicalLiftPhi P C 0 - liftedF P C 0 0 ∧
    canonicalLiftPhi P C 0 - liftedF P C 0 0 ≤ P.q ^ 2 * g ^ 2 / (2 * P.μ) := by
  have hl := (primitive P C).yStar_maximizes 0 0
  have hu := primal_origin_upper P C g hg
  have hz : liftedF P C 0 0 = P.α * C.H 0 := by simp [liftedF]
  change liftedF P C 0 0 ≤ canonicalLiftPhi P C 0 at hl
  rw [hz] at hl ⊢
  constructor <;> linarith

/-- The deterministic part of Proposition 3.1, including actual value and gradient semantics.
The oracle conclusions are `liftedField_unbiased`, `lifted_variance`, and
`liftedField_averaged_smooth` in `ManuscriptLiftOracle`. -/
theorem proposition31 {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (D g : ℝ) (hb : BddBelow (Set.range C.H))
    (hD : C.H 0 - sInf (Set.range C.H) ≤ D) (hg : ‖C.gradF 0‖ ≤ g) :
    JointPrimitive (primitive P C).jointFunction (P.ν * (1 + P.γ ^ 2) + P.ell * P.h) P.μ ∧
    BddBelow (Set.range (canonicalLiftPhi P C)) ∧
    canonicalLiftPhi P C 0 - sInf (Set.range (canonicalLiftPhi P C)) ≤
      P.α * D + P.q ^ 2 * g ^ 2 / (2 * P.μ) ∧
    (∀ x, canonicalLiftPhi P C x = sSup (Set.range (liftedF P C x))) ∧
    (∀ x, ‖C.gradF ((P.β * P.γ) • x)‖ ≤
      ((1 + P.ell * P.h / P.ν) / (P.γ * P.q)) * ‖gradient (canonicalLiftPhi P C) x‖) :=
  ⟨(primitive P C).jointPrimitive, primal_bddBelow P C hb,
    primal_gap P C D g hb hD hg, canonicalLiftPhi_eq_sup P C, stationarity_transfer P C⟩

end NCSCPureStochasticLB.PaperExact.GeneralLift
