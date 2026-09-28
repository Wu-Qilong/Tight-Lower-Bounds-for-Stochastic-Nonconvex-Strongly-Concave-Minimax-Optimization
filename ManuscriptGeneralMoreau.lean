import ManuscriptAlgorithmRepresentation

noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact

/-- General finite-dimensional differentiable weakly convex primal data.
No small Lipschitz constant, minimizer, or envelope regularity is assumed. -/
structure WeaklyConvexPrimal (d : ℕ) where
  F : Vec d → ℝ
  g : Vec d → Vec d
  M : ℝ
  M_pos : 0 < M
  grad_spec : ∀ x, HasGradientAt F (g x) x
  bddBelow : BddBelow (Set.range F)
  lower_model : ∀ u v, F u + @inner ℝ (Vec d) _ (g u) (v - u) -
    (M / 2) * ‖v - u‖ ^ 2 ≤ F v

namespace WeaklyConvexPrimal
variable {d : ℕ}

def cost (P : WeaklyConvexPrimal d) (x u : Vec d) : ℝ := P.F u + P.M * ‖u - x‖ ^ 2

theorem continuous_F (P : WeaklyConvexPrimal d) : Continuous P.F :=
  continuous_iff_continuousAt.mpr (fun x => (P.grad_spec x).continuousAt)

theorem cost_continuous (P : WeaklyConvexPrimal d) (x : Vec d) : Continuous (P.cost x) :=
  P.continuous_F.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))

/-- Compactness and a global lower bound give a proximal minimizer. -/
theorem exists_minimizer (P : WeaklyConvexPrimal d) (x : Vec d) :
    ∃ u, ∀ v, P.cost x u ≤ P.cost x v := by
  obtain ⟨b, hb⟩ := P.bddBelow
  have hb' : ∀ v, b ≤ P.F v := fun v => hb ⟨v, rfl⟩
  let R : ℝ := max 1 ((P.F x - b) / P.M + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hR' : (P.F x - b) / P.M + 1 ≤ R := le_max_right _ _
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, by simp [Metric.mem_closedBall, show 0 ≤ R by linarith]⟩
    (P.cost_continuous x).continuousOn
  refine ⟨u, fun v => ?_⟩
  by_cases hv : v ∈ Metric.closedBall x R
  · exact hmin hv
  · have hx : x ∈ Metric.closedBall x R := by
      simp [Metric.mem_closedBall, show 0 ≤ R by linarith]
    have hv' : R < ‖v - x‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    have hdiv : P.F x - b = P.M * ((P.F x - b) / P.M) := by
      field_simp [ne_of_gt P.M_pos]
    have hm := mul_le_mul_of_nonneg_left hR' (le_of_lt P.M_pos)
    have hs : R ≤ ‖v - x‖ ^ 2 := by nlinarith [sq_nonneg (‖v - x‖ - 1)]
    have hm' := mul_le_mul_of_nonneg_left hs (le_of_lt P.M_pos)
    have hh : P.cost x u ≤ P.cost x x := hmin hx
    simp only [cost, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero] at hh
    unfold cost
    nlinarith [hb' v, P.M_pos]

def prox (P : WeaklyConvexPrimal d) (x : Vec d) : Vec d := (P.exists_minimizer x).choose

theorem prox_minimizes (P : WeaklyConvexPrimal d) (x u : Vec d) :
    P.cost x (P.prox x) ≤ P.cost x u := (P.exists_minimizer x).choose_spec u

theorem cost_hasGradient (P : WeaklyConvexPrimal d) (x u : Vec d) :
    HasGradientAt (P.cost x) (P.g u + (2 * P.M) • (u - x)) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (P.grad_spec u).hasFDerivAt.add
    ((((hasFDerivAt_id u).sub_const x).norm_sq).const_mul P.M) using 1
  ext v
  simp [cost, InnerProductSpace.toDual_apply, inner_add_left, real_inner_smul_left]
  ring

theorem prox_first_order (P : WeaklyConvexPrimal d) (x : Vec d) :
    P.g (P.prox x) = (2 * P.M) • (x - P.prox x) := by
  have hmin : IsLocalMin (P.cost x) (P.prox x) := Filter.Eventually.of_forall (P.prox_minimizes x)
  have hz := hmin.hasFDerivAt_eq_zero (P.cost_hasGradient x (P.prox x)).hasFDerivAt
  have he : P.g (P.prox x) + (2 * P.M) • (P.prox x - x) = 0 := by
    apply (InnerProductSpace.toDual ℝ (Vec d)).injective
    simpa using hz
  calc
    P.g (P.prox x) = -((2 * P.M) • (P.prox x - x)) := eq_neg_of_add_eq_zero_left he
    _ = _ := by module

def envelope (P : WeaklyConvexPrimal d) (x : Vec d) : ℝ := P.cost x (P.prox x)
def envelopeGrad (P : WeaklyConvexPrimal d) (x : Vec d) : Vec d := (2 * P.M) • (x - P.prox x)

theorem envelopeGrad_eq (P : WeaklyConvexPrimal d) (x : Vec d) :
    P.envelopeGrad x = P.g (P.prox x) := (P.prox_first_order x).symm

theorem prox_quadratic_growth (P : WeaklyConvexPrimal d) (x u : Vec d) :
    P.envelope x + (P.M / 2) * ‖u - P.prox x‖ ^ 2 ≤ P.cost x u := by
  have hl := P.lower_model (P.prox x) u
  have hv : u - x = (P.prox x - x) + (u - P.prox x) := by module
  have hn : ‖u - x‖ ^ 2 = ‖P.prox x - x‖ ^ 2 +
      2 * @inner ℝ (Vec d) _ (P.prox x - x) (u - P.prox x) + ‖u - P.prox x‖ ^ 2 := by
    rw [hv, norm_add_sq_real]
  have hi : @inner ℝ (Vec d) _ (P.g (P.prox x)) (u - P.prox x) =
      -(2 * P.M) * @inner ℝ (Vec d) _ (P.prox x - x) (u - P.prox x) := by
    rw [P.prox_first_order, real_inner_smul_left]
    have he : x - P.prox x = -(P.prox x - x) := by module
    rw [he, inner_neg_left]; ring
  rw [hi] at hl
  unfold envelope cost
  rw [hn]
  nlinarith

theorem prox_unique (P : WeaklyConvexPrimal d) (x u : Vec d)
    (hu : ∀ v, P.cost x u ≤ P.cost x v) : u = P.prox x := by
  have h := P.prox_quadratic_growth x u
  have hm := hu (P.prox x)
  change P.cost x (P.prox x) + (P.M / 2) * ‖u - P.prox x‖ ^ 2 ≤ P.cost x u at h
  have hs : ‖u - P.prox x‖ ^ 2 = 0 := by nlinarith [P.M_pos, sq_nonneg ‖u - P.prox x‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

theorem existsUnique_minimizer (P : WeaklyConvexPrimal d) (x : Vec d) :
    ∃! u, ∀ v, P.cost x u ≤ P.cost x v :=
  ⟨P.prox x, P.prox_minimizes x, fun u hu => P.prox_unique x u hu⟩

theorem envelope_eq_inf (P : WeaklyConvexPrimal d) (x : Vec d) :
    P.envelope x = sInf (Set.range (P.cost x)) := by
  have hb : BddBelow (Set.range (P.cost x)) := ⟨P.envelope x, by
    rintro _ ⟨u, rfl⟩; exact P.prox_minimizes x u⟩
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨u, rfl⟩; exact P.prox_minimizes x u
  · exact csInf_le hb ⟨P.prox x, rfl⟩

theorem cost_increment (P : WeaklyConvexPrimal d) (x y u : Vec d) :
    P.cost y u - P.cost x u =
      @inner ℝ (Vec d) _ ((2 * P.M) • (x - u)) (y - x) + P.M * ‖y - x‖ ^ 2 := by
  have hv : y - u = (x - u) + (y - x) := by module
  have hn : ‖y - u‖ ^ 2 = ‖x - u‖ ^ 2 + 2 * @inner ℝ (Vec d) _ (x - u) (y - x) + ‖y - x‖ ^ 2 := by
    rw [hv, norm_add_sq_real]
  unfold cost
  rw [norm_sub_rev u y, norm_sub_rev u x, hn, real_inner_smul_left]
  ring

theorem prox_cocoercive (P : WeaklyConvexPrimal d) (x y : Vec d) :
    ‖P.prox y - P.prox x‖ ^ 2 ≤
      2 * @inner ℝ (Vec d) _ (P.prox y - P.prox x) (y - x) := by
  have hx := P.prox_quadratic_growth x (P.prox y)
  have hy := P.prox_quadratic_growth y (P.prox x)
  rw [norm_sub_rev (P.prox x) (P.prox y)] at hy
  have h1 := P.cost_increment x y (P.prox x)
  have h2 := P.cost_increment x y (P.prox y)
  have hi : @inner ℝ (Vec d) _ ((2 * P.M) • (x - P.prox x)) (y - x) -
      @inner ℝ (Vec d) _ ((2 * P.M) • (x - P.prox y)) (y - x) =
      (2 * P.M) * @inner ℝ (Vec d) _ (P.prox y - P.prox x) (y - x) := by
    rw [← inner_sub_left, ← real_inner_smul_left]
    congr 1
    module
  unfold envelope at hx hy
  nlinarith [P.M_pos]

theorem prox_lipschitz (P : WeaklyConvexPrimal d) (x y : Vec d) :
    ‖P.prox x - P.prox y‖ ≤ 2 * ‖x - y‖ := by
  have h := P.prox_cocoercive y x
  have h' := real_inner_le_norm (P.prox x - P.prox y) (x - y)
  have hn := norm_nonneg (P.prox x - P.prox y)
  by_cases hz : ‖P.prox x - P.prox y‖ = 0
  · rw [hz]; positivity
  · apply (mul_le_mul_right (lt_of_le_of_ne hn (Ne.symm hz))).mp
    nlinarith

theorem prox_continuous (P : WeaklyConvexPrimal d) : Continuous P.prox := by
  have h : LipschitzWith 2 P.prox := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using P.prox_lipschitz x y
  exact h.continuous

theorem envelopeGrad_continuous (P : WeaklyConvexPrimal d) : Continuous P.envelopeGrad :=
  (continuous_id.sub P.prox_continuous).const_smul _

theorem envelopeGrad_lipschitz (P : WeaklyConvexPrimal d) (x y : Vec d) :
    ‖P.envelopeGrad x - P.envelopeGrad y‖ ≤ (2 * P.M) * ‖x - y‖ := by
  have hc := P.prox_cocoercive y x
  have hn := norm_sub_sq_real (x - y) (P.prox x - P.prox y)
  have hi := real_inner_comm (x - y) (P.prox x - P.prox y)
  have he : (x - P.prox x) - (y - P.prox y) = (x - y) - (P.prox x - P.prox y) := by module
  have hb : ‖(x - P.prox x) - (y - P.prox y)‖ ≤ ‖x - y‖ := by
    rw [he]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  have hg : P.envelopeGrad x - P.envelopeGrad y =
      (2 * P.M) • ((x - P.prox x) - (y - P.prox y)) := by unfold envelopeGrad; module
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos (by have := P.M_pos; positivity)]
  exact mul_le_mul_of_nonneg_left hb (by have := P.M_pos; positivity)

theorem envelope_remainder (P : WeaklyConvexPrimal d) (x y : Vec d) :
    ‖P.envelope y - P.envelope x - @inner ℝ (Vec d) _ (P.envelopeGrad x) (y - x)‖ ≤
      (4 * P.M) * ‖y - x‖ ^ 2 := by
  have hup := P.prox_minimizes y (P.prox x)
  have hlo := P.prox_minimizes x (P.prox y)
  have hinc := P.cost_increment x y (P.prox x)
  have hinc' := P.cost_increment x y (P.prox y)
  have hi : @inner ℝ (Vec d) _ (P.envelopeGrad x) (y - x) -
      @inner ℝ (Vec d) _ ((2 * P.M) • (x - P.prox y)) (y - x) =
      @inner ℝ (Vec d) _ ((2 * P.M) • (P.prox y - P.prox x)) (y - x) := by
    rw [← inner_sub_left]
    congr 1
    unfold envelopeGrad
    module
  have hb : @inner ℝ (Vec d) _ ((2 * P.M) • (P.prox y - P.prox x)) (y - x) ≤
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
    @inner ℝ (Vec d) _ (P.envelopeGrad x) (y - x) + P.M * ‖y - x‖ ^ 2 at hinc
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hn : 0 ≤ P.M * ‖y - x‖ ^ 2 := mul_nonneg (le_of_lt P.M_pos) (sq_nonneg _)
  constructor <;> nlinarith

theorem envelope_hasGradient (P : WeaklyConvexPrimal d) (x : Vec d) :
    HasGradientAt P.envelope (P.envelopeGrad x) x := by
  rw [hasGradientAt_iff_tendsto]
  have ht : Filter.Tendsto (fun y : Vec d => ‖y - x‖) (nhds x) (nhds 0) := by
    have hc : ContinuousAt (fun y : Vec d => ‖y - x‖) x := (continuousAt_id.sub continuousAt_const).norm
    simpa only [ContinuousAt, sub_self, norm_zero] using hc
  have hKt : Filter.Tendsto (fun y : Vec d => (4 * P.M) * ‖y - x‖) (nhds x) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ht)
  apply squeeze_zero
  · intro y; exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · intro y
    have hr := P.envelope_remainder x y
    change ‖y - x‖⁻¹ * ‖P.envelope y - P.envelope x -
      @inner ℝ (Vec d) _ (P.envelopeGrad x) (y - x)‖ ≤ (4 * P.M) * ‖y - x‖
    by_cases hd : ‖y - x‖ = 0
    · simp [hd]
    · have hm := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg (y - x)))
      calc
        _ ≤ ‖y - x‖⁻¹ * ((4 * P.M) * ‖y - x‖ ^ 2) := hm
        _ = (4 * P.M) * ‖y - x‖ := by field_simp [hd]; ring
  · exact hKt

theorem infEnvelope_hasGradient (P : WeaklyConvexPrimal d) (x : Vec d) :
    HasGradientAt (fun z => sInf (Set.range (P.cost z))) (P.envelopeGrad x) x := by
  have he : (fun z => sInf (Set.range (P.cost z))) = P.envelope :=
    funext (fun z => (P.envelope_eq_inf z).symm)
  rw [he]
  exact P.envelope_hasGradient x

theorem infEnvelope_gradient (P : WeaklyConvexPrimal d) :
    gradient (fun z => sInf (Set.range (P.cost z))) = P.envelopeGrad :=
  funext (fun x => (P.infEnvelope_hasGradient x).gradient)

theorem infEnvelope_gradient_measurable (P : WeaklyConvexPrimal d) :
    Measurable (gradient (fun z => sInf (Set.range (P.cost z)))) := by
  rw [P.infEnvelope_gradient]
  exact P.envelopeGrad_continuous.measurable

end WeaklyConvexPrimal

/-- In finite dimensions the totalized derivative is Borel measurable. -/
theorem measurable_gradient_vec {d : ℕ} (F : Vec d → ℝ) : Measurable (gradient F) := by
  exact (InnerProductSpace.toDual ℝ (Vec d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ F)

theorem MeasuredOracle.Instance.field_measurable (I : MeasuredOracle.Instance)
    (m : StationarityObjective) (M : ℝ) : Measurable (I.field m M) := by
  cases m with
  | primal =>
    have he : I.population.gradPhi = gradient I.population.Phi :=
      funext (fun x => (I.population.gradPhi_spec x).gradient.symm)
    change Measurable I.population.gradPhi
    rw [he]
    exact measurable_gradient_vec _
  | moreau => exact measurable_gradient_vec _

theorem MeasuredOracle.Instance.regularFor_iff_oracle (I : MeasuredOracle.Instance)
    (m : StationarityObjective) (M : ℝ) :
    I.RegularFor m M ↔ Rectangular.JointlyMeasurable I.oracle :=
  ⟨And.left, fun h => ⟨h, I.field_measurable m M⟩⟩

/-- Descent lower bound with the sharp one-half coefficient, for arbitrary smooth functions. -/
theorem gradient_lower_model {d : ℕ} (F : Vec d → ℝ) (g : Vec d → Vec d) (M : ℝ)
    (hg : ∀ x, HasGradientAt F (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ M * ‖x - y‖) (u v : Vec d) :
    F u + @inner ℝ (Vec d) _ (g u) (v - u) - M / 2 * ‖v - u‖ ^ 2 ≤ F v := by
  let w := v - u
  let h : ℝ → ℝ := fun t => F (u + t • w) - F u -
    t * @inner ℝ (Vec d) _ (g u) w + M / 2 * t ^ 2 * ‖w‖ ^ 2
  let h' : ℝ → ℝ := fun t => @inner ℝ (Vec d) _ (g (u + t • w) - g u) w +
    M * t * ‖w‖ ^ 2
  have hd : ∀ t, HasDerivAt h (h' t) t := by
    intro t
    have hp : HasDerivAt (fun s : ℝ => u + s • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add u
    have hh := (((hg (u + t • w)).hasFDerivAt.comp_hasDerivAt t hp).sub_const (F u)).sub
      ((hasDerivAt_id t).mul_const (@inner ℝ (Vec d) _ (g u) w))
    convert hh.add ((((hasDerivAt_id t).pow 2).const_mul (M / 2)).mul_const (‖w‖ ^ 2)) using 1
    simp [h, h', InnerProductSpace.toDual_apply, inner_sub_left]
    ring_nf
    simp
  have hpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ h' t := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hb := hlip (u + t • w) u
    have hi := real_inner_le_norm (-(g (u + t • w) - g u)) w
    rw [inner_neg_left, norm_neg] at hi
    have he : u + t • w - u = t • w := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hb
    have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg w)
    change 0 ≤ @inner ℝ (Vec d) _ (g (u + t • w) - g u) w + M * t * ‖w‖ ^ 2
    nlinarith
  have hm : MonotoneOn h (Set.Icc 0 1) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc _ _) (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) hpos
  have h01 := hm (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) zero_le_one
  have he : u + (v - u) = v := by module
  simp only [h, w, zero_smul, add_zero, zero_mul, sub_self, one_smul, one_mul,
    zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, he] at h01
  linarith

namespace Rectangular.Population
variable {dx dy : ℕ}

/-- At an attained maximum the supplied derivative of the value equals the x-partial. -/
theorem gradPhi_eq_at_max (P : Population dx dy) (x : Vec dx) (y : Vec dy)
    (he : P.Phi x = P.f x y) (hmax : ∀ z, P.f z y ≤ P.Phi z) :
    P.gradPhi x = P.gradX x y := by
  have hm : IsLocalMin (fun z => P.Phi z - P.f z y) x :=
    Filter.Eventually.of_forall (fun z => by dsimp; rw [he]; linarith [hmax z])
  have hd := (P.gradPhi_spec x).hasFDerivAt.sub (P.gradX_spec x y).hasFDerivAt
  have hz := hm.hasFDerivAt_eq_zero hd
  apply (InnerProductSpace.toDual ℝ (Vec dx)).injective
  exact sub_eq_zero.mp hz

theorem lower_model_of_slice_lipschitz (P : Population dx dy) (M : ℝ)
    (hlip : ∀ y x x', ‖P.gradX x y - P.gradX x' y‖ ≤ M * ‖x - x'‖)
    (u v : Vec dx) :
    P.Phi u + @inner ℝ (Vec dx) _ (P.gradPhi u) (v - u) - M / 2 * ‖v - u‖ ^ 2 ≤ P.Phi v := by
  obtain ⟨y, he, hy⟩ := P.value_is_max u
  have hmax : ∀ z, P.f z y ≤ P.Phi z := fun z => (P.value_is_max z).choose_spec.2 y
  have hg := P.gradPhi_eq_at_max u y he hmax
  have hb := gradient_lower_model (fun z => P.f z y) (fun z => P.gradX z y) M
    (fun z => P.gradX_spec z y) (hlip y) u v
  rw [he, hg]
  exact hb.trans (hmax v)

def weaklyConvexPrimal (P : Population dx dy) (M : ℝ) (hM : 0 < M)
    (hb : BddBelow (Set.range P.Phi))
    (hlip : ∀ y x x', ‖P.gradX x y - P.gradX x' y‖ ≤ M * ‖x - x'‖) : WeaklyConvexPrimal dx where
  F := P.Phi
  g := P.gradPhi
  M := M
  M_pos := hM
  grad_spec := P.gradPhi_spec
  bddBelow := hb
  lower_model := P.lower_model_of_slice_lipschitz M hlip

end Rectangular.Population

namespace MeasuredOracle.Instance

theorem PopulationValid.slice_lipschitz {I : Instance} {M μ Δ : ℝ}
    (h : I.PopulationValid M μ Δ) (y : Vec I.dy) (x x' : Vec I.dx) :
    ‖I.population.gradX x y - I.population.gradX x' y‖ ≤ M * ‖x - x'‖ := by
  have hh := h.1 x y x' y
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_sq (norm_nonneg _)] at hh
  apply le_trans _ hh
  calc
    _ = Real.sqrt (‖I.population.gradX x y - I.population.gradX x' y‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

/-- The general Moreau construction applies to every valid declared population,
not just the calibrated hard family. -/
def populationMoreau (I : Instance) (M μ Δ : ℝ) (hM : 0 < M)
    (h : I.PopulationValid M μ Δ) : WeaklyConvexPrimal I.dx :=
  I.population.weaklyConvexPrimal M hM h.2.2.2 h.slice_lipschitz

theorem moreau_existsUnique (I : Instance) (M μ Δ : ℝ) (hM : 0 < M)
    (h : I.PopulationValid M μ Δ) (x : Vec I.dx) :
    ∃! u, ∀ v, I.population.Phi u + M * ‖u - x‖ ^ 2 ≤
      I.population.Phi v + M * ‖v - x‖ ^ 2 :=
  (I.populationMoreau M μ Δ hM h).existsUnique_minimizer x

theorem moreau_hasGradient (I : Instance) (M μ Δ : ℝ) (hM : 0 < M)
    (h : I.PopulationValid M μ Δ) (x : Vec I.dx) :
    HasGradientAt (fun z => sInf (Set.range (fun v => I.population.Phi v + M * ‖v - z‖ ^ 2)))
      ((2 * M) • (x - (I.populationMoreau M μ Δ hM h).prox x)) x :=
  (I.populationMoreau M μ Δ hM h).infEnvelope_hasGradient x

theorem moreau_field_eq (I : Instance) (M μ Δ : ℝ) (hM : 0 < M)
    (h : I.PopulationValid M μ Δ) :
    I.field .moreau M = (I.populationMoreau M μ Δ hM h).envelopeGrad :=
  (I.populationMoreau M μ Δ hM h).infEnvelope_gradient

theorem moreau_field_lipschitz (I : Instance) (M μ Δ : ℝ) (hM : 0 < M)
    (h : I.PopulationValid M μ Δ) (x y : Vec I.dx) :
    ‖I.field .moreau M x - I.field .moreau M y‖ ≤ (2 * M) * ‖x - y‖ := by
  rw [I.moreau_field_eq M μ Δ hM h]
  exact (I.populationMoreau M μ Δ hM h).envelopeGrad_lipschitz x y

end MeasuredOracle.Instance

theorem MeasuredOracle.risk_eq_iterated_of_jointlyMeasurable {K : ℕ}
    (A : Rectangular.Family K) (c : StationarityCriterion) (m : StationarityObjective)
    (M : ℝ) (N : ℕ) (I : MeasuredOracle.Instance)
    (hO : Rectangular.JointlyMeasurable I.oracle) :
    MeasuredOracle.risk A c m M N I =
      ∫⁻ ω, ∫⁻ w, MeasuredOracle.loss (A.policy I.dx I.dy) c I.oracle (I.field m M) N (ω, w)
        ∂iidRoundMeasure I.law N ∂A.law I.dx I.dy :=
  MeasuredOracle.risk_eq_iterated A c m M N I hO (I.field_measurable m M)

universe u

theorem MemoryModel.bv_complexity_lower_jointlyMeasurable (P : ManuscriptBVProblem)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      MemoryModel.complexity.{u}
        (fun I => I.ValidBV P.M P.μ P.Δ P.σ ∧ Rectangular.JointlyMeasurable I.oracle)
        K c m P.M P.ε := by
  simpa only [MeasuredOracle.Instance.regularFor_iff_oracle] using
    (MemoryModel.bv_complexity_lower.{u} P hK c m)

theorem MemoryModel.as_complexity_lower_jointlyMeasurable (P : ManuscriptASProblem)
    {K : ℕ} (hK : 1 ≤ K) (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      MemoryModel.complexity.{u}
        (fun I => I.ValidAS P.M P.μ P.Δ P.σ ∧ Rectangular.JointlyMeasurable I.oracle)
        K c m P.M P.ε := by
  simpa only [MeasuredOracle.Instance.regularFor_iff_oracle] using
    (MemoryModel.as_complexity_lower.{u} P hK c m)

end NCSCPureStochasticLB.PaperExact
