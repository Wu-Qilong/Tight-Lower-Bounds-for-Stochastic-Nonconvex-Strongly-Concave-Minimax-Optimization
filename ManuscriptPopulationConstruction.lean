import ManuscriptGeneralMoreau

noncomputable section
namespace NCSCPureStochasticLB.PaperExact

/-- Primitive minimax data: no value function, maximizer, or value derivative is supplied. -/
structure SmoothStronglyConcave (dx dy : ℕ) where
  f : Vec dx → Vec dy → ℝ
  gradX : Vec dx → Vec dy → Vec dx
  gradY : Vec dx → Vec dy → Vec dy
  M : ℝ
  μ : ℝ
  M_pos : 0 < M
  μ_pos : 0 < μ
  gradX_spec : ∀ x y, HasGradientAt (fun z => f z y) (gradX x y) x
  gradY_spec : ∀ x y, HasGradientAt (f x) (gradY x y) y
  smooth : ∀ x y x' y',
    Real.sqrt (‖gradX x y - gradX x' y'‖ ^ 2 + ‖gradY x y - gradY x' y'‖ ^ 2) ≤
      M * Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)
  stronglyConcave : ∀ x y y', f x y' ≤ f x y +
    @inner ℝ (Vec dy) _ (gradY x y) (y' - y) - μ / 2 * ‖y' - y‖ ^ 2

namespace SmoothStronglyConcave
variable {dx dy : ℕ}

/-- A convenience constructor from a scalar function and its canonical partial gradients. -/
def ofDifferentiable (f : Vec dx → Vec dy → ℝ) (M μ : ℝ) (hM : 0 < M) (hμ : 0 < μ)
    (hx : ∀ x y, DifferentiableAt ℝ (fun z => f z y) x)
    (hy : ∀ x y, DifferentiableAt ℝ (f x) y)
    (hs : ∀ x y x' y',
      Real.sqrt (‖gradient (fun z => f z y) x - gradient (fun z => f z y') x'‖ ^ 2 +
        ‖gradient (f x) y - gradient (f x') y'‖ ^ 2) ≤
      M * Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2))
    (hc : ∀ x y y', f x y' ≤ f x y +
      @inner ℝ (Vec dy) _ (gradient (f x) y) (y' - y) - μ / 2 * ‖y' - y‖ ^ 2) :
    SmoothStronglyConcave dx dy where
  f := f
  gradX := fun x y => gradient (fun z => f z y) x
  gradY := fun x y => gradient (f x) y
  M := M
  μ := μ
  M_pos := hM
  μ_pos := hμ
  gradX_spec := fun x y => (hx x y).hasGradientAt
  gradY_spec := fun x y => (hy x y).hasGradientAt
  smooth := hs
  stronglyConcave := hc

theorem continuous_y (P : SmoothStronglyConcave dx dy) (x : Vec dx) : Continuous (P.f x) :=
  continuous_iff_continuousAt.mpr (fun y => (P.gradY_spec x y).continuousAt)

/-- Strong concavity makes the unconstrained maximization attain its maximum. -/
theorem exists_maximizer (P : SmoothStronglyConcave dx dy) (x : Vec dx) :
    ∃ y, ∀ v, P.f x v ≤ P.f x y := by
  let R : ℝ := max 1 (2 * ‖P.gradY x 0‖ / P.μ + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hR' : 2 * ‖P.gradY x 0‖ / P.μ + 1 ≤ R := le_max_right _ _
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall (0 : Vec dy) R).exists_isMaxOn
    ⟨0, by simp [Metric.mem_closedBall, show 0 ≤ R by linarith]⟩
    (P.continuous_y x).continuousOn
  refine ⟨y, fun v => ?_⟩
  by_cases hv : v ∈ Metric.closedBall (0 : Vec dy) R
  · exact hmax hv
  · have hz : (0 : Vec dy) ∈ Metric.closedBall (0 : Vec dy) R := by
      simp [Metric.mem_closedBall, show 0 ≤ R by linarith]
    have hv' : R < ‖v‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    have hc := P.stronglyConcave x 0 v
    rw [sub_zero] at hc
    have hi := real_inner_le_norm (P.gradY x 0) v
    have hd : P.μ * (2 * ‖P.gradY x 0‖ / P.μ) = 2 * ‖P.gradY x 0‖ := by
      field_simp [ne_of_gt P.μ_pos]
    have hb := mul_le_mul_of_nonneg_left hR' (le_of_lt P.μ_pos)
    have hb' := mul_le_mul_of_nonneg_left (le_of_lt hv') (le_of_lt P.μ_pos)
    have hlinear : 2 * ‖P.gradY x 0‖ ≤ P.μ * ‖v‖ := by nlinarith [P.μ_pos]
    have hquad := mul_le_mul_of_nonneg_right hlinear (norm_nonneg v)
    have hh : P.f x 0 ≤ P.f x y := hmax hz
    nlinarith

def yStar (P : SmoothStronglyConcave dx dy) (x : Vec dx) : Vec dy :=
  (P.exists_maximizer x).choose

theorem yStar_maximizes (P : SmoothStronglyConcave dx dy) (x : Vec dx) (y : Vec dy) :
    P.f x y ≤ P.f x (P.yStar x) := (P.exists_maximizer x).choose_spec y

theorem yStar_stationary (P : SmoothStronglyConcave dx dy) (x : Vec dx) :
    P.gradY x (P.yStar x) = 0 := by
  have hm : IsLocalMax (P.f x) (P.yStar x) :=
    Filter.Eventually.of_forall (P.yStar_maximizes x)
  have hz := hm.hasFDerivAt_eq_zero (P.gradY_spec x (P.yStar x)).hasFDerivAt
  apply (InnerProductSpace.toDual ℝ (Vec dy)).injective
  simpa using hz

theorem yStar_quadratic_growth (P : SmoothStronglyConcave dx dy) (x : Vec dx) (y : Vec dy) :
    P.f x y + P.μ / 2 * ‖y - P.yStar x‖ ^ 2 ≤ P.f x (P.yStar x) := by
  have h := P.stronglyConcave x (P.yStar x) y
  rw [P.yStar_stationary, inner_zero_left, add_zero] at h
  linarith

theorem yStar_unique (P : SmoothStronglyConcave dx dy) (x : Vec dx) (y : Vec dy)
    (hy : ∀ v, P.f x v ≤ P.f x y) : y = P.yStar x := by
  have h := P.yStar_quadratic_growth x y
  have h' := hy (P.yStar x)
  have hz : ‖y - P.yStar x‖ ^ 2 = 0 := by nlinarith [P.μ_pos, sq_nonneg ‖y - P.yStar x‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem existsUnique_maximizer (P : SmoothStronglyConcave dx dy) (x : Vec dx) :
    ∃! y, ∀ v, P.f x v ≤ P.f x y :=
  ⟨P.yStar x, P.yStar_maximizes x, fun y hy => P.yStar_unique x y hy⟩

theorem gradX_bound (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) (y y' : Vec dy) :
    ‖P.gradX x y - P.gradX x' y'‖ ≤
      P.M * Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  apply le_trans _ (P.smooth x y x' y')
  calc
    _ = Real.sqrt (‖P.gradX x y - P.gradX x' y'‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem gradY_bound (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) (y y' : Vec dy) :
    ‖P.gradY x y - P.gradY x' y'‖ ≤
      P.M * Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2) := by
  apply le_trans _ (P.smooth x y x' y')
  calc
    _ = Real.sqrt (‖P.gradY x y - P.gradY x' y'‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

theorem gradX_x_lipschitz (P : SmoothStronglyConcave dx dy) (y : Vec dy) (x x' : Vec dx) :
    ‖P.gradX x y - P.gradX x' y‖ ≤ P.M * ‖x - x'‖ := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq (norm_nonneg _)] using P.gradX_bound x x' y y

theorem gradX_y_lipschitz (P : SmoothStronglyConcave dx dy) (x : Vec dx) (y y' : Vec dy) :
    ‖P.gradX x y - P.gradX x y'‖ ≤ P.M * ‖y - y'‖ := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    Real.sqrt_sq (norm_nonneg _)] using P.gradX_bound x x y y'

theorem gradY_x_lipschitz (P : SmoothStronglyConcave dx dy) (y : Vec dy) (x x' : Vec dx) :
    ‖P.gradY x y - P.gradY x' y‖ ≤ P.M * ‖x - x'‖ := by
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq (norm_nonneg _)] using P.gradY_bound x x' y y

theorem gradY_strong_antimonotone (P : SmoothStronglyConcave dx dy) (x : Vec dx)
    (y y' : Vec dy) :
    P.μ * ‖y' - y‖ ^ 2 ≤ @inner ℝ (Vec dy) _ (P.gradY x y - P.gradY x y') (y' - y) := by
  have h := P.stronglyConcave x y y'
  have h' := P.stronglyConcave x y' y
  have he : y - y' = -(y' - y) := by module
  rw [he, inner_neg_right, norm_neg] at h'
  rw [inner_sub_left]
  linarith

theorem yStar_lipschitz (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) :
    ‖P.yStar x' - P.yStar x‖ ≤ (P.M / P.μ) * ‖x' - x‖ := by
  have h := P.gradY_strong_antimonotone x (P.yStar x) (P.yStar x')
  rw [P.yStar_stationary, zero_sub] at h
  have hb := P.gradY_x_lipschitz (P.yStar x') x x'
  rw [P.yStar_stationary, sub_zero, norm_sub_rev x x'] at hb
  have hi := real_inner_le_norm (-(P.gradY x (P.yStar x'))) (P.yStar x' - P.yStar x)
  rw [norm_neg] at hi
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (P.yStar x' - P.yStar x))
  by_cases hz : ‖P.yStar x' - P.yStar x‖ = 0
  · rw [hz]; have := P.M_pos; have := P.μ_pos; positivity
  · have hp : 0 < ‖P.yStar x' - P.yStar x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hc : P.μ * ‖P.yStar x' - P.yStar x‖ ≤ P.M * ‖x' - x‖ := by
      apply (mul_le_mul_right hp).mp
      nlinarith
    have he : P.M / P.μ * ‖x' - x‖ = (P.M * ‖x' - x‖) / P.μ := by ring
    rw [he]
    apply (le_div_iff₀ P.μ_pos).mpr
    simpa only [mul_comm] using hc

def Phi (P : SmoothStronglyConcave dx dy) (x : Vec dx) : ℝ := P.f x (P.yStar x)
def gradPhi (P : SmoothStronglyConcave dx dy) (x : Vec dx) : Vec dx := P.gradX x (P.yStar x)

theorem Phi_eq_sup (P : SmoothStronglyConcave dx dy) (x : Vec dx) :
    P.Phi x = sSup (Set.range (P.f x)) := by
  have hb : BddAbove (Set.range (P.f x)) := ⟨P.Phi x, by
    rintro _ ⟨y, rfl⟩; exact P.yStar_maximizes x y⟩
  apply le_antisymm
  · exact le_csSup hb ⟨P.yStar x, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨y, rfl⟩; exact P.yStar_maximizes x y

theorem slice_upper (P : SmoothStronglyConcave dx dy) (y : Vec dy) (x x' : Vec dx) :
    P.f x' y ≤ P.f x y + @inner ℝ (Vec dx) _ (P.gradX x y) (x' - x) +
      P.M / 2 * ‖x' - x‖ ^ 2 := by
  have hg : ∀ z, HasGradientAt (fun w => -P.f w y) (-P.gradX z y) z := by
    intro z
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa only [map_neg] using (P.gradX_spec z y).hasFDerivAt.neg
  have hl : ∀ u v, ‖-P.gradX u y - -P.gradX v y‖ ≤ P.M * ‖u - v‖ := by
    intro u v
    simpa only [neg_sub_neg, norm_sub_rev] using P.gradX_x_lipschitz y u v
  have h := gradient_lower_model (fun z => -P.f z y) (fun z => -P.gradX z y) P.M hg hl x x'
  simp only [inner_neg_left] at h
  linarith

theorem Phi_remainder_lower (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) :
    -(P.M / 2) * ‖x' - x‖ ^ 2 ≤ P.Phi x' - P.Phi x -
      @inner ℝ (Vec dx) _ (P.gradPhi x) (x' - x) := by
  have hl := gradient_lower_model (fun z => P.f z (P.yStar x)) (fun z => P.gradX z (P.yStar x))
    P.M (fun z => P.gradX_spec z _) (P.gradX_x_lipschitz _) x x'
  have hm := P.yStar_maximizes x' (P.yStar x)
  change P.f x' (P.yStar x) ≤ P.Phi x' at hm
  change P.Phi x + @inner ℝ (Vec dx) _ (P.gradPhi x) (x' - x) -
    P.M / 2 * ‖x' - x‖ ^ 2 ≤ P.f x' (P.yStar x) at hl
  linarith

theorem Phi_remainder_upper (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) :
    P.Phi x' - P.Phi x - @inner ℝ (Vec dx) _ (P.gradPhi x) (x' - x) ≤
      (P.M / 2 + P.M * (P.M / P.μ)) * ‖x' - x‖ ^ 2 := by
  have hu := P.slice_upper (P.yStar x') x x'
  have hm := P.yStar_maximizes x (P.yStar x')
  have hl := P.gradX_y_lipschitz x (P.yStar x') (P.yStar x)
  have hy := P.yStar_lipschitz x x'
  have hi := real_inner_le_norm (P.gradX x (P.yStar x') - P.gradPhi x) (x' - x)
  have hb := mul_le_mul_of_nonneg_left hy (le_of_lt P.M_pos)
  have hc := mul_le_mul_of_nonneg_right (hl.trans hb) (norm_nonneg (x' - x))
  rw [inner_sub_left] at hi
  change P.Phi x' ≤ P.f x (P.yStar x') +
    @inner ℝ (Vec dx) _ (P.gradX x (P.yStar x')) (x' - x) + P.M / 2 * ‖x' - x‖ ^ 2 at hu
  change P.f x (P.yStar x') ≤ P.Phi x at hm
  change ‖P.gradX x (P.yStar x') - P.gradPhi x‖ * ‖x' - x‖ ≤ _ at hc
  nlinarith

theorem Phi_remainder (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) :
    ‖P.Phi x' - P.Phi x - @inner ℝ (Vec dx) _ (P.gradPhi x) (x' - x)‖ ≤
      (P.M / 2 + P.M * (P.M / P.μ)) * ‖x' - x‖ ^ 2 := by
  rw [Real.norm_eq_abs, abs_le]
  have hl := P.Phi_remainder_lower x x'
  have hu := P.Phi_remainder_upper x x'
  have hn : 0 ≤ (P.M * (P.M / P.μ)) * ‖x' - x‖ ^ 2 := by
    have := P.M_pos; have := P.μ_pos; positivity
  constructor <;> nlinarith

/-- Danskin's gradient formula, proved from primitive data rather than assumed. -/
theorem Phi_hasGradient (P : SmoothStronglyConcave dx dy) (x : Vec dx) :
    HasGradientAt P.Phi (P.gradPhi x) x := by
  rw [hasGradientAt_iff_tendsto]
  let C := P.M / 2 + P.M * (P.M / P.μ)
  have ht : Filter.Tendsto (fun y : Vec dx => ‖y - x‖) (nhds x) (nhds 0) := by
    have hc : ContinuousAt (fun y : Vec dx => ‖y - x‖) x := (continuousAt_id.sub continuousAt_const).norm
    simpa only [ContinuousAt, sub_self, norm_zero] using hc
  have hCt : Filter.Tendsto (fun y : Vec dx => C * ‖y - x‖) (nhds x) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul ht)
  apply squeeze_zero
  · intro y; exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · intro y
    have hr := P.Phi_remainder x y
    change ‖y - x‖⁻¹ * ‖P.Phi y - P.Phi x -
      @inner ℝ (Vec dx) _ (P.gradPhi x) (y - x)‖ ≤ C * ‖y - x‖
    by_cases hd : ‖y - x‖ = 0
    · simp [hd]
    · have hm := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (norm_nonneg (y - x)))
      calc
        _ ≤ ‖y - x‖⁻¹ * (C * ‖y - x‖ ^ 2) := hm
        _ = C * ‖y - x‖ := by field_simp [hd]; ring
  · exact hCt

theorem gradPhi_lipschitz (P : SmoothStronglyConcave dx dy) (x x' : Vec dx) :
    ‖P.gradPhi x' - P.gradPhi x‖ ≤ P.M * (1 + P.M / P.μ) * ‖x' - x‖ := by
  have h := dist_triangle (P.gradX x' (P.yStar x')) (P.gradX x (P.yStar x')) (P.gradX x (P.yStar x))
  simp only [dist_eq_norm] at h
  have hx := P.gradX_x_lipschitz (P.yStar x') x' x
  have hy := P.gradX_y_lipschitz x (P.yStar x') (P.yStar x)
  have hb := mul_le_mul_of_nonneg_left (P.yStar_lipschitz x x') (le_of_lt P.M_pos)
  change ‖P.gradPhi x' - P.gradPhi x‖ ≤ _ at h
  nlinarith

theorem yStar_continuous (P : SmoothStronglyConcave dx dy) : Continuous P.yStar := by
  have h : LipschitzWith ⟨P.M / P.μ, by have := P.M_pos; have := P.μ_pos; positivity⟩ P.yStar := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm] using P.yStar_lipschitz y x
  exact h.continuous

theorem gradPhi_continuous (P : SmoothStronglyConcave dx dy) : Continuous P.gradPhi := by
  have h : LipschitzWith ⟨P.M * (1 + P.M / P.μ), by have := P.M_pos; have := P.μ_pos; positivity⟩ P.gradPhi := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm] using P.gradPhi_lipschitz y x
  exact h.continuous

/-- All formerly supplied value/maximizer/gradient data are now constructed. -/
def population (P : SmoothStronglyConcave dx dy) : Rectangular.Population dx dy where
  f := P.f
  gradX := P.gradX
  gradY := P.gradY
  Phi := P.Phi
  gradPhi := P.gradPhi
  gradX_spec := P.gradX_spec
  gradY_spec := P.gradY_spec
  gradPhi_spec := P.Phi_hasGradient
  value_is_max := fun x => ⟨P.yStar x, rfl, P.yStar_maximizes x⟩

theorem population_Phi_eq_sup (P : SmoothStronglyConcave dx dy) (x : Vec dx) :
    P.population.Phi x = sSup (Set.range (P.f x)) := P.Phi_eq_sup x

theorem population_gradPhi_eq (P : SmoothStronglyConcave dx dy) :
    P.population.gradPhi = gradient (fun x => sSup (Set.range (P.f x))) := by
  have he : (fun x => sSup (Set.range (P.f x))) = P.Phi := funext (fun x => (P.Phi_eq_sup x).symm)
  rw [he]
  exact funext (fun x => (P.Phi_hasGradient x).gradient.symm)

def moreau (P : SmoothStronglyConcave dx dy)
    (hb : BddBelow (Set.range (fun x => sSup (Set.range (P.f x))))) : WeaklyConvexPrimal dx :=
  P.population.weaklyConvexPrimal P.M P.M_pos (by
    have he : (fun x => sSup (Set.range (P.f x))) = P.Phi := funext (fun x => (P.Phi_eq_sup x).symm)
    rw [he] at hb
    exact hb) P.gradX_x_lipschitz

/-- Actual minimax value followed by the actual infimum-defined Moreau envelope. -/
theorem minimax_moreau_hasGradient (P : SmoothStronglyConcave dx dy)
    (hb : BddBelow (Set.range (fun x => sSup (Set.range (P.f x))))) (x : Vec dx) :
    HasGradientAt (fun z => sInf (Set.range (fun v => sSup (Set.range (P.f v)) + P.M * ‖v - z‖ ^ 2)))
      ((2 * P.M) • (x - (P.moreau hb).prox x)) x := by
  have he : (fun v => sSup (Set.range (P.f v))) = P.Phi := funext (fun v => (P.Phi_eq_sup v).symm)
  change HasGradientAt
    (fun z => sInf (Set.range (fun v => (fun w => sSup (Set.range (P.f w))) v + P.M * ‖v - z‖ ^ 2))) _ x
  rw [he]
  exact (P.moreau hb).infEnvelope_hasGradient x

end SmoothStronglyConcave

/-- The value and its derivative are uniquely determined by the primitive population data. -/
theorem Rectangular.Population.ext_of_primitives {dx dy : ℕ} (P Q : Rectangular.Population dx dy)
    (hf : P.f = Q.f) (hx : P.gradX = Q.gradX) (hy : P.gradY = Q.gradY) : P = Q := by
  cases P with
  | mk f gx gy F g hX hY hF hmax =>
    cases Q with
    | mk f' gx' gy' F' g' hX' hY' hF' hmax' =>
      cases hf
      cases hx
      cases hy
      have hv : F = F' := by
        funext x
        obtain ⟨y, he, hm⟩ := hmax x
        obtain ⟨y', he', hm'⟩ := hmax' x
        apply le_antisymm
        · rw [he]; exact hm' y
        · rw [he']; exact hm y'
      cases hv
      have hg : g = g' := funext (fun x => (hF x).unique (hF' x))
      cases hg
      rfl

namespace MeasuredOracle.Instance
open MeasureTheory

def primitive (I : Instance) (M μ Δ : ℝ) (hM : 0 < M) (hμ : 0 < μ)
    (h : I.PopulationValid M μ Δ) : SmoothStronglyConcave I.dx I.dy where
  f := I.population.f
  gradX := I.population.gradX
  gradY := I.population.gradY
  M := M
  μ := μ
  M_pos := hM
  μ_pos := hμ
  gradX_spec := I.population.gradX_spec
  gradY_spec := I.population.gradY_spec
  smooth := h.1
  stronglyConcave := h.2.1

/-- Reconstruction is exact: no smaller subclass of the current population interface is used. -/
theorem primitive_population (I : Instance) (M μ Δ : ℝ) (hM : 0 < M) (hμ : 0 < μ)
    (h : I.PopulationValid M μ Δ) : (I.primitive M μ Δ hM hμ h).population = I.population :=
  Rectangular.Population.ext_of_primitives _ _ rfl rfl rfl

def ofPrimitive {dx dy : ℕ} (P : SmoothStronglyConcave dx dy)
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (O : Rectangular.Oracle dx dy Seed) : Instance :=
  ⟨dx, dy, P.population, Seed, inferInstance, ν, inferInstance, O⟩

theorem ofPrimitive_populationValid {dx dy : ℕ} (P : SmoothStronglyConcave dx dy)
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (O : Rectangular.Oracle dx dy Seed) (Δ : ℝ)
    (hb : BddBelow (Set.range (fun x => sSup (Set.range (P.f x)))))
    (hgap : sSup (Set.range (P.f 0)) - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ) :
    (ofPrimitive P Seed ν O).PopulationValid P.M P.μ Δ := by
  have he : (fun x => sSup (Set.range (P.f x))) = P.Phi := funext (fun x => (P.Phi_eq_sup x).symm)
  rw [he] at hb
  change (fun x => sSup (Set.range (P.f x))) 0 - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ at hgap
  rw [he] at hgap
  exact ⟨P.smooth, P.stronglyConcave, hgap, hb⟩

theorem ofPrimitive_primitive (I : Instance) (M μ Δ : ℝ) (hM : 0 < M) (hμ : 0 < μ)
    (h : I.PopulationValid M μ Δ) :
    ofPrimitive (I.primitive M μ Δ hM hμ h) I.Seed I.law I.oracle = I := by
  unfold ofPrimitive
  rw [I.primitive_population M μ Δ hM hμ h]

/-- Exact coverage of the declared population class by primitive assumptions. -/
theorem populationValid_iff_primitive (I : Instance) (M μ Δ : ℝ) (hM : 0 < M) (hμ : 0 < μ) :
    I.PopulationValid M μ Δ ↔ ∃ P : SmoothStronglyConcave I.dx I.dy,
      P.M = M ∧ P.μ = μ ∧ ofPrimitive P I.Seed I.law I.oracle = I ∧
      BddBelow (Set.range (fun x => sSup (Set.range (P.f x)))) ∧
      sSup (Set.range (P.f 0)) - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ := by
  constructor
  · intro h
    let P := I.primitive M μ Δ hM hμ h
    have hp : P.population = I.population := I.primitive_population M μ Δ hM hμ h
    have hv : (fun x => sSup (Set.range (P.f x))) = I.population.Phi := by
      funext x
      rw [← P.population_Phi_eq_sup, hp]
    refine ⟨P, rfl, rfl, I.ofPrimitive_primitive M μ Δ hM hμ h, ?_, ?_⟩
    · rw [hv]; exact h.2.2.2
    · change (fun x => sSup (Set.range (P.f x))) 0 - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ
      rw [hv]; exact h.2.2.1
  · rintro ⟨P, hPM, hPμ, he, hb, hgap⟩
    have h := ofPrimitive_populationValid P I.Seed I.law I.oracle Δ hb hgap
    rw [he, hPM, hPμ] at h
    exact h

/-- Explicit raw oracle moment conditions; neither a value nor a value gradient occurs here. -/
def PrimitiveBVMoments {dx dy : ℕ} (P : SmoothStronglyConcave dx dy)
    {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed)
    (O : Rectangular.Oracle dx dy Seed) (σ : ℝ) : Prop :=
  (∀ x y, Integrable (fun ξ => O.Gx x y ξ) ν ∧ Integrable (fun ξ => O.Gy x y ξ) ν ∧
    (∫ ξ, O.Gx x y ξ ∂ν) = P.gradX x y ∧ (∫ ξ, O.Gy x y ξ ∂ν) = P.gradY x y) ∧
  (∀ x y, Integrable (fun ξ => ‖O.Gx x y ξ - P.gradX x y‖ ^ 2 +
      ‖O.Gy x y ξ - P.gradY x y‖ ^ 2) ν ∧
    (∫ ξ, ‖O.Gx x y ξ - P.gradX x y‖ ^ 2 + ‖O.Gy x y ξ - P.gradY x y‖ ^ 2 ∂ν) ≤ σ ^ 2)

def PrimitiveASMoments {dx dy : ℕ} (P : SmoothStronglyConcave dx dy)
    {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed)
    (O : Rectangular.Oracle dx dy Seed) (σ : ℝ) : Prop :=
  PrimitiveBVMoments P ν O σ ∧ ∀ x y x' y',
    Integrable (fun ξ => ‖O.Gx x y ξ - O.Gx x' y' ξ‖ ^ 2 +
      ‖O.Gy x y ξ - O.Gy x' y' ξ‖ ^ 2) ν ∧
    (∫ ξ, ‖O.Gx x y ξ - O.Gx x' y' ξ‖ ^ 2 + ‖O.Gy x y ξ - O.Gy x' y' ξ‖ ^ 2 ∂ν) ≤
      P.M ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)

theorem ofPrimitive_validBV_iff {dx dy : ℕ} (P : SmoothStronglyConcave dx dy)
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (O : Rectangular.Oracle dx dy Seed) (Δ σ : ℝ)
    (hb : BddBelow (Set.range (fun x => sSup (Set.range (P.f x)))))
    (hgap : sSup (Set.range (P.f 0)) - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ) :
    (ofPrimitive P Seed ν O).ValidBV P.M P.μ Δ σ ↔ PrimitiveBVMoments P ν O σ := by
  change ((ofPrimitive P Seed ν O).PopulationValid P.M P.μ Δ ∧ _) ↔ _
  exact and_iff_right (ofPrimitive_populationValid P Seed ν O Δ hb hgap)

theorem ofPrimitive_validAS_iff {dx dy : ℕ} (P : SmoothStronglyConcave dx dy)
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (O : Rectangular.Oracle dx dy Seed) (Δ σ : ℝ)
    (hb : BddBelow (Set.range (fun x => sSup (Set.range (P.f x)))))
    (hgap : sSup (Set.range (P.f 0)) - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ) :
    (ofPrimitive P Seed ν O).ValidAS P.M P.μ Δ σ ↔ PrimitiveASMoments P ν O σ := by
  unfold ValidAS PrimitiveASMoments
  rw [ofPrimitive_validBV_iff P Seed ν O Δ σ hb hgap]
  rfl

theorem validBV_iff_primitive (I : Instance) (M μ Δ σ : ℝ) (hM : 0 < M) (hμ : 0 < μ) :
    I.ValidBV M μ Δ σ ↔ ∃ P : SmoothStronglyConcave I.dx I.dy,
      P.M = M ∧ P.μ = μ ∧ ofPrimitive P I.Seed I.law I.oracle = I ∧
      BddBelow (Set.range (fun x => sSup (Set.range (P.f x)))) ∧
      (sSup (Set.range (P.f 0)) - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ) ∧
      PrimitiveBVMoments P I.law I.oracle σ := by
  constructor
  · intro h
    obtain ⟨P, hPM, hPμ, he, hb, hgap⟩ := (I.populationValid_iff_primitive M μ Δ hM hμ).mp h.1
    refine ⟨P, hPM, hPμ, he, hb, hgap, ?_⟩
    apply (ofPrimitive_validBV_iff P I.Seed I.law I.oracle Δ σ hb hgap).mp
    rw [he, hPM, hPμ]
    exact h
  · rintro ⟨P, hPM, hPμ, he, hb, hgap, hm⟩
    have h := (ofPrimitive_validBV_iff P I.Seed I.law I.oracle Δ σ hb hgap).mpr hm
    rw [he, hPM, hPμ] at h
    exact h

theorem validAS_iff_primitive (I : Instance) (M μ Δ σ : ℝ) (hM : 0 < M) (hμ : 0 < μ) :
    I.ValidAS M μ Δ σ ↔ ∃ P : SmoothStronglyConcave I.dx I.dy,
      P.M = M ∧ P.μ = μ ∧ ofPrimitive P I.Seed I.law I.oracle = I ∧
      BddBelow (Set.range (fun x => sSup (Set.range (P.f x)))) ∧
      (sSup (Set.range (P.f 0)) - sInf (Set.range (fun x => sSup (Set.range (P.f x)))) ≤ Δ) ∧
      PrimitiveASMoments P I.law I.oracle σ := by
  constructor
  · intro h
    obtain ⟨P, hPM, hPμ, he, hb, hgap⟩ := (I.populationValid_iff_primitive M μ Δ hM hμ).mp h.1.1
    refine ⟨P, hPM, hPμ, he, hb, hgap, ?_⟩
    apply (ofPrimitive_validAS_iff P I.Seed I.law I.oracle Δ σ hb hgap).mp
    rw [he, hPM, hPμ]
    exact h
  · rintro ⟨P, hPM, hPμ, he, hb, hgap, hm⟩
    have h := (ofPrimitive_validAS_iff P I.Seed I.law I.oracle Δ σ hb hgap).mpr hm
    rw [he, hPM, hPμ] at h
    exact h

end MeasuredOracle.Instance

universe u

theorem MemoryModel.risk_primitive_reconstruction {K : ℕ} (A : MemoryModel.Family.{u} K)
    (c : StationarityCriterion) (m : StationarityObjective) (N : ℕ)
    (I : MeasuredOracle.Instance) (M μ Δ : ℝ) (hM : 0 < M) (hμ : 0 < μ)
    (h : I.PopulationValid M μ Δ) :
    MemoryModel.risk A c m M N
      (MeasuredOracle.Instance.ofPrimitive (I.primitive M μ Δ hM hμ h) I.Seed I.law I.oracle) =
      MemoryModel.risk A c m M N I := by
  rw [I.ofPrimitive_primitive M μ Δ hM hμ h]

end NCSCPureStochasticLB.PaperExact
