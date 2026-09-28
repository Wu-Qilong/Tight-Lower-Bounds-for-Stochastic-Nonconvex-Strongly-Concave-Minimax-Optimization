import PaperAlignment

/-! Exact lift constants used in Appendices D--F of the ICLR manuscript.
The base-chain certificate keeps its published Lipschitz bound 152. The manuscript's
conservative bound 155 is implemented without changing the imported analytic input. -/

noncomputable section
namespace NCSCPureStochasticLB.PaperExact

/-- Shared deterministic calibration. The BV and AS choices of `h` are supplied below. -/
structure ManuscriptCalibration where
  M : ℝ
  μ : ℝ
  ε : ℝ
  h : ℝ
  M_pos : 0 < M
  μ_pos : 0 < μ
  ε_pos : 0 < ε
  h_pos : 0 < h
  h_le : h ≤ μ / (4 * 155)

namespace ManuscriptCalibration

def gamma (P : ManuscriptCalibration) : ℝ := Real.sqrt (P.M / (4 * P.μ))

theorem gamma_pos (P : ManuscriptCalibration) : 0 < P.gamma :=
  Real.sqrt_pos.2 (div_pos P.M_pos (mul_pos (by norm_num) P.μ_pos))

theorem gamma_sq (P : ManuscriptCalibration) : P.gamma ^ 2 = P.M / (4 * P.μ) :=
  Real.sq_sqrt (le_of_lt (div_pos P.M_pos (mul_pos (by norm_num) P.μ_pos)))

def q (P : ManuscriptCalibration) : ℝ := 8 * P.ε / P.gamma

theorem q_pos (P : ManuscriptCalibration) : 0 < P.q :=
  div_pos (mul_pos (by norm_num) P.ε_pos) P.gamma_pos

/-- The old lift writes `ν = μ_internal + 152h`. Choosing `μ_internal = μ + 3h`
gives exactly the manuscript's objective with `ν = μ + 155h`, and proves a slightly
stronger concavity bound before weakening it to the requested `μ`. -/
def lift (P : ManuscriptCalibration) : LiftParameters where
  μ := P.μ + 3 * P.h
  h := P.h
  q := P.q
  γ := P.gamma
  μ_pos := add_pos P.μ_pos (mul_pos (by norm_num) P.h_pos)
  h_pos := P.h_pos
  q_pos := P.q_pos
  γ_pos := P.gamma_pos

theorem nu_eq (P : ManuscriptCalibration) : P.lift.ν = P.μ + 155 * P.h := by
  simp [lift, LiftParameters.ν, ℓ₀]; ring

theorem gamma_q (P : ManuscriptCalibration) : P.lift.γ * P.lift.q = 8 * P.ε := by
  change P.gamma * (8 * P.ε / P.gamma) = _
  field_simp [ne_of_gt P.gamma_pos]

theorem q_sq (P : ManuscriptCalibration) :
    P.q ^ 2 = 256 * P.ε ^ 2 / (P.M / P.μ) := by
  unfold q
  rw [div_pow, P.gamma_sq]
  field_simp
  ring

theorem ell_h_le (P : ManuscriptCalibration) : 155 * P.h ≤ P.μ / 4 := by
  have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4 * 155)).1 P.h_le
  linarith

theorem nu_le (P : ManuscriptCalibration) : P.lift.ν ≤ 5 * P.μ / 4 := by
  rw [P.nu_eq]
  linarith [P.ell_h_le]

theorem transfer_ratio (P : ManuscriptCalibration) : ℓ₀ * P.lift.h / P.lift.ν ≤ 1 / 5 := by
  apply (div_le_iff₀ (lift_nu_pos P.lift)).2
  rw [P.nu_eq]
  change 152 * P.h ≤ 1 / 5 * (P.μ + 155 * P.h)
  linarith [P.ell_h_le, P.h_pos]

/-- The manuscript's desired strong concavity follows from the stronger internal bound. -/
theorem stronglyConcave {T : ℕ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) : LiftStrongConcavity C P.lift P.μ := by
  intro x y y'
  have hh := liftedF_mu_strong_concavity C P.lift x y y'
  have hnonneg : 0 ≤ 3 * P.h / 2 * ‖y' - y‖ ^ 2 := by
    have := P.h_pos
    positivity
  change liftedF C P.lift x y' ≤ _ at hh ⊢
  change liftedF C P.lift x y' ≤ liftedF C P.lift x y +
    @inner ℝ (Vec T) _
      (P.lift.q • C.gradF (P.lift.β • y) - P.lift.ν • (y - P.lift.γ • x))
      (y' - y) - (P.μ + 3 * P.h) / 2 * ‖y' - y‖ ^ 2 at hh
  nlinarith

/-- The precise primal Lipschitz constant in equation (30), for either choice of `h`. -/
theorem primal_lipschitz {T : ℕ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) (x x' : Vec T) :
    ‖canonicalLiftGradPhi C P.lift x - canonicalLiftGradPhi C P.lift x'‖ ≤
      (5 * P.M / 64) * ‖x - x'‖ := by
  have hm : P.μ ≤ P.lift.μ := by change P.μ ≤ P.μ + 3 * P.h; linarith [P.h_pos]
  have hh : ℓ₀ * P.lift.h ≤ P.μ / 4 := by
    change 152 * P.h ≤ P.μ / 4
    linarith [P.ell_h_le, P.h_pos]
  have hn : 0 ≤ P.lift.ν * P.lift.γ ^ 2 * ℓ₀ * P.lift.h := by
    have := lift_nu_pos P.lift
    have := P.lift.h_pos
    have : 0 ≤ ℓ₀ := by norm_num [ℓ₀]
    positivity
  have hcoeff : P.lift.ν * P.lift.γ ^ 2 * ℓ₀ * P.lift.h / P.lift.μ ≤ 5 * P.M / 64 := by
    calc
      _ ≤ P.lift.ν * P.lift.γ ^ 2 * ℓ₀ * P.lift.h / P.μ :=
        div_le_div_of_nonneg_left hn P.μ_pos hm
      _ = P.lift.ν * (ℓ₀ * P.lift.h) * P.gamma ^ 2 / P.μ := by
        change P.lift.ν * P.gamma ^ 2 * ℓ₀ * P.lift.h / P.μ = _
        ring
      _ ≤ (5 * P.μ / 4) * (P.μ / 4) * P.gamma ^ 2 / P.μ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt P.μ_pos)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul P.nu_le hh
          (mul_nonneg (by norm_num [ℓ₀]) (le_of_lt P.h_pos))
          (by have := P.μ_pos; positivity)
      _ = 5 * P.M / 64 := by rw [P.gamma_sq]; field_simp [ne_of_gt P.μ_pos]; ring
  exact (canonicalLiftGradPhi_lipschitz C P.lift x x').trans
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))

/-- Proposition C.2 with the new exact lift calibration. The support/progress witness is
an explicit input here, not a new axiom or an assumed risk conclusion. -/
theorem hard_event_moments {T R K : ℕ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hT : 8 ≤ T)
    (A : BernoulliRun T R K (liftedOracle B P.lift))
    (W : RunProgressWitness C.dim_pos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    5 * P.ε ≤ stationarityNormRisk p (canonicalLiftGradPhi C P.lift) A ∧
      (100 / 3 : ℝ) * P.ε ^ 2 ≤ stationarityRisk p (canonicalLiftGradPhi C P.lift) A := by
  exact manuscript_C2_moments C B P.lift (canonicalLiftPropertiesCertificate C B P.lift)
    p P.ε hp hp1 P.ε_pos P.gamma_q P.transfer_ratio hT A W hR

end ManuscriptCalibration

def manuscriptBVCalibration (M μ ε : ℝ) (hM : 0 < M) (hμ : 0 < μ) (hε : 0 < ε) :
    ManuscriptCalibration where
  M := M
  μ := μ
  ε := ε
  h := μ / (4 * 155)
  M_pos := hM
  μ_pos := hμ
  ε_pos := hε
  h_pos := div_pos hμ (by norm_num)
  h_le := le_rfl

def manuscriptASCalibration (M μ ε p s : ℝ)
    (hM : 0 < M) (hμ : 0 < μ) (hε : 0 < ε) (hp : 0 < p) (hs : 0 < s) :
    ManuscriptCalibration where
  M := M
  μ := μ
  ε := ε
  h := min (μ / (4 * 155)) (M * Real.sqrt p / (4 * s))
  M_pos := hM
  μ_pos := hμ
  ε_pos := hε
  h_pos := lt_min (div_pos hμ (by norm_num))
    (div_pos (mul_pos hM (Real.sqrt_pos.2 hp)) (mul_pos (by norm_num) hs))
  h_le := min_le_left _ _

end NCSCPureStochasticLB.PaperExact
