import GaussianInformation
import ManuscriptProgressExact

/-! Alignment with the ICLR manuscript: finite primal infima, sharp primal smoothness,
same-output envelope transfer, and explicit averaging over internal algorithmic randomness.
The legacy calibration is retained; see PAPER_ALIGNMENT.md for the remaining differences. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NCSCPureStochasticLB.PaperExact

/-- Section 3.1 / equation (6): class membership entails a finite primal lower bound. -/
theorem inNCSCClass_bddBelow {T : ℕ} {I : PopulationObjective T} {M μ Δ : ℝ}
    (h : InNCSCClass I M μ Δ) : BddBelow (Set.range I.Phi) := h.2.2.2

/-- The norm bound of Appendix F, equation (63), obtained directly from the first-order
identity. This proof does not need a Hessian or an additional smoothness axiom. -/
theorem canonicalLiftGradPhi_lipschitz {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (x x' : Vec T) :
    ‖canonicalLiftGradPhi C P x - canonicalLiftGradPhi C P x'‖ ≤
      (P.ν * P.γ ^ 2 * ℓ₀ * P.h / P.μ) * ‖x - x'‖ := by
  have hb : 0 < P.β := div_pos P.h_pos P.q_pos
  have hq : 0 ≤ P.γ * P.q := le_of_lt (mul_pos P.γ_pos P.q_pos)
  have hl : 0 ≤ ℓ₀ * P.β := mul_nonneg (by norm_num [ℓ₀]) (le_of_lt hb)
  rw [canonicalLiftGradPhi_eq_scaled_chain, canonicalLiftGradPhi_eq_scaled_chain,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  calc
    (P.γ * P.q) * ‖C.gradF (P.β • canonicalLiftYStar C P x) -
        C.gradF (P.β • canonicalLiftYStar C P x')‖
      ≤ (P.γ * P.q) * (ℓ₀ * ‖P.β • canonicalLiftYStar C P x -
          P.β • canonicalLiftYStar C P x'‖) :=
        mul_le_mul_of_nonneg_left (C.grad_lipschitz _ _) hq
    _ = (P.γ * P.q) * ((ℓ₀ * P.β) *
        ‖canonicalLiftYStar C P x - canonicalLiftYStar C P x'‖) := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb]; ring
    _ ≤ (P.γ * P.q) * ((ℓ₀ * P.β) *
        ((P.ν * P.γ / P.μ) * ‖x - x'‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (canonicalLiftYStar_lipschitz C P x x') hl) hq
    _ = (P.ν * P.γ ^ 2 * ℓ₀ * P.h / P.μ) * ‖x - x'‖ := by
        calc
          _ = (P.ν * P.γ ^ 2 * ℓ₀ * (P.q * P.β) / P.μ) * ‖x - x'‖ := by ring
          _ = _ := by rw [P.q_mul_beta]

/-- Equation (30)'s curvature constant under the displayed calibration bounds. -/
theorem canonicalLiftGradPhi_lipschitz_calibrated {T : ℕ}
    (C : ExplicitZeroChainCertificate T) (P : LiftParameters) (M : ℝ)
    (hν : P.ν ≤ 5 * P.μ / 4) (hh : ℓ₀ * P.h ≤ P.μ / 4)
    (hγ : P.γ ^ 2 = M / (4 * P.μ)) (x x' : Vec T) :
    ‖canonicalLiftGradPhi C P x - canonicalLiftGradPhi C P x'‖ ≤
      (5 * M / 64) * ‖x - x'‖ := by
  have hcoeff : P.ν * P.γ ^ 2 * ℓ₀ * P.h / P.μ ≤ 5 * M / 64 := by
    calc
      _ = P.ν * (ℓ₀ * P.h) * P.γ ^ 2 / P.μ := by ring
      _ ≤ (5 * P.μ / 4) * (P.μ / 4) * P.γ ^ 2 / P.μ := by
        apply div_le_div_of_nonneg_right _ (le_of_lt P.μ_pos)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul hν hh (mul_nonneg (by norm_num [ℓ₀]) (le_of_lt P.h_pos))
          (by have := P.μ_pos; positivity)
      _ = 5 * M / 64 := by rw [hγ]; field_simp [ne_of_gt P.μ_pos]; ring
  exact (canonicalLiftGradPhi_lipschitz C P x x').trans
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))

/-- Same-output transfer used in Appendix F. The premise is the proximal first-order
identity; existence, uniqueness and differentiation of the Moreau envelope are separate. -/
theorem same_output_envelope_transfer {T : ℕ} (g : Vec T → Vec T)
    (M : ℝ) (hM : 0 < M)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ (5 * M / 64) * ‖x - y‖)
    (x u : Vec T) (hprox : g u = (2 * M) • (x - u)) :
    ‖g x‖ ≤ (133 / 128 : ℝ) * ‖g u‖ := by
  have ht : ‖g x‖ ≤ ‖g x - g u‖ + ‖g u‖ := by
    simpa using norm_add_le (g x - g u) (g u)
  have hn : ‖g u‖ = (2 * M) * ‖x - u‖ := by
    rw [hprox, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hh := hlip x u
  nlinarith

/-- The hard-event margin in Appendix F follows at the same output point. -/
theorem envelope_hard_event_margin {T : ℕ} (g : Vec T → Vec T)
    (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ (5 * M / 64) * ‖x - y‖)
    (x u : Vec T) (hprox : g u = (2 * M) • (x - u))
    (hhard : (20 / 3 : ℝ) * ε < ‖g x‖) : 6 * ε < ‖g u‖ := by
  have h := same_output_envelope_transfer g M hM hlip x u hprox
  linarith

/-- Uniform quantitative risk margin, before averaging over internal randomness. -/
theorem runProgress_uniform_squared_risk {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε) (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (hT : 8 ≤ T) (A : BernoulliRun T R K (liftedOracle B P))
    (W : RunProgressWitness C.dim_pos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    (25 / 18 : ℝ) * ε ^ 2 ≤ stationarityRisk p L.gradPhi A := by
  have ht := terminal_unrevealed_probability_of_runProgress C.dim_pos hT p
    (le_of_lt hp) hp1 A W hR
  have he := unfinished_probability_of_terminal_unrevealed C.dim_pos p
    (le_of_lt hp) hp1 P A ht
  have hl := stationarityRisk_ge_event_mass p (le_of_lt hp) hp1 L.gradPhi A
    (unfinishedOutputEvent P A) ((25 / 9 : ℝ) * ε ^ 2) (by positivity)
    (fun w hw => le_of_lt (proposition24_pathwise_stationarity_sq C B P L
      ε hε hγq hratio ((A.trace w).output) hw))
  have hm := mul_le_mul_of_nonneg_left (le_of_lt he)
    (show 0 ≤ (25 / 9 : ℝ) * ε ^ 2 by positivity)
  nlinarith

/-- Sharpen the existing progress lemma to the manuscript's probability `3/4`. -/
theorem progress_probability_three_quarters
    (R T : ℕ) (p : ℝ) (inc : Fin R → RoundWorld R → ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p)
    (hT : 8 ≤ T) (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    (3 / 4 : ℝ) ≤ roundProb p {w | (∑ t : Fin R, inc t w) < T} := by
  exact progress_three_quarters_from_exact R T p inc hp hp1 h01 hreveal (by omega) hR

theorem unfinished_probability_three_quarters {T R K : ℕ}
    {O : StochasticOracle T Bool} (hTpos : 0 < T) (hT : 8 ≤ T)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (P : LiftParameters)
    (A : BernoulliRun T R K O) (W : RunProgressWitness hTpos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    (3 / 4 : ℝ) ≤ roundProb p (unfinishedOutputEvent P A) := by
  have h := progress_probability_three_quarters R T p W.inc hp hp1
    W.zero_one W.reveal_prob hT hR
  exact h.trans (roundProb_mono p (le_of_lt hp) hp1 (fun w hw =>
    unfinished_prog_of_terminal_unrevealed hTpos P A w
      (W.unfinished_implies_terminal_unrevealed w hw)))

def stationarityNormRisk {T R K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (g : Vec T → Vec T) (A : BernoulliRun T R K O) : ℝ :=
  roundExpect p (fun w => ‖g ((A.trace w).output)‖)

theorem stationarityNormRisk_ge_event_mass
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {T R K : ℕ} {O : StochasticOracle T Bool}
    (g : Vec T → Vec T) (A : BernoulliRun T R K O)
    (E : Set (RoundWorld R)) (c : ℝ)
    (h : ∀ w, w ∈ E → c ≤ ‖g ((A.trace w).output)‖) :
    c * roundProb p E ≤ stationarityNormRisk p g A := by
  classical
  unfold roundProb stationarityNormRisk roundExpect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : w ∈ E
  · simpa [hw, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (h w hw) (roundWeight_nonneg p hp hp1 w)
  · simpa [hw] using mul_nonneg (roundWeight_nonneg p hp hp1 w)
      (norm_nonneg (g ((A.trace w).output)))

theorem runProgress_uniform_norm_risk {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 2 * ε) (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (hT : 8 ≤ T) (A : BernoulliRun T R K (liftedOracle B P))
    (W : RunProgressWitness C.dim_pos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    (5 / 4 : ℝ) * ε ≤ stationarityNormRisk p L.gradPhi A := by
  have he := unfinished_probability_three_quarters C.dim_pos hT p hp hp1 P A W hR
  have hl := stationarityNormRisk_ge_event_mass p (le_of_lt hp) hp1 L.gradPhi A
    (unfinishedOutputEvent P A) ((5 / 3 : ℝ) * ε) (fun w hw =>
      le_of_lt (proposition24_pathwise_stationarity C B P L ε hε hγq hratio
        ((A.trace w).output) hw))
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ (5 / 3 : ℝ) * ε by positivity)
  nlinarith

/-- Proposition C.2's displayed first and second moment constants under `γq = 8ε`.
This is the probabilistic conclusion; calibration and a concrete support witness remain explicit. -/
theorem manuscript_C2_moments {T R K : ℕ}
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (P : LiftParameters)
    (L : LiftPropertiesCertificate T C B P)
    (p ε : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε)
    (hγq : P.γ * P.q = 8 * ε) (hratio : ℓ₀ * P.h / P.ν ≤ 1 / 5)
    (hT : 8 ≤ T) (A : BernoulliRun T R K (liftedOracle B P))
    (W : RunProgressWitness C.dim_pos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    5 * ε ≤ stationarityNormRisk p L.gradPhi A ∧
      (100 / 3 : ℝ) * ε ^ 2 ≤ stationarityRisk p L.gradPhi A := by
  have hε' : 0 < 4 * ε := by positivity
  have hγq' : P.γ * P.q = 2 * (4 * ε) := by linarith
  constructor
  · have h := runProgress_uniform_norm_risk C B P L p (4 * ε) hp hp1 hε'
      hγq' hratio hT A W hR
    nlinarith
  · have he := unfinished_probability_three_quarters C.dim_pos hT p hp hp1 P A W hR
    have hl := stationarityRisk_ge_event_mass p (le_of_lt hp) hp1 L.gradPhi A
      (unfinishedOutputEvent P A) ((25 / 9 : ℝ) * (4 * ε) ^ 2) (by positivity)
      (fun w hw => le_of_lt (proposition24_pathwise_stationarity_sq C B P L
        (4 * ε) hε' hγq' hratio ((A.trace w).output) hw))
    have hm := mul_le_mul_of_nonneg_left he
      (show 0 ≤ (25 / 9 : ℝ) * (4 * ε) ^ 2 by positivity)
    nlinarith

universe u

/-- The independent internal seed is averaged after taking the finite oracle expectation.
Nonnegative integration includes non-integrable (infinite-risk) algorithms. -/
def internalRandomStationarityRisk {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) {T R K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T R K O) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (stationarityRisk p g (A ω)) ∂ρ

theorem internalRandomStationarityRisk_lower {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {T R K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T R K O)
    (c : ℝ) (h : ∀ ω, c ≤ stationarityRisk p g (A ω)) :
    ENNReal.ofReal c ≤ internalRandomStationarityRisk ρ p g A := by
  calc
    ENNReal.ofReal c = ∫⁻ _ω : Ω, ENNReal.ofReal c ∂ρ := by simp
    _ ≤ _ := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (h ω))

/-- An explicit integrated internal-seed theorem for the fixed BV construction. -/
theorem bv_internal_random_risk_lower {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {T R K : ℕ} (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P) (hT : 8 ≤ T)
    (A : Ω → BernoulliRun T R K (bvConstructedOracle W))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal (P.ε ^ 2) <
      internalRandomStationarityRisk ρ P.p (bvConstructedPopulation W).gradPhi A := by
  have hl := internalRandomStationarityRisk_lower ρ P.p
    (bvConstructedPopulation W).gradPhi A ((25 / 18 : ℝ) * P.ε ^ 2) (fun ω =>
      runProgress_uniform_squared_risk C W.B W.LP W.lift_properties P.p P.ε
        (bv_p_pos P) (bv_p_le_one P) P.ε_pos (bvWitness_gamma_mul_q W)
        (le_of_eq (bvWitness_transfer_ratio W)) hT (A ω)
        (bvCanonicalRunProgressWitness C P W (A ω)) hR)
  have hs : P.ε ^ 2 < (25 / 18 : ℝ) * P.ε ^ 2 := by
    nlinarith [sq_pos_of_pos P.ε_pos]
  exact ((ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by norm_num) (sq_pos_of_pos P.ε_pos))).2 hs).trans_le hl

/-- An explicit integrated internal-seed theorem for the fixed AS construction. -/
theorem as_internal_random_risk_lower {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {T R K : ℕ} {mΓ : ℝ} (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ) (hT : 8 ≤ T)
    (A : Ω → BernoulliRun T R K (asConstructedOracle W))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal (P.ε ^ 2) <
      internalRandomStationarityRisk ρ P.p (asConstructedPopulation W).gradPhi A := by
  have hl := internalRandomStationarityRisk_lower ρ P.p
    (asConstructedPopulation W).gradPhi A ((25 / 18 : ℝ) * P.ε ^ 2) (fun ω =>
      runProgress_uniform_squared_risk C W.B W.LP W.lift_properties P.p P.ε
        P.p_pos (as_p_le_one P) P.ε_pos (asWitness_gamma_mul_q W)
        (asWitness_transfer_ratio W) hT (A ω)
        (asCanonicalRunProgressWitness C P W Gate (A ω)) hR)
  have hs : P.ε ^ 2 < (25 / 18 : ℝ) * P.ε ^ 2 := by
    nlinarith [sq_pos_of_pos P.ε_pos]
  exact ((ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by norm_num) (sq_pos_of_pos P.ε_pos))).2 hs).trans_le hl

/-- Explicit expected-norm risk, averaged over the independent internal seed. -/
def internalRandomNormRisk {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) {T R K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T R K O) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (stationarityNormRisk p g (A ω)) ∂ρ

theorem internalRandomNormRisk_lower {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {T R K : ℕ} {O : StochasticOracle T Bool}
    (p : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T R K O)
    (c : ℝ) (h : ∀ ω, c ≤ stationarityNormRisk p g (A ω)) :
    ENNReal.ofReal c ≤ internalRandomNormRisk ρ p g A := by
  calc
    ENNReal.ofReal c = ∫⁻ _ω : Ω, ENNReal.ofReal c ∂ρ := by simp
    _ ≤ _ := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (h ω))

theorem bv_internal_random_norm_lower {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {T R K : ℕ} (C : ExplicitZeroChainCertificate T) (P : BVParameters)
    (W : BVConstructionWitness C P) (hT : 8 ≤ T)
    (A : Ω → BernoulliRun T R K (bvConstructedOracle W))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal P.ε <
      internalRandomNormRisk ρ P.p (bvConstructedPopulation W).gradPhi A := by
  have hl := internalRandomNormRisk_lower ρ P.p
    (bvConstructedPopulation W).gradPhi A ((5 / 4 : ℝ) * P.ε) (fun ω =>
      runProgress_uniform_norm_risk C W.B W.LP W.lift_properties P.p P.ε
        (bv_p_pos P) (bv_p_le_one P) P.ε_pos (bvWitness_gamma_mul_q W)
        (le_of_eq (bvWitness_transfer_ratio W)) hT (A ω)
        (bvCanonicalRunProgressWitness C P W (A ω)) hR)
  have hs : P.ε < (5 / 4 : ℝ) * P.ε := by linarith [P.ε_pos]
  exact ((ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) P.ε_pos)).2 hs).trans_le hl

theorem as_internal_random_norm_lower {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {T R K : ℕ} {mΓ : ℝ} (C : ExplicitZeroChainCertificate T) (P : ASParameters)
    (W : ASConstructionWitness C P) (Gate : SmoothGateCertificate mΓ) (hT : 8 ≤ T)
    (A : Ω → BernoulliRun T R K (asConstructedOracle W))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal P.ε <
      internalRandomNormRisk ρ P.p (asConstructedPopulation W).gradPhi A := by
  have hl := internalRandomNormRisk_lower ρ P.p
    (asConstructedPopulation W).gradPhi A ((5 / 4 : ℝ) * P.ε) (fun ω =>
      runProgress_uniform_norm_risk C W.B W.LP W.lift_properties P.p P.ε
        P.p_pos (as_p_le_one P) P.ε_pos (asWitness_gamma_mul_q W)
        (asWitness_transfer_ratio W) hT (A ω)
        (asCanonicalRunProgressWitness C P W Gate (A ω)) hR)
  have hs : P.ε < (5 / 4 : ℝ) * P.ε := by linarith [P.ε_pos]
  exact ((ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) P.ε_pos)).2 hs).trans_le hl

end NCSCPureStochasticLB.PaperExact
