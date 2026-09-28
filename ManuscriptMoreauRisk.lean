import ManuscriptMoreau

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

universe u

namespace ManuscriptCalibration

/-- Appendix F's exact hard-event margins for the actual Moreau gradient at the algorithm output. -/
theorem moreau_moments {T R K : ℕ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hT : 8 ≤ T)
    (A : BernoulliRun T R K (liftedOracle B P.lift))
    (W : RunProgressWitness C.dim_pos p A)
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    (9 / 2 : ℝ) * P.ε ≤ stationarityNormRisk p (P.primal C).envelopeGrad A ∧
      27 * P.ε ^ 2 ≤ stationarityRisk p (P.primal C).envelopeGrad A := by
  have he := unfinished_probability_three_quarters C.dim_pos hT p hp hp1 P.lift A W hR
  have hgq : P.lift.γ * P.lift.q = 2 * (4 * P.ε) := by linarith [P.gamma_q]
  have hhard : ∀ w, w ∈ unfinishedOutputEvent P.lift A →
      6 * P.ε < ‖(P.primal C).envelopeGrad ((A.trace w).output)‖ := by
    intro w hw
    have hg := proposition24_pathwise_stationarity C B P.lift
      (canonicalLiftPropertiesCertificate C B P.lift) (4 * P.ε)
      (by have := P.ε_pos; positivity) hgq P.transfer_ratio ((A.trace w).output) hw
    have hg' : (20 / 3 : ℝ) * P.ε < ‖(P.primal C).g ((A.trace w).output)‖ := by
      change (5 / 3 : ℝ) * (4 * P.ε) < ‖canonicalLiftGradPhi C P.lift ((A.trace w).output)‖ at hg
      change (20 / 3 : ℝ) * P.ε < ‖canonicalLiftGradPhi C P.lift ((A.trace w).output)‖
      linarith
    have hs := envelope_hard_event_margin (P.primal C).g P.M P.ε P.M_pos P.ε_pos
      (P.primal C).grad_lip ((A.trace w).output) ((P.primal C).prox ((A.trace w).output))
      ((P.primal C).prox_first_order _) hg'
    simpa only [CalibratedPrimal.envelopeGrad_eq] using hs
  constructor
  · have hl := stationarityNormRisk_ge_event_mass p (le_of_lt hp) hp1 (P.primal C).envelopeGrad A
      (unfinishedOutputEvent P.lift A) (6 * P.ε) (fun w hw => le_of_lt (hhard w hw))
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 6 * P.ε by have := P.ε_pos; positivity)
    nlinarith
  · have hl := stationarityRisk_ge_event_mass p (le_of_lt hp) hp1 (P.primal C).envelopeGrad A
      (unfinishedOutputEvent P.lift A) (36 * P.ε ^ 2) (by positivity) (by
        intro w hw
        have hh := hhard w hw
        nlinarith [P.ε_pos, norm_nonneg ((P.primal C).envelopeGrad ((A.trace w).output))])
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 36 * P.ε ^ 2 by positivity)
    nlinarith

end ManuscriptCalibration

/-- Integrate the two uniform margins over an independent internal seed. -/
theorem moreau_integrated_margins {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {T R K : ℕ} {O : StochasticOracle T Bool}
    (p ε : ℝ) (g : Vec T → Vec T) (A : Ω → BernoulliRun T R K O)
    (hm : ∀ ω, (9 / 2 : ℝ) * ε ≤ stationarityNormRisk p g (A ω) ∧
      27 * ε ^ 2 ≤ stationarityRisk p g (A ω)) :
    ENNReal.ofReal ((9 / 2 : ℝ) * ε) ≤ internalRandomNormRisk ρ p g A ∧
    ENNReal.ofReal (27 * ε ^ 2) ≤ internalRandomStationarityRisk ρ p g A :=
  ⟨internalRandomNormRisk_lower ρ p g A _ (fun ω => (hm ω).1),
    internalRandomStationarityRisk_lower ρ p g A _ (fun ω => (hm ω).2)⟩

theorem round_lower_of_moreau_margins {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {T R K : ℕ} {O : StochasticOracle T Bool}
    (p ε c : ℝ) (hε : 0 < ε) (g : Vec T → Vec T) (A : Ω → BernoulliRun T R K O)
    (hm : (R : ℝ) ≤ c → ∀ ω, (9 / 2 : ℝ) * ε ≤ stationarityNormRisk p g (A ω) ∧
      27 * ε ^ 2 ≤ stationarityRisk p g (A ω))
    (hsuccess : internalRandomNormRisk ρ p g A ≤ ENNReal.ofReal ε ∨
      internalRandomStationarityRisk ρ p g A ≤ ENNReal.ofReal (ε ^ 2)) : c < (R : ℝ) := by
  by_contra hn
  have hi := moreau_integrated_margins ρ p ε g A (hm (le_of_not_gt hn))
  rcases hsuccess with h | h
  · have hs : ENNReal.ofReal ε < ENNReal.ofReal ((9 / 2 : ℝ) * ε) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    exact (not_lt_of_ge (hi.1.trans h)) hs
  · have hs : ENNReal.ofReal (ε ^ 2) < ENNReal.ofReal (27 * ε ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) (sq_pos_of_pos hε))).2
        (by nlinarith [sq_pos_of_pos hε])
    exact (not_lt_of_ge (hi.2.trans h)) hs

namespace ManuscriptBVProblem

def moreau (P : ManuscriptBVProblem) : CalibratedPrimal P.T := P.calibration.primal P.chain

theorem moreau_is_envelope (P : ManuscriptBVProblem) (x : Vec P.T) :
    P.moreau.envelope x = sInf (Set.range (fun v => P.population.Phi v + P.M * ‖v - x‖ ^ 2)) :=
  P.moreau.envelope_eq_inf x

theorem moreau_hasGradient (P : ManuscriptBVProblem) (x : Vec P.T) :
    HasGradientAt P.moreau.envelope (P.moreau.envelopeGrad x) x := P.moreau.envelope_hasGradient x

theorem moreau_moments (P : ManuscriptBVProblem) {R K : ℕ} (A : BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    (9 / 2 : ℝ) * P.ε ≤ stationarityNormRisk P.p P.moreau.envelopeGrad A ∧
      27 * P.ε ^ 2 ≤ stationarityRisk P.p P.moreau.envelopeGrad A :=
  P.calibration.moreau_moments P.chain P.base P.p P.p_pos P.p_le_one P.T_ge_eight A
    (pairGrowthRunProgress P.chain.dim_pos P.p (manuscriptBV_pair_growth P.chain P.calibration.lift P.p) A) hR

theorem moreau_randomized_moments (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ} (A : Ω → BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal ((9 / 2 : ℝ) * P.ε) ≤ internalRandomNormRisk ρ P.p P.moreau.envelopeGrad A ∧
    ENNReal.ofReal (27 * P.ε ^ 2) ≤ internalRandomStationarityRisk ρ P.p P.moreau.envelopeGrad A :=
  moreau_integrated_margins ρ P.p P.ε _ A (fun ω => P.moreau_moments (A ω) hR)

theorem moreau_rate_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ} (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal (P.ε ^ 2)) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (R : ℝ) :=
  P.rate_threshold.trans_lt (round_lower_of_moreau_margins ρ P.p P.ε _ P.ε_pos _ A
    (fun h ω => P.moreau_moments (A ω) h) hsuccess)

theorem moreau_gradient_lower (P : ManuscriptBVProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ} (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal (P.ε ^ 2))
    (hbatch : ∀ ω w, ValidBatchSizes ((A ω).trace w)) :
    ∀ ω w, manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
      (returnedGradientCount ((A ω).trace w) : ℝ) := by
  intro ω w
  have hc := (gradientCountAccounting P.T R K ((A ω).trace w) (hbatch ω w)).1
  have hcast : (R : ℝ) ≤ (returnedGradientCount ((A ω).trace w) : ℝ) := by exact_mod_cast hc
  exact (P.moreau_rate_lower ρ A hsuccess).trans_le hcast

end ManuscriptBVProblem

namespace ManuscriptASProblem

def moreau (P : ManuscriptASProblem) : CalibratedPrimal P.T := P.calibration.primal P.chain

theorem moreau_is_envelope (P : ManuscriptASProblem) (x : Vec P.T) :
    P.moreau.envelope x = sInf (Set.range (fun v => P.population.Phi v + P.M * ‖v - x‖ ^ 2)) :=
  P.moreau.envelope_eq_inf x

theorem moreau_hasGradient (P : ManuscriptASProblem) (x : Vec P.T) :
    HasGradientAt P.moreau.envelope (P.moreau.envelopeGrad x) x := P.moreau.envelope_hasGradient x

theorem moreau_moments (P : ManuscriptASProblem) {R K : ℕ} (A : BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    (9 / 2 : ℝ) * P.ε ≤ stationarityNormRisk P.p P.moreau.envelopeGrad A ∧
      27 * P.ε ^ 2 ≤ stationarityRisk P.p P.moreau.envelopeGrad A :=
  P.calibration.moreau_moments P.chain P.base P.p P.p_pos P.p_le_one P.T_ge_eight A
    (pairGrowthRunProgress P.chain.dim_pos P.p
      (manuscriptAS_pair_growth P.chain P.calibration.lift P.p explicitSmoothGateCertificate) A) hR

theorem moreau_randomized_moments (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ} (A : Ω → BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal ((9 / 2 : ℝ) * P.ε) ≤ internalRandomNormRisk ρ P.p P.moreau.envelopeGrad A ∧
    ENNReal.ofReal (27 * P.ε ^ 2) ≤ internalRandomStationarityRisk ρ P.p P.moreau.envelopeGrad A :=
  moreau_integrated_margins ρ P.p P.ε _ A (fun ω => P.moreau_moments (A ω) hR)

theorem moreau_rate_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ} (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal (P.ε ^ 2)) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (R : ℝ) :=
  P.rate_threshold.trans_lt (round_lower_of_moreau_margins ρ P.p P.ε _ P.ε_pos _ A
    (fun h ω => P.moreau_moments (A ω) h) hsuccess)

theorem moreau_gradient_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ} (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.moreau.envelopeGrad A ≤ ENNReal.ofReal (P.ε ^ 2))
    (hbatch : ∀ ω w, ValidBatchSizes ((A ω).trace w)) :
    ∀ ω w, manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
      (returnedGradientCount ((A ω).trace w) : ℝ) := by
  intro ω w
  have hc := (gradientCountAccounting P.T R K ((A ω).trace w) (hbatch ω w)).1
  have hcast : (R : ℝ) ≤ (returnedGradientCount ((A ω).trace w) : ℝ) := by exact_mod_cast hc
  exact (P.moreau_rate_lower ρ A hsuccess).trans_le hcast

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
