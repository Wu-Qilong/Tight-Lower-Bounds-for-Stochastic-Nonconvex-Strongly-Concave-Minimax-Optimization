import ManuscriptGeneralMoreau
import ManuscriptLiftHessian
import ManuscriptLiftOracle
import ManuscriptCommonEvent
import ManuscriptKernelPolicy
import ManuscriptKernelExecution
import ManuscriptKernelComposition
import ManuscriptTapeCoordinates
import ManuscriptNativeTraceBridge
import ManuscriptStochasticMemory
import ManuscriptMemoryExecution
import ManuscriptMemoryCoordinates
import ManuscriptMemoryNative
import ManuscriptMemoryAELegal
import ManuscriptCausalGuard
import ManuscriptGuardPreservation
import ManuscriptGeneralProgress
import ManuscriptKernelComplexity

/-! Paper-facing statements for the manuscript locked in CHECKLIST_STATUS.md.
This module does not assert completion of the remaining modelling gates. -/
noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact

/-- Theorem 4.1's BV protocol has exactly one returned gradient per round.
The criterion parameter covers both expected norm and expected squared norm. -/
theorem theorem41_paper (P : ManuscriptBVProblem) (c : StationarityCriterion) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      KernelModel.complexity
        (fun I => I.ValidBV P.M P.μ P.Δ P.σ ∧ Rectangular.JointlyMeasurable I.oracle)
        1 c .primal P.M P.ε :=
  KernelModel.bv_complexity_lower P (by decide) c .primal

/-- Theorem 5.1's fixed finite batch bound; the rate constant is independent of K. -/
theorem theorem51_paper (P : ManuscriptASProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      KernelModel.complexity
        (fun I => I.ValidAS P.M P.μ P.Δ P.σ ∧ Rectangular.JointlyMeasurable I.oracle)
        K c .primal P.M P.ε :=
  KernelModel.as_complexity_lower P hK c .primal

/-- Corollary 5.2, BV branch: unchanged parameters, K=1, either moment criterion. -/
theorem corollary52_bv_paper (P : ManuscriptBVProblem) (c : StationarityCriterion) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      KernelModel.complexity
        (fun I => I.ValidBV P.M P.μ P.Δ P.σ ∧ Rectangular.JointlyMeasurable I.oracle)
        1 c .moreau P.M P.ε :=
  KernelModel.bv_complexity_lower P (by decide) c .moreau

/-- Corollary 5.2, AS branch: unchanged parameters and fixed finite K. -/
theorem corollary52_as_paper (P : ManuscriptASProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      KernelModel.complexity
        (fun I => I.ValidAS P.M P.μ P.Δ P.σ ∧ Rectangular.JointlyMeasurable I.oracle)
        K c .moreau P.M P.ε :=
  KernelModel.as_complexity_lower P hK c .moreau

/-- Reverse-triangle half of Lemma F.2, at the same output point. -/
theorem same_output_envelope_reverse {T : ℕ} (g : Vec T → Vec T)
    (M : ℝ) (hM : 0 < M)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ (5 * M / 64) * ‖x - y‖)
    (x u : Vec T) (hprox : g u = (2 * M) • (x - u)) :
    (123 / 128 : ℝ) * ‖g u‖ ≤ ‖g x‖ := by
  have ht : ‖g u‖ ≤ ‖g x - g u‖ + ‖g x‖ := by
    have hh' : ‖g u‖ ≤ ‖g u - g x‖ + ‖g x‖ := by
      simpa using norm_add_le (g u - g x) (g x)
    simpa only [norm_sub_rev (g u) (g x)] using hh'
  have hn : ‖g u‖ = (2 * M) * ‖x - u‖ := by
    rw [hprox, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hh := hlip x u
  nlinarith

/-- Lemma F.2: both inequalities for the actual Moreau envelope, with parameter 1/(2M). -/
theorem lemmaF2_paper {T : ℕ} (P : CalibratedPrimal T) (x : Vec T) :
    (123 / 128 : ℝ) * ‖gradient P.envelope x‖ ≤ ‖gradient P.F x‖ ∧
    ‖gradient P.F x‖ ≤ (133 / 128 : ℝ) * ‖gradient P.envelope x‖ := by
  rw [(P.envelope_hasGradient x).gradient, (P.grad_spec x).gradient]
  constructor
  · rw [P.envelopeGrad_eq]
    exact same_output_envelope_reverse P.g P.M P.M_pos P.grad_lip x (P.prox x)
      (P.prox_first_order x)
  · exact P.same_output_transfer x

/-- Lemma F.2 specialized to the calibrated hard family used in both appendices. -/
theorem lemmaF2_calibrated_paper {T : ℕ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) (x : Vec T) :
    (123 / 128 : ℝ) * ‖gradient (P.primal C).envelope x‖ ≤
        ‖gradient (canonicalLiftPhi C P.lift) x‖ ∧
    ‖gradient (canonicalLiftPhi C P.lift) x‖ ≤
        (133 / 128 : ℝ) * ‖gradient (P.primal C).envelope x‖ :=
  lemmaF2_paper (P.primal C) x

namespace GeneralLift

/-- Proposition F.1 with an explicit C2 base function and its actual gradient.
The Hessian is represented as a continuous linear operator (basis-independent). -/
theorem propositionF1_paper {T : ℕ} (P : LiftParameters) (H : Vec T → ℝ)
    (hC : ContDiff ℝ 2 H)
    (hl : ∀ u v, ‖gradient H u - gradient H v‖ ≤ P.ell * ‖u - v‖) :
    let C := Base.ofC2 P.ell H hC hl
    (∀ x, fderiv ℝ (gradient (canonicalLiftPhi P C)) x =
      (P.ν * P.γ ^ 2 * P.h) •
        (fderiv ℝ (gradient H) (P.β • canonicalLiftYStar P C x)).comp
          (resolventInv P C (P.β • canonicalLiftYStar P C x))) ∧
    (∀ x x', ‖gradient (canonicalLiftPhi P C) x - gradient (canonicalLiftPhi P C) x'‖ ≤
      (P.ν * P.γ ^ 2 * P.ell * P.h / P.μ) * ‖x - x'‖) :=
  propositionF1 P (Base.ofC2 P.ell H hC hl) hC

/-- Calibrated 5M/64 conclusion of Proposition F.1 for the actual primal gradient. -/
theorem propositionF1_calibrated_paper {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
    (M : ℝ) (hh : P.ell * P.h ≤ P.μ / 4) (hγ : P.γ ^ 2 = M / (4 * P.μ)) :
    ∀ x x', ‖gradient (canonicalLiftPhi P C) x - gradient (canonicalLiftPhi P C) x'‖ ≤
      (5 * M / 64) * ‖x - x'‖ := by
  have hν : P.ν ≤ 5 * P.μ / 4 := by
    change P.μ + P.ell * P.h ≤ _
    linarith
  intro x x'
  rw [(canonicalLiftPhi_grad P C x).gradient, (canonicalLiftPhi_grad P C x').gradient]
  exact canonicalLiftGradPhi_lipschitz_calibrated P C M hν hh hγ x x'

/-- The hard chain now supplies the C2 input to the general lift without a second axiom. -/
def paperChainBase (T : ℕ) (hT : 2 ≤ T) (ell : ℝ) (hell : 152 ≤ ell) : Base T ell :=
  Base.ofC2 ell (explicitFT T (by omega)) (lemmaB1_paper T hT).contDiff (by
    intro u v
    exact ((lemmaB1_paper T hT).grad_lipschitz u v).trans
      (mul_le_mul_of_nonneg_right hell (norm_nonneg _)))

/-- The named chain interface exposes the paper's actual gradient, not a supplied field. -/
theorem paperChainBase_gradient (T : ℕ) (hT : 2 ≤ T) (ell : ℝ) (hell : 152 ≤ ell) :
    (paperChainBase T hT ell hell).gradF = gradient (explicitFT T (by omega)) := rfl

/-- Proposition 3.1 with the paper's explicit C2 assumption and actual base gradient. -/
theorem proposition31_paper {T : ℕ} (P : LiftParameters) (H : Vec T → ℝ)
    (hC : ContDiff ℝ 2 H)
    (hl : ∀ u v, ‖gradient H u - gradient H v‖ ≤ P.ell * ‖u - v‖)
    (D g : ℝ) (hb : BddBelow (Set.range H))
    (hD : H 0 - sInf (Set.range H) ≤ D) (hg : ‖gradient H 0‖ ≤ g) :
    let C := Base.ofC2 P.ell H hC hl
    JointPrimitive (primitive P C).jointFunction (P.ν * (1 + P.γ ^ 2) + P.ell * P.h) P.μ ∧
    BddBelow (Set.range (canonicalLiftPhi P C)) ∧
    canonicalLiftPhi P C 0 - sInf (Set.range (canonicalLiftPhi P C)) ≤
      P.α * D + P.q ^ 2 * g ^ 2 / (2 * P.μ) ∧
    (∀ x, canonicalLiftPhi P C x = sSup (Set.range (liftedF P C x))) ∧
    (∀ x, ‖gradient H ((P.β * P.γ) • x)‖ ≤
      ((1 + P.ell * P.h / P.ν) / (P.γ * P.q)) * ‖gradient (canonicalLiftPhi P C) x‖) :=
  proposition31 P (Base.ofC2 P.ell H hC hl) D g hb hD hg

variable {T : ℕ} (P : LiftParameters) (C : Base T P.ell)
variable {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
variable (G : Vec T → Ω → Vec T)

/-- Proposition 3.1's variance implication, without an averaged-smoothness premise.
Measurability and second moments are explicit well-posedness hypotheses. -/
theorem proposition31_variance_paper
    (hGm : Measurable (fun z : Vec T × Ω => G z.1 z.2))
    (hG : ∀ u, MemLp (G u) 2 ρ)
    (hu : ∀ u, (∫ ξ, G u ξ ∂ρ) = C.gradF u)
    (v : ℝ) (hv : ∀ u, (∫ ξ, ‖G u ξ - C.gradF u‖ ^ 2 ∂ρ) ≤ v ^ 2) :
    Measurable (fun z : JointSpace T T × Ω => liftedField P G z.1 z.2) ∧
    (∀ z, MemLp (liftedField P G z) 2 ρ) ∧
    (∀ z, (∫ ξ, liftedField P G z ξ ∂ρ) = gradient (primitive P C).jointFunction z) ∧
    (∀ z, (∫ ξ, ‖liftedField P G z ξ - gradient (primitive P C).jointFunction z‖ ^ 2 ∂ρ) ≤
      P.q ^ 2 * v ^ 2) := by
  refine ⟨liftedField_jointlyMeasurable P G hGm, liftedField_memLp P ρ G hG, ?_, ?_⟩
  · intro z
    rw [(primitive P C).joint_gradient]
    exact liftedField_unbiased P C ρ G hG hu z
  · intro z
    rw [(primitive P C).joint_gradient]
    exact lifted_variance P C ρ G hv z

/-- Proposition 3.1's same-seed AS implication, without a variance-bound premise. -/
theorem proposition31_AS_paper
    (hGm : Measurable (fun z : Vec T × Ω => G z.1 z.2))
    (hG : ∀ u, MemLp (G u) 2 ρ)
    (hu : ∀ u, (∫ ξ, G u ξ ∂ρ) = C.gradF u)
    (S : ℝ) (hS : 0 ≤ S)
    (hAS : ∀ u w, (∫ ξ, ‖G u ξ - G w ξ‖ ^ 2 ∂ρ) ≤ S ^ 2 * ‖u - w‖ ^ 2) :
    Measurable (fun z : JointSpace T T × Ω => liftedField P G z.1 z.2) ∧
    (∀ z, MemLp (liftedField P G z) 2 ρ) ∧
    (∀ z, (∫ ξ, liftedField P G z ξ ∂ρ) = gradient (primitive P C).jointFunction z) ∧
    (∀ z w, (∫ ξ, ‖liftedField P G z ξ - liftedField P G w ξ‖ ^ 2 ∂ρ) ≤
      (P.ν * (1 + P.γ ^ 2) + P.h * S) ^ 2 * ‖z - w‖ ^ 2) := by
  refine ⟨liftedField_jointlyMeasurable P G hGm, liftedField_memLp P ρ G hG, ?_,
    liftedField_averaged_smooth P ρ G hG S hS hAS⟩
  intro z
  rw [(primitive P C).joint_gradient]
  exact liftedField_unbiased P C ρ G hG hu z

end GeneralLift
end NCSCPureStochasticLB.PaperExact
