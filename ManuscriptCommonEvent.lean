import ManuscriptOracleMeasure
import ManuscriptExactGate
import ManuscriptProgressExact

noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact

/-- Definition 3.4's common-seed events, expressed using an actual measure.
The existential query is inside each seed event, not outside the probability.
Unbiasedness and the parameter range are included by `probabilityPZeroChain`. -/
def CommonEventPZC {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (g : Vec T → Ω → Vec T) (p : ℝ) : Prop :=
    ρ {ξ | ∃ u, prog 0 (g u ξ) = prog (1 / 4) u + 1} ≤ ENNReal.ofReal p ∧
    ρ {ξ | ∃ u, prog 0 (g u ξ) > prog (1 / 4) u + 1} = 0

/-- Paper Definition 3.4, including the differentiable base function and unbiased oracle.
All probabilities use the same seed law. No samplewise scalar-loss assumption is made. -/
def probabilityPZeroChain {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (H : Vec T → ℝ) (g : Vec T → Ω → Vec T) (p : ℝ) : Prop :=
    IsProbabilityMeasure ρ ∧ 0 < p ∧ p ≤ 1 ∧ Differentiable ℝ H ∧
    (∀ u, Integrable (g u) ρ ∧ (∫ ξ, g u ξ ∂ρ) = gradient H u) ∧ CommonEventPZC ρ g p

/-- One common event controls an entire batch, with no union-bound factor K. -/
theorem CommonEventPZC.same_seed_batch {T K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} {g : Vec T → Ω → Vec T} {p : ℝ} (h : CommonEventPZC ρ g p)
    (u : Fin K → Vec T) :
    ρ {ξ | ∃ k, prog 0 (g (u k) ξ) = prog (1 / 4) (u k) + 1} ≤ ENNReal.ofReal p ∧
    ρ {ξ | ∃ k, prog 0 (g (u k) ξ) > prog (1 / 4) (u k) + 1} = 0 := by
  constructor
  · exact (measure_mono (by rintro ξ ⟨k, hk⟩; exact ⟨u k, hk⟩)).trans h.1
  · apply le_antisymm _ bot_le
    exact (measure_mono (by rintro ξ ⟨k, hk⟩; exact ⟨u k, hk⟩)).trans h.2.le

/-- The complement is a simultaneous statement over every query, not a per-query null set. -/
theorem CommonEventPZC.simultaneous_no_skip {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} {g : Vec T → Ω → Vec T} {p : ℝ} (h : CommonEventPZC ρ g p) :
    ∀ᵐ ξ ∂ρ, ∀ u, prog 0 (g u ξ) ≤ prog (1 / 4) u + 1 := by
  rw [ae_iff]
  simpa only [not_forall, not_le, Set.setOf_exists] using h.2

/-- Common Bernoulli event construction used by both parts of Lemma C.1. -/
theorem commonEventPZC_of_bernoulli {T : ℕ} (g : Vec T → Bool → Vec T) (p : ℝ)
    (hfalse : ∀ u, prog 0 (g u false) ≤ prog (1 / 4) u)
    (hnext : ∀ u b, prog 0 (g u b) ≤ prog (1 / 4) u + 1) :
    CommonEventPZC (bernoulliMeasure p) g p := by
  constructor
  · have hsub : {b | ∃ u, prog 0 (g u b) = prog (1 / 4) u + 1} ⊆ {true} := by
      rintro b ⟨u, hu⟩
      cases b
      · have := hfalse u; omega
      · simp
    exact (measure_mono hsub).trans (by simp [bernoulliMeasure_singleton])
  · have hempty : {b | ∃ u, prog 0 (g u b) > prog (1 / 4) u + 1} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
      exact fun u => hnext u b
    rw [hempty, measure_empty]

/-- Lemma C.1, BV oracle: full Definition 3.4, not pointwise-in-query probability. -/
theorem lemmaC1_bv_paper {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    probabilityPZeroChain (bernoulliMeasure p) (explicitFT T C.dim_pos) (bvBaseOracle C p) p := by
  refine ⟨bernoulliMeasure_probability p hp.le hp1, hp, hp1, ?_, ?_, ?_⟩
  · exact fun u => (C.grad_is_gradient u).differentiableAt
  · intro u
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_bernoulliMeasure p hp.le hp1]
    change bernoulliExpectVec p (fun b => bvBaseOracle C p u b) = _
    rw [bvBaseOracle_unbiased C p hp.ne']
    exact (C.grad_is_gradient u).gradient.symm
  · exact commonEventPZC_of_bernoulli _ p (bvBaseOracle_prog_false_le C p)
      (bvBaseOracle_prog_le_succ C p)

/-- Lemma C.1, smooth-gated AS oracle, with the exact smooth gate certificate. -/
theorem lemmaC1_as_paper {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    probabilityPZeroChain (bernoulliMeasure p) (explicitFT T C.dim_pos) (asBaseOracle C p) p := by
  refine ⟨bernoulliMeasure_probability p hp.le hp1, hp, hp1, ?_, ?_, ?_⟩
  · exact fun u => (C.grad_is_gradient u).differentiableAt
  · intro u
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_bernoulliMeasure p hp.le hp1]
    change bernoulliExpectVec p (fun b => asBaseOracle C p u b) = _
    rw [asBaseOracle_unbiased C p hp.ne']
    exact (C.grad_is_gradient u).gradient.symm
  · exact commonEventPZC_of_bernoulli _ p (asBaseOracle_prog_false_le C paperSmoothGateCertificate p)
      (asBaseOracle_prog_le_succ C p)

/-- The finite weighted probability equals probability under the genuine product measure. -/
theorem roundProb_eq_measureReal {R : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Set (RoundWorld R)) :
    roundProb p E = (iidRoundMeasure (bernoulliMeasure p) R).real E := by
  classical
  letI := roundMeasure_probability p hp0 hp1 R
  rw [iidRoundMeasure_bernoulli p hp0 hp1]
  have hi : (∫ w, E.indicator (fun _ => (1 : ℝ)) w ∂roundMeasure p R) = roundProb p E := by
    rw [integral_fintype _ Integrable.of_finite]
    unfold roundProb roundExpect
    apply Finset.sum_congr rfl
    intro w _
    change (roundMeasure p R {w}).toReal • E.indicator (fun _ => (1 : ℝ)) w = _
    rw [roundMeasure_singleton, ENNReal.toReal_ofReal (roundWeight_nonneg p hp0 hp1 w)]
    by_cases hw : w ∈ E <;> simp [Set.indicator_apply, hw, smul_eq_mul]
  rw [← hi, integral_indicator (Set.toFinite E).measurableSet]
  simp

/-- Exact support probability on an actual i.i.d. product space for the constructed runs. -/
theorem lemma35_bernoulli_measure_paper {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : BernoulliRun T R K O) (W : RunProgressWitness hT p A) :
    1 - p * R / T ≤ (iidRoundMeasure (bernoulliMeasure p) R).real
      {w | ∀ i ∈ supp (A.trace w).output, i.1 + 1 ≤ T - 1} := by
  rw [← roundProb_eq_measureReal p hp0 hp1]
  exact lemma35_bernoulli_support_paper hT p hp0 hp1 A W

end NCSCPureStochasticLB.PaperExact
