import ManuscriptProbability

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- A coordinate observable, zero for an unused slot. -/
def slotCoordinate {T : ℕ} (q : Option (Vec T × Vec T)) (c : Fin T ⊕ Fin T) : ℝ :=
  match q with
  | none => 0
  | some z => Sum.elim z.1 z.2 c

theorem slotCoordinate_ne_zero {T : ℕ} (q : Option (Vec T × Vec T)) (c : Fin T ⊕ Fin T) :
    slotCoordinate q c ≠ 0 ↔ ∃ z, q = some z ∧ c ∈ jointSupport z := by
  cases q <;> simp [slotCoordinate, jointSupport]

/-- Eliminate quantification over real query/response vectors from the support event. -/
theorem standardZeroRespecting_iff_coordinates {T N K : ℕ} (tr : InteractionTrace T N K) :
    StandardZeroRespectingTrace tr ↔
      (∀ t k c, slotCoordinate (tr.query t k) c ≠ 0 →
        ∃ s : Fin N, s.val < t.val ∧ ∃ j, slotCoordinate (tr.response s j) c ≠ 0) ∧
      (∀ c, Sum.elim tr.output (0 : Vec T) c ≠ 0 →
        ∃ s j, slotCoordinate (tr.response s j) c ≠ 0) := by
  simp only [slotCoordinate_ne_zero]
  constructor
  · intro h
    constructor
    · intro t k c hc
      obtain ⟨q, hq, hc⟩ := hc
      obtain ⟨s, hs, j, r, hr, hc⟩ := h.1 t k q hq hc
      exact ⟨s, hs, j, r, hr, hc⟩
    · intro c hc
      exact h.2 hc
  · rintro ⟨hq, ho⟩
    constructor
    · intro t k q he c hc
      exact hq t k c ⟨q, he, hc⟩
    · intro c hc
      exact ho c hc

/-- Observable regularity of a family of executions. No legality or risk assumption
is included: these fields concern only coordinate maps, active slots, and outputs. -/
structure ObservableMeasurable {Ω : Type*} [MeasurableSpace Ω] {T N K : ℕ}
    (tr : Ω → InteractionTrace T N K) : Prop where
  query : ∀ t k c, Measurable (fun ω => slotCoordinate ((tr ω).query t k) c)
  response : ∀ t k c, Measurable (fun ω => slotCoordinate ((tr ω).response t k) c)
  active : ∀ t k, MeasurableSet {ω | ((tr ω).query t k).isSome = true}
  output : Measurable (fun ω => (tr ω).output)

theorem ObservableMeasurable.support_event {Ω : Type*} [MeasurableSpace Ω] {T N K : ℕ}
    {tr : Ω → InteractionTrace T N K} (h : ObservableMeasurable tr) :
    MeasurableSet {ω | StandardZeroRespectingTrace (tr ω)} := by
  simp only [standardZeroRespecting_iff_coordinates, imp_iff_not_or, not_not,
    Set.setOf_forall, Set.setOf_exists, Set.setOf_and, Set.setOf_or]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro t
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro c
    exact (measurableSet_eq_fun (h.query t k c) measurable_const).union
      (MeasurableSet.iUnion (fun s => (MeasurableSet.const _).inter
        (MeasurableSet.iUnion (fun j => (measurableSet_eq_fun (h.response s j c) measurable_const).compl))))
  · apply MeasurableSet.iInter
    intro c
    have ho : Measurable (fun ω => Sum.elim (tr ω).output (0 : Vec T) c) := by
      cases c with
      | inl i => exact (measurable_pi_apply i).comp h.output
      | inr i => exact measurable_const
    exact (measurableSet_eq_fun ho measurable_const).union
      (MeasurableSet.iUnion (fun s => MeasurableSet.iUnion (fun j =>
        (measurableSet_eq_fun (h.response s j c) measurable_const).compl)))

theorem ObservableMeasurable.call_count {Ω : Type*} [MeasurableSpace Ω] {T N K : ℕ}
    {tr : Ω → InteractionTrace T N K} (h : ObservableMeasurable tr) :
    Measurable (fun ω => returnedGradientCount (tr ω)) := by
  unfold returnedGradientCount batchSize
  apply Finset.measurable_sum
  intro t ht
  apply Finset.measurable_sum
  intro k hk
  exact Measurable.ite (h.active t k) measurable_const measurable_const

theorem ObservableMeasurable.legal_event {Ω : Type*} [MeasurableSpace Ω] {T N K : ℕ}
    {tr : Ω → InteractionTrace T N K} (h : ObservableMeasurable tr) (B : ℕ) :
    MeasurableSet {ω | StandardZeroRespectingTrace (tr ω) ∧ returnedGradientCount (tr ω) ≤ B} :=
  h.support_event.inter (measurableSet_le h.call_count measurable_const)

theorem measurableSet_prod_of_finite_slices {Ω W : Type*} [MeasurableSpace Ω]
    [MeasurableSpace W] [Fintype W] [MeasurableSingletonClass W]
    (q : Ω × W → Prop) (hq : ∀ w, MeasurableSet {ω | q (ω, w)}) :
    MeasurableSet {z | q z} := by
  have he : {z | q z} = ⋃ w, (Prod.fst ⁻¹' {ω | q (ω, w)}) ∩ (Prod.snd ⁻¹' {w}) := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun w => ((hq w).preimage measurable_fst).inter
    ((measurableSet_singleton w).preimage measurable_snd))

/-- Finite-world observable regularity automatically gives joint regularity. -/
theorem ObservableMeasurable.joint {Ω : Type*} [MeasurableSpace Ω] {T N K : ℕ}
    (tr : Ω → RoundWorld N → InteractionTrace T N K)
    (h : ∀ w, ObservableMeasurable (fun ω => tr ω w)) :
    ObservableMeasurable (fun z : Ω × RoundWorld N => tr z.1 z.2) where
  query := fun t k c => measurable_from_prod_countable (fun w => (h w).query t k c)
  response := fun t k c => measurable_from_prod_countable (fun w => (h w).response t k c)
  active := fun t k => measurableSet_prod_of_finite_slices _ (fun w => (h w).active t k)
  output := measurable_from_prod_countable (fun w => (h w).output)

def ObservableOnline {Ω : Type*} [MeasurableSpace Ω] {T N K : ℕ}
    (O : StochasticOracle T Bool) (A : Ω → OnlinePolicy T K N) : Prop :=
  ∀ w, ObservableMeasurable (fun ω => (A ω).execute O w)

theorem ObservableOnline.productLegal {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Ω → OnlinePolicy T K N) (ho : ObservableOnline O A) (hl : AEOracleLegal ρ O p A) :
    ProductLegal ρ O p A := by
  have hm := (ObservableMeasurable.joint _ ho).legal_event N
  exact ⟨hm, (aeOracleLegal_iff_product ρ O p hp0 hp1 A hm).mp hl⟩

theorem ObservableOnline.loss_measurable {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    {T N K : ℕ} (O : StochasticOracle T Bool) (g : Vec T → Vec T)
    (A : Ω → OnlinePolicy T K N) (ho : ObservableOnline O A) (hg : Measurable g) :
    Measurable (onlineLoss c O g A) :=
  measurable_onlineLoss c O g A hg (fun w => (ho w).output)

/-- Under almost-sure legality, the oracle-independent repair preserves the full
trace on the joint probability space. -/
theorem repair_execute_ae_eq {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ) (A : Ω → OnlinePolicy T K N)
    (h : ProductLegal ρ O p A) :
    (fun z : Ω × RoundWorld N => ((A z.1).repairBudget).execute O z.2) =ᵐ[ρ.prod (roundMeasure p N)]
      (fun z => (A z.1).execute O z.2) := by
  filter_upwards [h.2] with z hz
  exact (A z.1).repairBudget_preserves O z.2 hz.1 hz.2

theorem repair_onlineLoss_ae_eq {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N) (h : ProductLegal ρ O p A) :
    onlineLoss c O g (fun ω => (A ω).repairBudget) =ᵐ[ρ.prod (roundMeasure p N)] onlineLoss c O g A := by
  filter_upwards [repair_execute_ae_eq ρ O p A h] with z hz
  cases c <;> simp only [onlineLoss, hz]

theorem repair_onlineLoss_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N) (h : ProductLegal ρ O p A)
    (hm : AEMeasurable (onlineLoss c O g A) (ρ.prod (roundMeasure p N))) :
    AEMeasurable (onlineLoss c O g (fun ω => (A ω).repairBudget)) (ρ.prod (roundMeasure p N)) :=
  hm.congr (repair_onlineLoss_ae_eq c ρ O p g A h).symm

theorem repair_product_risk_eq {Ω : Type*} [MeasurableSpace Ω] (c : StationarityCriterion)
    (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool) (p : ℝ)
    (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N) (h : ProductLegal ρ O p A) :
    (∫⁻ z, onlineLoss c O g (fun ω => (A ω).repairBudget) z ∂ρ.prod (roundMeasure p N)) =
      ∫⁻ z, onlineLoss c O g A z ∂ρ.prod (roundMeasure p N) :=
  lintegral_congr_ae (repair_onlineLoss_ae_eq c ρ O p g A h)

theorem ObservableOnline.repaired_loss_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (c : StationarityCriterion) (ρ : Measure Ω) {T N K : ℕ} (O : StochasticOracle T Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Vec T → Vec T) (A : Ω → OnlinePolicy T K N)
    (ho : ObservableOnline O A) (hg : Measurable g) (hl : AEOracleLegal ρ O p A) :
    AEMeasurable (onlineLoss c O g (fun ω => (A ω).repairBudget)) (ρ.prod (roundMeasure p N)) :=
  repair_onlineLoss_aemeasurable c ρ O p g A (ho.productLegal ρ O p hp0 hp1 A hl)
    (ho.loss_measurable c O g A hg).aemeasurable

theorem CalibratedPrimal.g_continuous {T : ℕ} (P : CalibratedPrimal T) : Continuous P.g := by
  have h : LipschitzWith ⟨5 * P.M / 64, by have := P.M_pos; positivity⟩ P.g := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm] using P.grad_lip x y
  exact h.continuous

theorem CalibratedPrimal.prox_continuous {T : ℕ} (P : CalibratedPrimal T) : Continuous P.prox := by
  have h : LipschitzWith 2 P.prox := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using P.prox_lipschitz x y
  exact h.continuous

theorem CalibratedPrimal.envelopeGrad_continuous {T : ℕ} (P : CalibratedPrimal T) :
    Continuous P.envelopeGrad := by
  have he : P.envelopeGrad = P.g ∘ P.prox := funext P.envelopeGrad_eq
  rw [he]
  exact P.g_continuous.comp P.prox_continuous

namespace ManuscriptBVProblem

theorem observable_product_budget_lower (P : ManuscriptBVProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (ho : ObservableOnline P.oracle A) (hl : AEOracleLegal ρ P.oracle P.p A)
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  exact P.product_online_budget_lower ρ A c
    (ho.productLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A hl)
    (ho.loss_measurable c P.oracle _ A P.moreau.g_continuous.measurable).aemeasurable h

theorem observable_product_moreau_budget_lower (P : ManuscriptBVProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (ho : ObservableOnline P.oracle A) (hl : AEOracleLegal ρ P.oracle P.p A)
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  exact P.product_online_moreau_budget_lower ρ A c
    (ho.productLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A hl)
    (ho.loss_measurable c P.oracle _ A P.moreau.envelopeGrad_continuous.measurable).aemeasurable h

end ManuscriptBVProblem

namespace ManuscriptASProblem

theorem observable_product_budget_lower (P : ManuscriptASProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (ho : ObservableOnline P.oracle A) (hl : AEOracleLegal ρ P.oracle P.p A)
    (h : (∫⁻ z, onlineLoss c P.oracle P.population.gradPhi A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  exact P.product_online_budget_lower ρ A c
    (ho.productLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A hl)
    (ho.loss_measurable c P.oracle _ A P.moreau.g_continuous.measurable).aemeasurable h

theorem observable_product_moreau_budget_lower (P : ManuscriptASProblem) {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {N K : ℕ} (A : Ω → OnlinePolicy P.T K N)
    (c : StationarityCriterion) (ho : ObservableOnline P.oracle A) (hl : AEOracleLegal ρ P.oracle P.p A)
    (h : (∫⁻ z, onlineLoss c P.oracle P.moreau.envelopeGrad A z ∂ρ.prod (roundMeasure P.p N)) ≤ c.target P.ε) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (N : ℝ) := by
  exact P.product_online_moreau_budget_lower ρ A c
    (ho.productLegal ρ P.oracle P.p (le_of_lt P.p_pos) P.p_le_one A hl)
    (ho.loss_measurable c P.oracle _ A P.moreau.envelopeGrad_continuous.measurable).aemeasurable h

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
