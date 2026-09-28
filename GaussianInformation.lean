import NCSCPureStochasticLB

open Real MeasureTheory ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact

/-! Elementary density algebra used by the internal proof of Proposition 4.6. -/

theorem gaussianPDFReal_ratio_same_variance
    (m₁ m₂ v x : ℝ) (hv : 0 < v) :
    gaussianPDFReal m₁ ⟨v, le_of_lt hv⟩ x /
        gaussianPDFReal m₂ ⟨v, le_of_lt hv⟩ x =
      Real.exp (((x - m₂) ^ 2 - (x - m₁) ^ 2) / (2 * v)) := by
  simp only [gaussianPDFReal_def, NNReal.coe_mk]
  have hs : 0 < Real.sqrt (2 * Real.pi * v) := by positivity
  rw [div_eq_iff (mul_ne_zero (inv_ne_zero (ne_of_gt hs)) (Real.exp_ne_zero _))]
  have hexp : ((x - m₂) ^ 2 - (x - m₁) ^ 2) / (2 * v) =
      (-((x - m₁) ^ 2) / (2 * v)) - (-((x - m₂) ^ 2) / (2 * v)) := by
    field_simp [ne_of_gt hv]
    ring
  rw [hexp]
  rw [Real.exp_sub]
  field_simp [ne_of_gt hs, Real.exp_ne_zero]

theorem log_gaussianPDFReal_ratio_same_variance
    (m₁ m₂ v x : ℝ) (hv : 0 < v) :
    Real.log (gaussianPDFReal m₁ ⟨v, le_of_lt hv⟩ x /
        gaussianPDFReal m₂ ⟨v, le_of_lt hv⟩ x) =
      ((x - m₂) ^ 2 - (x - m₁) ^ 2) / (2 * v) := by
  rw [gaussianPDFReal_ratio_same_variance m₁ m₂ v x hv, Real.log_exp]

theorem rnDeriv_gaussianReal_same_variance
    (m₁ m₂ : ℝ) (v : NNReal) (hv : v ≠ 0) :
    (gaussianReal m₁ v).rnDeriv (gaussianReal m₂ v) =ᵐ[gaussianReal m₂ v]
      fun x => gaussianPDF m₁ v x / gaussianPDF m₂ v x := by
  rw [gaussianReal_of_var_ne_zero m₁ hv, gaussianReal_of_var_ne_zero m₂ hv]
  letI : SigmaFinite (volume.withDensity (gaussianPDF m₁ v)) :=
    SigmaFinite.withDensity_of_ne_top
      (ae_of_all volume (fun _ => gaussianPDF_ne_top))
  have hright := Measure.rnDeriv_withDensity_right
    (volume.withDensity (gaussianPDF m₁ v)) volume
    (measurable_gaussianPDF m₂ v).aemeasurable
    (ae_of_all volume (fun x => (gaussianPDF_pos m₂ hv x).ne'))
    (ae_of_all volume (fun _ => gaussianPDF_ne_top))
  have hleft := Measure.rnDeriv_withDensity volume (measurable_gaussianPDF m₁ v)
  have hac : volume.withDensity (gaussianPDF m₂ v) ≪ volume :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le hright, hac.ae_le hleft] with x hxR hxL
  rw [hxR, hxL]
  simp [div_eq_mul_inv, mul_comm]

theorem llr_gaussianReal_same_variance
    (m₁ m₂ : ℝ) (v : NNReal) (hv : 0 < v) :
    llr (gaussianReal m₁ v) (gaussianReal m₂ v) =ᵐ[gaussianReal m₁ v]
      fun x => ((x - m₂) ^ 2 - (x - m₁) ^ 2) / (2 * (v : ℝ)) := by
  have hv0 : v ≠ 0 := ne_of_gt hv
  have h₁vol : gaussianReal m₁ v ≪ volume :=
    gaussianReal_absolutelyContinuous m₁ hv0
  have hvol₂ : volume ≪ gaussianReal m₂ v :=
    gaussianReal_absolutelyContinuous' m₂ hv0
  have h₁₂ : gaussianReal m₁ v ≪ gaussianReal m₂ v := h₁vol.trans hvol₂
  have hrn := rnDeriv_gaussianReal_same_variance m₁ m₂ v hv0
  filter_upwards [h₁₂.ae_le hrn] with x hx
  change Real.log (((gaussianReal m₁ v).rnDeriv (gaussianReal m₂ v) x).toReal) = _
  rw [hx, ENNReal.toReal_div, toReal_gaussianPDF,
    toReal_gaussianPDF]
  exact log_gaussianPDFReal_ratio_same_variance m₁ m₂ (v : ℝ) x
    (NNReal.coe_pos.mpr hv)

theorem gaussianStatisticMeasure_mean
    (Lbar θ σ : ℝ) :
    (∫ x : ℝ, x ∂gaussianStatisticMeasure Lbar θ σ) = -Lbar * θ := by
  letI : IsProbabilityMeasure (gaussianNoiseMeasure σ) := by
    unfold gaussianNoiseMeasure
    infer_instance
  let m : ℝ := -Lbar * θ
  have hmap : Measure.map (fun z : ℝ => z + m) (gaussianNoiseMeasure σ) =
      gaussianStatisticMeasure Lbar θ σ := by
    simpa [gaussianNoiseMeasure, gaussianStatisticMeasure, m] using
      (gaussianReal_map_add_const
        (μ := (0 : ℝ)) (v := gaussianVariance σ) m)
  rw [← hmap]
  change (∫ x : ℝ, id x ∂Measure.map (fun z : ℝ => id z + m)
    (gaussianNoiseMeasure σ)) = _
  rw [integral_map (measurable_id.add_const m).aemeasurable
    measurable_id.aestronglyMeasurable]
  simp only [id_eq]
  rw [integral_add (gaussianNoiseMeasure_integrable_id σ) (integrable_const m),
    gaussianNoiseMeasure_mean_zero, integral_const]
  simp [m, gaussianNoiseMeasure_probability]

theorem gaussianReal_integrable_id_from_sigma (m σ : ℝ) :
    Integrable (fun x : ℝ => x)
      (gaussianReal m (gaussianVariance σ)) := by
  letI : IsProbabilityMeasure (gaussianNoiseMeasure σ) := by
    unfold gaussianNoiseMeasure
    infer_instance
  have hmap : Measure.map (fun z : ℝ => z + m) (gaussianNoiseMeasure σ) =
      gaussianReal m (gaussianVariance σ) := by
    simpa [gaussianNoiseMeasure] using
      (gaussianReal_map_add_const
        (μ := (0 : ℝ)) (v := gaussianVariance σ) m)
  rw [← hmap]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_id.add_const m).aemeasurable).2
  simpa only [Function.comp_apply, id_eq] using
    (gaussianNoiseMeasure_integrable_id σ).add (integrable_const m)

theorem toReal_klDiv_gaussianReal_same_variance_sigma
    (m₁ m₂ σ : ℝ) (hσ : 0 < σ) :
    (InformationTheory.klDiv
      (gaussianReal m₁ (gaussianVariance σ))
      (gaussianReal m₂ (gaussianVariance σ))).toReal =
      (m₁ - m₂) ^ 2 / (2 * σ ^ 2) := by
  let v := gaussianVariance σ
  have hv : 0 < v := by
    rw [show v = gaussianVariance σ by rfl, gaussianVariance]
    exact_mod_cast sq_pos_of_pos hσ
  have h₁vol : gaussianReal m₁ v ≪ volume :=
    gaussianReal_absolutelyContinuous m₁ (ne_of_gt hv)
  have hvol₂ : volume ≪ gaussianReal m₂ v :=
    gaussianReal_absolutelyContinuous' m₂ (ne_of_gt hv)
  have h₁₂ : gaussianReal m₁ v ≪ gaussianReal m₂ v := h₁vol.trans hvol₂
  rw [InformationTheory.toReal_klDiv_of_measure_eq h₁₂ (by simp)]
  rw [integral_congr_ae (llr_gaussianReal_same_variance m₁ m₂ v hv)]
  have hvreal : (v : ℝ) = σ ^ 2 := by rfl
  let c : ℝ := (m₁ - m₂) / (v : ℝ)
  let d : ℝ := (m₂ ^ 2 - m₁ ^ 2) / (2 * (v : ℝ))
  have hfun : (fun x : ℝ => ((x - m₂) ^ 2 - (x - m₁) ^ 2) /
      (2 * (v : ℝ))) = fun x => c * x + d := by
    funext x
    dsimp [c, d]
    field_simp [ne_of_gt (NNReal.coe_pos.mpr hv)]
    ring
  rw [hfun]
  have hxi : Integrable (fun x : ℝ => x) (gaussianReal m₁ v) := by
    simpa [v] using gaussianReal_integrable_id_from_sigma m₁ σ
  have hci : Integrable (fun x : ℝ => c * x) (gaussianReal m₁ v) :=
    hxi.const_mul c
  rw [integral_add hci (integrable_const d), integral_const_mul]
  have hmean : (∫ x : ℝ, x ∂gaussianReal m₁ v) = m₁ := by
    simpa [gaussianStatisticMeasure, v] using
      gaussianStatisticMeasure_mean 1 (-m₁) σ
  rw [hmean, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.one_toReal, one_smul]
  dsimp [c, d]
  rw [hvreal]
  field_simp [ne_of_gt hσ]
  ring

theorem gaussianStatisticMeasure_klDiv_two_point
    (Lbar a σ : ℝ) (hσ : 0 < σ) :
    (InformationTheory.klDiv
      (gaussianStatisticMeasure Lbar a σ)
      (gaussianStatisticMeasure Lbar (-a) σ)).toReal =
      (2 * Lbar * a) ^ 2 / (2 * σ ^ 2) := by
  rw [gaussianStatisticMeasure, gaussianStatisticMeasure]
  convert toReal_klDiv_gaussianReal_same_variance_sigma
    (-Lbar * a) (-Lbar * (-a)) σ hσ using 1
  ring

theorem gaussianStatisticMeasure_sum_marginal_klDiv
    (R : ℕ) (Lbar a σ : ℝ) (hσ : 0 < σ) :
    (∑ _t : Fin R,
      (InformationTheory.klDiv
        (gaussianStatisticMeasure Lbar a σ)
        (gaussianStatisticMeasure Lbar (-a) σ)).toReal) =
      (R : ℝ) * (2 * Lbar * a) ^ 2 / (2 * σ ^ 2) := by
  rw [gaussianStatisticMeasure_klDiv_two_point Lbar a σ hσ]
  simp [div_eq_mul_inv]
  ring

section ProductRadonNikodym

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ₁ ν₁ : Measure α} {μ₂ ν₂ : Measure β}

theorem rnDeriv_prod_of_ac [SigmaFinite μ₁] [SigmaFinite ν₁]
    [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) =ᵐ[ν₁.prod ν₂]
      fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 := by
  let f₁ := μ₁.rnDeriv ν₁
  let f₂ := μ₂.rnDeriv ν₂
  have hm₁ : ν₁.withDensity (μ₁.rnDeriv ν₁) = μ₁ :=
    Measure.withDensity_rnDeriv_eq μ₁ ν₁ h₁
  have hm₂ : ν₂.withDensity (μ₂.rnDeriv ν₂) = μ₂ :=
    Measure.withDensity_rnDeriv_eq μ₂ ν₂ h₂
  have hprod : μ₁.prod μ₂ = (ν₁.prod ν₂).withDensity
      (fun z => f₁ z.1 * f₂ z.2) := by
    rw [← hm₁, ← hm₂]
    exact prod_withDensity (μ := ν₁) (ν := ν₂)
      (Measure.measurable_rnDeriv μ₁ ν₁) (Measure.measurable_rnDeriv μ₂ ν₂)
  rw [hprod]
  simpa [f₁, f₂] using Measure.rnDeriv_withDensity (ν₁.prod ν₂)
    (((Measure.measurable_rnDeriv μ₁ ν₁).comp measurable_fst).mul
      ((Measure.measurable_rnDeriv μ₂ ν₂).comp measurable_snd))

theorem llr_prod_of_ac [SigmaFinite μ₁] [SigmaFinite ν₁]
    [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    llr (μ₁.prod μ₂) (ν₁.prod ν₂) =ᵐ[μ₁.prod μ₂]
      fun z => llr μ₁ ν₁ z.1 + llr μ₂ ν₂ z.2 := by
  have hp : μ₁.prod μ₂ ≪ ν₁.prod ν₂ := h₁.prod h₂
  have hrn := hp.ae_le (rnDeriv_prod_of_ac h₁ h₂)
  have hpos₁ : ∀ᵐ z ∂μ₁.prod μ₂, 0 < μ₁.rnDeriv ν₁ z.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioi.preimage
        ((Measure.measurable_rnDeriv μ₁ ν₁).comp measurable_fst))).2
    filter_upwards [Measure.rnDeriv_pos h₁] with x hx
    exact ae_of_all _ (fun _ => hx)
  have hpos₂ : ∀ᵐ z ∂μ₁.prod μ₂, 0 < μ₂.rnDeriv ν₂ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioi.preimage
        ((Measure.measurable_rnDeriv μ₂ ν₂).comp measurable_snd))).2
    exact ae_of_all _ (fun x => Measure.rnDeriv_pos h₂)
  have htop₁ : ∀ᵐ z ∂μ₁.prod μ₂, μ₁.rnDeriv ν₁ z.1 < (⊤ : ENNReal) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Iio.preimage
        ((Measure.measurable_rnDeriv μ₁ ν₁).comp measurable_fst))).2
    filter_upwards [h₁.ae_le (Measure.rnDeriv_lt_top μ₁ ν₁)] with x hx
    exact ae_of_all _ (fun _ => hx)
  have htop₂ : ∀ᵐ z ∂μ₁.prod μ₂, μ₂.rnDeriv ν₂ z.2 < (⊤ : ENNReal) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Iio.preimage
        ((Measure.measurable_rnDeriv μ₂ ν₂).comp measurable_snd))).2
    exact ae_of_all _ (fun x => h₂.ae_le (Measure.rnDeriv_lt_top μ₂ ν₂))
  filter_upwards [hrn, hpos₁, hpos₂, htop₁, htop₂] with z hz hp₁ hp₂ ht₁ ht₂
  change Real.log (((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) z).toReal) =
    Real.log ((μ₁.rnDeriv ν₁ z.1).toReal) +
      Real.log ((μ₂.rnDeriv ν₂ z.2).toReal)
  rw [hz, ENNReal.toReal_mul, Real.log_mul]
  · exact (ENNReal.toReal_pos hp₁.ne' ht₁.ne).ne'
  · exact (ENNReal.toReal_pos hp₂.ne' ht₂.ne).ne'

theorem toReal_klDiv_prod_add [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂)
    (hi₁ : Integrable (llr μ₁ ν₁) μ₁)
    (hi₂ : Integrable (llr μ₂ ν₂) μ₂) :
    (InformationTheory.klDiv (μ₁.prod μ₂) (ν₁.prod ν₂)).toReal =
      (InformationTheory.klDiv μ₁ ν₁).toReal +
        (InformationTheory.klDiv μ₂ ν₂).toReal := by
  let f : α × β → ℝ := fun z => llr μ₁ ν₁ z.1
  let g : α × β → ℝ := fun z => llr μ₂ ν₂ z.2
  have hf : Integrable f (μ₁.prod μ₂) := by
    have h := hi₁.mul_prod (integrable_const (μ := μ₂) (1 : ℝ))
    simpa [f] using h
  have hg : Integrable g (μ₁.prod μ₂) := by
    have h := (integrable_const (μ := μ₁) (1 : ℝ)).mul_prod hi₂
    simpa [g] using h
  have hp : μ₁.prod μ₂ ≪ ν₁.prod ν₂ := h₁.prod h₂
  rw [InformationTheory.toReal_klDiv_of_measure_eq hp (by simp)]
  rw [integral_congr_ae (llr_prod_of_ac h₁ h₂)]
  change (∫ z, f z + g z ∂μ₁.prod μ₂) = _
  rw [integral_add hf hg]
  have hfint : (∫ z, f z ∂μ₁.prod μ₂) = ∫ x, llr μ₁ ν₁ x ∂μ₁ := by
    rw [integral_prod f hf]
    simp [f]
  have hgint : (∫ z, g z ∂μ₁.prod μ₂) = ∫ y, llr μ₂ ν₂ y ∂μ₂ := by
    rw [integral_prod g hg]
    simp [g]
  rw [hfint, hgint,
    ← InformationTheory.toReal_klDiv_of_measure_eq h₁ (by simp),
    ← InformationTheory.toReal_klDiv_of_measure_eq h₂ (by simp)]

end ProductRadonNikodym

section MapInvariance

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ ν : Measure α} {e : α → β}

theorem llr_map_comp_of_measurableEmbedding [SigmaFinite μ] [SigmaFinite ν]
    (he : MeasurableEmbedding e) (h : μ ≪ ν) :
    (fun x => llr (μ.map e) (ν.map e) (e x)) =ᵐ[μ] llr μ ν := by
  have hrn := h.ae_le (he.rnDeriv_map μ ν)
  filter_upwards [hrn] with x hx
  simp only [llr_def, Function.comp_apply]
  rw [hx]

theorem toReal_klDiv_map_of_measurableEmbedding
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (he : MeasurableEmbedding e) (h : μ ≪ ν) :
    (InformationTheory.klDiv (μ.map e) (ν.map e)).toReal =
      (InformationTheory.klDiv μ ν).toReal := by
  have hmap : μ.map e ≪ ν.map e := he.absolutelyContinuous_map h
  rw [InformationTheory.toReal_klDiv_of_measure_eq hmap (by simp [he.measurable]),
    InformationTheory.toReal_klDiv_of_measure_eq h (by simp)]
  rw [integral_map he.measurable.aemeasurable
    (stronglyMeasurable_llr (μ.map e) (ν.map e)).aestronglyMeasurable]
  exact integral_congr_ae (llr_map_comp_of_measurableEmbedding he h)

theorem integrable_llr_map_of_measurableEmbedding [SigmaFinite μ] [SigmaFinite ν]
    (he : MeasurableEmbedding e) (h : μ ≪ ν)
    (hi : Integrable (llr μ ν) μ) :
    Integrable (llr (μ.map e) (ν.map e)) (μ.map e) := by
  apply (integrable_map_measure
    (stronglyMeasurable_llr (μ.map e) (ν.map e)).aestronglyMeasurable
    he.measurable.aemeasurable).2
  exact hi.congr (llr_map_comp_of_measurableEmbedding he h).symm

end MapInvariance

section FiniteProductKL

variable {α : Type*} [MeasurableSpace α] (μ ν : Measure α)

theorem absolutelyContinuous_pi_const [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≪ ν) :
    ∀ R : ℕ, (Measure.pi fun _ : Fin R => μ) ≪
      (Measure.pi fun _ : Fin R => ν) := by
  intro R
  induction R with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      let pμ := Measure.pi fun _ : Fin (n + 1) => μ
      let pν := Measure.pi fun _ : Fin (n + 1) => ν
      let tμ := Measure.pi fun _ : Fin n => μ
      let tν := Measure.pi fun _ : Fin n => ν
      have hmμ : Measure.map e pμ = μ.prod tμ := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) 0).map_eq
      have hmν : Measure.map e pν = ν.prod tν := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ν) 0).map_eq
      have hmap : Measure.map e pμ ≪ Measure.map e pν := by
        rw [hmμ, hmν]
        exact h.prod ih
      have hback : Measure.map e.symm (Measure.map e pμ) ≪
          Measure.map e.symm (Measure.map e pν) :=
        e.symm.measurableEmbedding.absolutelyContinuous_map hmap
      simpa only [e, MeasurableEquiv.map_symm_map] using hback

theorem integrable_llr_pi_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ ≪ ν) (hi : Integrable (llr μ ν) μ) :
    ∀ R : ℕ, Integrable
      (llr (Measure.pi fun _ : Fin R => μ) (Measure.pi fun _ : Fin R => ν))
      (Measure.pi fun _ : Fin R => μ) := by
  intro R
  induction R with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp [llr_def]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      let pμ := Measure.pi fun _ : Fin (n + 1) => μ
      let pν := Measure.pi fun _ : Fin (n + 1) => ν
      let tμ := Measure.pi fun _ : Fin n => μ
      let tν := Measure.pi fun _ : Fin n => ν
      have hmμ : Measure.map e pμ = μ.prod tμ := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) 0).map_eq
      have hmν : Measure.map e pν = ν.prod tν := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ν) 0).map_eq
      have htac : tμ ≪ tν := absolutelyContinuous_pi_const μ ν h n
      let f : α × (Fin n → α) → ℝ := fun z => llr μ ν z.1
      let g : α × (Fin n → α) → ℝ := fun z => llr tμ tν z.2
      have hf : Integrable f (μ.prod tμ) := by
        have hf' := hi.mul_prod (integrable_const (μ := tμ) (1 : ℝ))
        simpa [f] using hf'
      have hg : Integrable g (μ.prod tμ) := by
        have hg' := (integrable_const (μ := μ) (1 : ℝ)).mul_prod ih
        simpa [g] using hg'
      have hprod : Integrable (llr (μ.prod tμ) (ν.prod tν)) (μ.prod tμ) := by
        exact (hf.add hg).congr (llr_prod_of_ac h htac).symm
      have hback := integrable_llr_map_of_measurableEmbedding
        e.symm.measurableEmbedding (h.prod htac) hprod
      have hmμ' : Measure.map e.symm (μ.prod tμ) = pμ := by
        rw [← hmμ]
        simpa only [e, MeasurableEquiv.map_symm_map]
      have hmν' : Measure.map e.symm (ν.prod tν) = pν := by
        rw [← hmν]
        simpa only [e, MeasurableEquiv.map_symm_map]
      rw [hmμ', hmν'] at hback
      exact hback

theorem toReal_klDiv_pi_const
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ ≪ ν) (hi : Integrable (llr μ ν) μ)
    (hacpi : ∀ R : ℕ,
      (Measure.pi fun _ : Fin R => μ) ≪ (Measure.pi fun _ : Fin R => ν))
    (hpi : ∀ R : ℕ, Integrable
      (llr (Measure.pi fun _ : Fin R => μ) (Measure.pi fun _ : Fin R => ν))
      (Measure.pi fun _ : Fin R => μ)) :
    ∀ R : ℕ,
      (InformationTheory.klDiv
        (Measure.pi fun _ : Fin R => μ)
        (Measure.pi fun _ : Fin R => ν)).toReal =
        (R : ℝ) * (InformationTheory.klDiv μ ν).toReal := by
  intro R
  induction R with
  | zero =>
      have heq : (Measure.pi fun _ : Fin 0 => μ) =
          (Measure.pi fun _ : Fin 0 => ν) := by
        rw [Measure.pi_of_empty, Measure.pi_of_empty]
      rw [heq, InformationTheory.klDiv_self]
      simp
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      let pμ := Measure.pi fun _ : Fin (n + 1) => μ
      let pν := Measure.pi fun _ : Fin (n + 1) => ν
      let tμ := Measure.pi fun _ : Fin n => μ
      let tν := Measure.pi fun _ : Fin n => ν
      have hmμ : Measure.map e pμ = μ.prod tμ := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) 0).map_eq
      have hmν : Measure.map e pν = ν.prod tν := by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ν) 0).map_eq
      have hpac : pμ ≪ pν := hacpi (n + 1)
      have hinv := toReal_klDiv_map_of_measurableEmbedding
        e.measurableEmbedding hpac
      rw [hmμ, hmν] at hinv
      rw [← hinv]
      have htac : tμ ≪ tν := hacpi n
      rw [toReal_klDiv_prod_add h htac hi (hpi n)]
      rw [ih]
      push_cast
      ring

theorem toReal_klDiv_pi_const_of_integrable
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ ≪ ν) (hi : Integrable (llr μ ν) μ) :
    ∀ R : ℕ,
      (InformationTheory.klDiv
        (Measure.pi fun _ : Fin R => μ)
        (Measure.pi fun _ : Fin R => ν)).toReal =
        (R : ℝ) * (InformationTheory.klDiv μ ν).toReal := by
  exact toReal_klDiv_pi_const μ ν h hi
    (absolutelyContinuous_pi_const μ ν h)
    (integrable_llr_pi_const μ ν h hi)

end FiniteProductKL

theorem integrable_llr_gaussianReal_same_variance_sigma
    (m₁ m₂ σ : ℝ) (hσ : 0 < σ) :
    Integrable
      (llr (gaussianReal m₁ (gaussianVariance σ))
        (gaussianReal m₂ (gaussianVariance σ)))
      (gaussianReal m₁ (gaussianVariance σ)) := by
  let v := gaussianVariance σ
  have hv : 0 < v := by
    rw [show v = gaussianVariance σ by rfl, gaussianVariance]
    exact_mod_cast sq_pos_of_pos hσ
  let c : ℝ := (m₁ - m₂) / (v : ℝ)
  let d : ℝ := (m₂ ^ 2 - m₁ ^ 2) / (2 * (v : ℝ))
  have hfun : (fun x : ℝ => ((x - m₂) ^ 2 - (x - m₁) ^ 2) /
      (2 * (v : ℝ))) = fun x => c * x + d := by
    funext x
    dsimp [c, d]
    field_simp [ne_of_gt (NNReal.coe_pos.mpr hv)]
    ring
  have hx : Integrable (fun x : ℝ => x) (gaussianReal m₁ v) := by
    simpa [v] using gaussianReal_integrable_id_from_sigma m₁ σ
  have haffine : Integrable (fun x : ℝ => c * x + d) (gaussianReal m₁ v) :=
    (hx.const_mul c).add (integrable_const d)
  have hllr : llr (gaussianReal m₁ v) (gaussianReal m₂ v) =ᵐ[
      gaussianReal m₁ v] fun x => c * x + d :=
    (llr_gaussianReal_same_variance m₁ m₂ v hv).trans
      (ae_of_all _ fun x => congrFun hfun x)
  exact haffine.congr hllr.symm

theorem toReal_klDiv_gaussianReal_pi_same_variance_sigma
    (R : ℕ) (m₁ m₂ σ : ℝ) (hσ : 0 < σ) :
    (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R => gaussianReal m₁ (gaussianVariance σ))
      (Measure.pi fun _ : Fin R => gaussianReal m₂ (gaussianVariance σ))).toReal =
      (R : ℝ) * ((m₁ - m₂) ^ 2 / (2 * σ ^ 2)) := by
  have hv : gaussianVariance σ ≠ 0 := by
    exact ne_of_gt (by
      rw [gaussianVariance]
      exact_mod_cast sq_pos_of_pos hσ)
  have hac : gaussianReal m₁ (gaussianVariance σ) ≪
      gaussianReal m₂ (gaussianVariance σ) :=
    (gaussianReal_absolutelyContinuous m₁ hv).trans
      (gaussianReal_absolutelyContinuous' m₂ hv)
  rw [toReal_klDiv_pi_const_of_integrable _ _ hac
    (integrable_llr_gaussianReal_same_variance_sigma m₁ m₂ σ hσ) R]
  rw [toReal_klDiv_gaussianReal_same_variance_sigma m₁ m₂ σ hσ]

theorem gaussianStatisticMeasure_pi_klDiv_two_point
    (R : ℕ) (Lbar a σ : ℝ) (hσ : 0 < σ) :
    (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar a σ)
      (Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar (-a) σ)).toReal =
      (R : ℝ) * ((2 * Lbar * a) ^ 2 / (2 * σ ^ 2)) := by
  rw [gaussianStatisticMeasure, gaussianStatisticMeasure]
  convert toReal_klDiv_gaussianReal_pi_same_variance_sigma
    R (-Lbar * a) (-Lbar * (-a)) σ hσ using 1
  ring

/-- The canonical transcript with its product-Gaussian KL field discharged internally. -/
noncomputable def canonicalGaussianTranscriptExact
    (R : ℕ) (Lbar a σ : ℝ) (hσ : 0 < σ) :
    GaussianTranscriptExperiment R Lbar a σ := by
  apply canonicalGaussianTranscript R Lbar a σ
  rw [gaussianStatisticMeasure_pi_klDiv_two_point R Lbar a σ hσ]
  ring

theorem two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have h := Real.le_log_one_add_of_nonneg (sub_nonneg.mpr hx)
  convert h using 1 <;> ring

/-- A deliberately non-optimal binary Pinsker inequality.  Its constant is
already sufficient for Proposition 4.6 after shrinking the universal round
constant. -/
theorem binaryRelativeEntropy_sq_gap
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    (p - q) ^ 2 / 2 ≤
      p * Real.log (p / q) +
        (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have hp_nonneg : 0 ≤ p := le_of_lt hp0
  have hq_nonneg : 0 ≤ q := le_of_lt hq0
  have hpc : 0 < 1 - p := sub_pos.mpr hp1
  have hqc : 0 < 1 - q := sub_pos.mpr hq1
  by_cases hpq : q ≤ p
  · have hratio : 1 ≤ p / q := by
      apply (le_div_iff₀ hq0).2
      simpa using hpq
    have hlog₁ := two_mul_sub_div_add_le_log hratio
    have hlog₂ := Real.one_sub_inv_le_log_of_pos (div_pos hpc hqc)
    have hp_mul : p * (2 * (p / q - 1) / (p / q + 1)) ≤
        p * Real.log (p / q) := mul_le_mul_of_nonneg_left hlog₁ hp_nonneg
    have hpc_mul : (1 - p) * (1 - ((1 - p) / (1 - q))⁻¹) ≤
        (1 - p) * Real.log ((1 - p) / (1 - q)) :=
      mul_le_mul_of_nonneg_left hlog₂ (le_of_lt hpc)
    have halg : p * (2 * (p / q - 1) / (p / q + 1)) +
        (1 - p) * (1 - ((1 - p) / (1 - q))⁻¹) =
        (p - q) ^ 2 / (p + q) := by
      field_simp [ne_of_gt hq0, ne_of_gt hqc, ne_of_gt (add_pos hp0 hq0)]
      ring
    calc
      (p - q) ^ 2 / 2 ≤ (p - q) ^ 2 / (p + q) := by
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (add_pos hp0 hq0)).2
        nlinarith [sq_nonneg (p - q)]
      _ = p * (2 * (p / q - 1) / (p / q + 1)) +
            (1 - p) * (1 - ((1 - p) / (1 - q))⁻¹) := halg.symm
      _ ≤ p * Real.log (p / q) +
          (1 - p) * Real.log ((1 - p) / (1 - q)) := add_le_add hp_mul hpc_mul
  · have hpq' : p ≤ q := le_of_not_ge hpq
    have hratio : 1 ≤ (1 - p) / (1 - q) :=
      (le_div_iff₀ hqc).2 (by linarith)
    have hlog₁ := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hq0)
    have hlog₂ := two_mul_sub_div_add_le_log hratio
    have hp_mul : p * (1 - (p / q)⁻¹) ≤ p * Real.log (p / q) :=
      mul_le_mul_of_nonneg_left hlog₁ hp_nonneg
    have hpc_mul : (1 - p) *
        (2 * ((1 - p) / (1 - q) - 1) / ((1 - p) / (1 - q) + 1)) ≤
        (1 - p) * Real.log ((1 - p) / (1 - q)) :=
      mul_le_mul_of_nonneg_left hlog₂ (le_of_lt hpc)
    have halg : p * (1 - (p / q)⁻¹) +
        (1 - p) *
          (2 * ((1 - p) / (1 - q) - 1) / ((1 - p) / (1 - q) + 1)) =
        (p - q) ^ 2 / (2 - p - q) := by
      field_simp [ne_of_gt hp0, ne_of_gt hqc,
        ne_of_gt (by linarith : 0 < 2 - p - q)]
      ring
    calc
      (p - q) ^ 2 / 2 ≤ (p - q) ^ 2 / (2 - p - q) := by
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
          (by linarith : 0 < 2 - p - q)).2
        nlinarith [sq_nonneg (p - q)]
      _ = p * (1 - (p / q)⁻¹) +
          (1 - p) *
            (2 * ((1 - p) / (1 - q) - 1) / ((1 - p) / (1 - q) + 1)) := halg.symm
      _ ≤ p * Real.log (p / q) +
          (1 - p) * Real.log ((1 - p) / (1 - q)) := add_le_add hp_mul hpc_mul

section EventDataProcessing

variable {X : Type*} [MeasurableSpace X] {P Q : Measure X}

theorem event_klFun_lower_bound [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hi : Integrable (llr P Q) P)
    {B : Set X} (hB : MeasurableSet B) :
    Q.real B * InformationTheory.klFun (P.real B / Q.real B) ≤
      ∫ x in B, InformationTheory.klFun (P.rnDeriv Q x).toReal ∂Q := by
  let PB := P.restrict B
  let QB := Q.restrict B
  have hPB : PB = QB.withDensity (P.rnDeriv Q) := by
    dsimp [PB, QB]
    rw [← MeasureTheory.restrict_withDensity hB,
      MeasureTheory.Measure.withDensity_rnDeriv_eq P Q hPQ]
  have hPBQ : PB ≪ QB := by
    rw [hPB]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hrn : PB.rnDeriv QB =ᵐ[QB] P.rnDeriv Q := by
    rw [hPB]
    exact MeasureTheory.Measure.rnDeriv_withDensity QB
      (Measure.measurable_rnDeriv P Q)
  have hki : Integrable
      (fun x => InformationTheory.klFun (P.rnDeriv Q x).toReal) Q :=
    (InformationTheory.integrable_klFun_rnDeriv_iff hPQ).2 hi
  have hkiB : Integrable
      (fun x => InformationTheory.klFun (P.rnDeriv Q x).toReal) QB := by
    simpa [QB] using hki.integrableOn
  have hrnfun : (fun x => InformationTheory.klFun (PB.rnDeriv QB x).toReal) =ᵐ[QB]
      fun x => InformationTheory.klFun (P.rnDeriv Q x).toReal :=
    hrn.fun_comp fun z => InformationTheory.klFun z.toReal
  have hkiB' : Integrable
      (fun x => InformationTheory.klFun (PB.rnDeriv QB x).toReal) QB :=
    hkiB.congr hrnfun.symm
  have hj := MeasureTheory.mul_le_integral_rnDeriv_of_ac
    InformationTheory.convexOn_klFun
    InformationTheory.continuous_klFun.continuousWithinAt hkiB' hPBQ
  rw [integral_congr_ae hrnfun] at hj
  simpa [PB, QB, measureReal_def, hB] using hj

theorem event_gap_sq_le_two_kl [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hQP : Q ≪ P) (hi : Integrable (llr P Q) P)
    {B : Set X} (hB : MeasurableSet B) :
    (P.real B - Q.real B) ^ 2 / 2 ≤
      (InformationTheory.klDiv P Q).toReal := by
  let p := P.real B
  let q := Q.real B
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    calc
      p = (P B).toReal := rfl
      _ ≤ (P Set.univ).toReal := ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ B))
      _ = 1 := by simp
  have hq1 : q ≤ 1 := by
    calc
      q = (Q B).toReal := rfl
      _ ≤ (Q Set.univ).toReal := ENNReal.toReal_mono (measure_ne_top Q Set.univ)
        (measure_mono (Set.subset_univ B))
      _ = 1 := by simp
  have hPcomp : P.real Bᶜ = 1 - p := by
    rw [measureReal_def, measure_compl hB (measure_ne_top P B), measure_univ]
    rw [ENNReal.toReal_sub_of_le (by
      calc
        P B ≤ P Set.univ := measure_mono (Set.subset_univ B)
        _ = 1 := measure_univ)] <;>
      simp [p, measureReal_def, measure_ne_top]
  have hQcomp : Q.real Bᶜ = 1 - q := by
    rw [measureReal_def, measure_compl hB (measure_ne_top Q B), measure_univ]
    rw [ENNReal.toReal_sub_of_le (by
      calc
        Q B ≤ Q Set.univ := measure_mono (Set.subset_univ B)
        _ = 1 := measure_univ)] <;>
      simp [q, measureReal_def, measure_ne_top]
  by_cases hqz : q = 0
  · have hQB : Q B = 0 := by
      change (Q B).toReal = 0 at hqz
      rw [ENNReal.toReal_eq_zero_iff] at hqz
      exact hqz.resolve_right (measure_ne_top Q B)
    have hPB : P B = 0 := hPQ hQB
    have hpz : p = 0 := by simp [p, measureReal_def, hPB]
    simp [p, q, hpz, hqz]
  by_cases hqo : q = 1
  · have hQBc : Q Bᶜ = 0 := by
      have hz : Q.real Bᶜ = 0 := by rw [hQcomp, hqo]; norm_num
      change (Q Bᶜ).toReal = 0 at hz
      rw [ENNReal.toReal_eq_zero_iff] at hz
      exact hz.resolve_right (measure_ne_top Q Bᶜ)
    have hPBc : P Bᶜ = 0 := hPQ hQBc
    have hpo : p = 1 := by
      have hz : P.real Bᶜ = 0 := by simp [measureReal_def, hPBc]
      rw [hPcomp] at hz
      linarith
    simp [p, q, hpo, hqo]
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
  have hqlt : q < 1 := lt_of_le_of_ne hq1 hqo
  have hpz : p ≠ 0 := by
    intro hpzero
    have hPB : P B = 0 := by
      change (P B).toReal = 0 at hpzero
      rw [ENNReal.toReal_eq_zero_iff] at hpzero
      exact hpzero.resolve_right (measure_ne_top P B)
    have hQB : Q B = 0 := hQP hPB
    exact hqz (by simp [q, measureReal_def, hQB])
  have hpo : p ≠ 1 := by
    intro hpone
    have hPBc : P Bᶜ = 0 := by
      have hz : P.real Bᶜ = 0 := by rw [hPcomp, hpone]; norm_num
      change (P Bᶜ).toReal = 0 at hz
      rw [ENNReal.toReal_eq_zero_iff] at hz
      exact hz.resolve_right (measure_ne_top P Bᶜ)
    have hQBc : Q Bᶜ = 0 := hQP hPBc
    have hqone : q = 1 := by
      have hz : Q.real Bᶜ = 0 := by simp [measureReal_def, hQBc]
      rw [hQcomp] at hz
      linarith
    exact hqo hqone
  have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hplt : p < 1 := lt_of_le_of_ne hp1 hpo
  have hleft := event_klFun_lower_bound hPQ hi hB
  have hright := event_klFun_lower_bound hPQ hi hB.compl
  rw [hPcomp, hQcomp] at hright
  have hsum := add_le_add hleft hright
  have hki : Integrable
      (fun x => InformationTheory.klFun (P.rnDeriv Q x).toReal) Q :=
    (InformationTheory.integrable_klFun_rnDeriv_iff hPQ).2 hi
  calc
    (P.real B - Q.real B) ^ 2 / 2 = (p - q) ^ 2 / 2 := by rfl
    _ ≤ p * Real.log (p / q) +
        (1 - p) * Real.log ((1 - p) / (1 - q)) :=
      binaryRelativeEntropy_sq_gap hppos hplt hqpos hqlt
    _ = Q.real B * InformationTheory.klFun (P.real B / Q.real B) +
        Q.real Bᶜ * InformationTheory.klFun (P.real Bᶜ / Q.real Bᶜ) := by
      rw [hPcomp, hQcomp]
      change p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) =
        q * InformationTheory.klFun (p / q) +
          (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q))
      rw [InformationTheory.klFun_apply, InformationTheory.klFun_apply]
      field_simp [ne_of_gt hqpos, ne_of_gt (sub_pos.mpr hqlt)]
      ring
    _ ≤ (∫ x in B, InformationTheory.klFun (P.rnDeriv Q x).toReal ∂Q) +
        ∫ x in Bᶜ, InformationTheory.klFun (P.rnDeriv Q x).toReal ∂Q := by
      simpa [hPcomp, hQcomp] using hsum
    _ = (InformationTheory.klDiv P Q).toReal := by
      rw [integral_add_compl hB hki]
      exact (InformationTheory.toReal_klDiv_eq_integral_klFun hPQ).symm

theorem event_gap_le_half_of_kl_le_eighth
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hQP : Q ≪ P) (hi : Integrable (llr P Q) P)
    (hKL : (InformationTheory.klDiv P Q).toReal ≤ 1 / 8)
    {B : Set X} (hB : MeasurableSet B) :
    P.real B - Q.real B ≤ 1 / 2 := by
  have hs := event_gap_sq_le_two_kl hPQ hQP hi hB
  have hsq : (P.real B - Q.real B) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (P.real B - Q.real B + 1 / 2)]

end EventDataProcessing

/-- The elementary testing step after Pinsker: a half-unit bound on the gap of
the positive-output event implies average sign error at least one quarter. -/
theorem gaussianAverageSignError_of_positive_event_gap
    {R : ℕ} {Lbar a σ : ℝ}
    (E : GaussianTranscriptExperiment R Lbar a σ) (ha : 0 < a)
    (A : MeasurableEstimator R)
    (hgap : (E.plusMeasure {s | 0 < A.toFun s}).toReal -
      (E.minusMeasure {s | 0 < A.toFun s}).toReal ≤ 1 / 2) :
    1 / 4 ≤ gaussianAverageSignError E A := by
  let B : Set (Fin R → ℝ) := {s | 0 < A.toFun s}
  have hB : MeasurableSet B := by
    exact measurableSet_Ioi.preimage A.measurable_toFun
  have hp_le : E.plusMeasure B ≤ 1 := by
    calc
      E.plusMeasure B ≤ E.plusMeasure Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := E.plus_probability
  have hp_fin : E.plusMeasure B ≠ ⊤ :=
    (lt_of_le_of_lt hp_le (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hcomp : (E.plusMeasure Bᶜ).toReal = 1 - (E.plusMeasure B).toReal := by
    rw [measure_compl hB hp_fin, E.plus_probability]
    rw [ENNReal.toReal_sub_of_le hp_le] <;> simp [hp_fin]
  have hplus : Bᶜ = {s | A.toFun s * a ≤ 0} := by
    ext s
    simp only [B, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro hs
      have hx : A.toFun s ≤ 0 := le_of_not_gt hs
      exact mul_nonpos_of_nonpos_of_nonneg hx (le_of_lt ha)
    · intro hs hx
      exact (not_lt_of_ge hs) (mul_pos hx ha)
  have hminus : B ⊆ {s | A.toFun s * (-a) ≤ 0} := by
    intro s hs
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) (neg_nonpos.mpr (le_of_lt ha))
  have hm : (E.minusMeasure B).toReal ≤
      (E.minusMeasure {s | A.toFun s * (-a) ≤ 0}).toReal := by
    exact ENNReal.toReal_mono (by
      have hfin : E.minusMeasure {s | A.toFun s * (-a) ≤ 0} ≠ ⊤ := by
        have hle : E.minusMeasure {s | A.toFun s * (-a) ≤ 0} ≤ 1 := by
          calc
            _ ≤ E.minusMeasure Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := E.minus_probability
        exact (lt_of_le_of_lt hle (by norm_num : (1 : ENNReal) < ⊤)).ne
      exact hfin) (measure_mono hminus)
  rw [gaussianAverageSignError, ← hplus, hcomp]
  dsimp [B] at hgap ⊢
  linarith

theorem gaussianStatisticMeasure_ac
    (Lbar a₁ a₂ σ : ℝ) (hσ : 0 < σ) :
    gaussianStatisticMeasure Lbar a₁ σ ≪
      gaussianStatisticMeasure Lbar a₂ σ := by
  have hv : gaussianVariance σ ≠ 0 := ne_of_gt (by
    rw [gaussianVariance]
    exact_mod_cast sq_pos_of_pos hσ)
  unfold gaussianStatisticMeasure
  exact (gaussianReal_absolutelyContinuous (-Lbar * a₁) hv).trans
    (gaussianReal_absolutelyContinuous' (-Lbar * a₂) hv)

theorem canonicalGaussian_sign_error_of_kl_le_eighth
    (R : ℕ) (Lbar σ ε : ℝ)
    (hL : 0 < Lbar) (hσ : 0 < σ) (hε : 0 < ε)
    (hsmall : (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (gaussianA Lbar ε) σ)
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (-gaussianA Lbar ε) σ)).toReal ≤ 1 / 8) :
    ∀ A : MeasurableEstimator R,
      1 / 4 ≤ gaussianAverageSignError
        (canonicalGaussianTranscriptExact R Lbar (gaussianA Lbar ε) σ hσ) A := by
  intro A
  let a := gaussianA Lbar ε
  let P := Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar a σ
  let Q := Measure.pi fun _ : Fin R => gaussianStatisticMeasure Lbar (-a) σ
  haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar a σ) := by
    unfold gaussianStatisticMeasure
    infer_instance
  haveI : IsProbabilityMeasure (gaussianStatisticMeasure Lbar (-a) σ) := by
    unfold gaussianStatisticMeasure
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  haveI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  have hbasePQ : gaussianStatisticMeasure Lbar a σ ≪
      gaussianStatisticMeasure Lbar (-a) σ :=
    gaussianStatisticMeasure_ac Lbar a (-a) σ hσ
  have hbaseQP : gaussianStatisticMeasure Lbar (-a) σ ≪
      gaussianStatisticMeasure Lbar a σ :=
    gaussianStatisticMeasure_ac Lbar (-a) a σ hσ
  have hPQ : P ≪ Q := by
    exact absolutelyContinuous_pi_const _ _ hbasePQ R
  have hQP : Q ≪ P := by
    exact absolutelyContinuous_pi_const _ _ hbaseQP R
  have hibase : Integrable
      (llr (gaussianStatisticMeasure Lbar a σ)
        (gaussianStatisticMeasure Lbar (-a) σ))
      (gaussianStatisticMeasure Lbar a σ) := by
    unfold gaussianStatisticMeasure
    exact integrable_llr_gaussianReal_same_variance_sigma
      (-Lbar * a) (-Lbar * (-a)) σ hσ
  have hi : Integrable (llr P Q) P := by
    exact integrable_llr_pi_const _ _ hbasePQ hibase R
  have hmeas : MeasurableSet {s : Fin R → ℝ | 0 < A.toFun s} :=
    measurableSet_Ioi.preimage A.measurable_toFun
  have hgap : P.real {s | 0 < A.toFun s} - Q.real {s | 0 < A.toFun s} ≤ 1 / 2 := by
    apply event_gap_le_half_of_kl_le_eighth hPQ hQP hi
    · simpa [P, Q, a] using hsmall
    · exact hmeas
  apply gaussianAverageSignError_of_positive_event_gap
    (canonicalGaussianTranscriptExact R Lbar a σ hσ)
    (by dsimp [a, gaussianA]; positivity) A
  simpa [P, Q, a, canonicalGaussianTranscriptExact,
    canonicalGaussianTranscript] using hgap

/-- Proposition 4.6's location certificate after closing the KL side; only the
binary-testing/Pinsker estimate remains as an input. -/
noncomputable def canonicalGaussianLocationProofCertificateOfSignError
    (R : ℕ) (Lbar σ ε : ℝ)
    (hL : 0 < Lbar) (hσ : 0 < σ) (hε : 0 < ε)
    (hsign : ∀ A : MeasurableEstimator R,
      1 / 4 ≤ gaussianAverageSignError
        (canonicalGaussianTranscriptExact R Lbar (gaussianA Lbar ε) σ hσ) A) :
    GaussianLocationProofCertificate R Lbar σ ε := by
  have hKL : (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (gaussianA Lbar ε) σ)
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (-gaussianA Lbar ε) σ)).toReal =
      (R : ℝ) * (2 * Lbar * gaussianA Lbar ε) ^ 2 / (2 * σ ^ 2) := by
    rw [gaussianStatisticMeasure_pi_klDiv_two_point
      R Lbar (gaussianA Lbar ε) σ hσ]
    ring
  apply canonicalGaussianLocationProofCertificate R Lbar σ ε hL hσ hε hKL
  simpa [canonicalGaussianTranscriptExact] using hsign

theorem canonicalGaussian_kl_le_eighth
    (R : ℕ) (Lbar σ ε : ℝ)
    (hL : 0 < Lbar) (hσ : 0 < σ) (hε : 0 < ε)
    (hR : (R : ℝ) ≤ σ ^ 2 / (256 * ε ^ 2)) :
    (InformationTheory.klDiv
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (gaussianA Lbar ε) σ)
      (Measure.pi fun _ : Fin R =>
        gaussianStatisticMeasure Lbar (-gaussianA Lbar ε) σ)).toReal ≤ 1 / 8 := by
  rw [gaussianStatisticMeasure_pi_klDiv_two_point
    R Lbar (gaussianA Lbar ε) σ hσ]
  have hR' : 256 * ε ^ 2 * (R : ℝ) ≤ σ ^ 2 := by
    have := (le_div_iff₀ (by positivity : 0 < 256 * ε ^ 2)).mp hR
    nlinarith
  rw [gaussianA]
  have hL0 : Lbar ≠ 0 := ne_of_gt hL
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have heq : (R : ℝ) * ((2 * Lbar * (4 * ε / Lbar)) ^ 2 / (2 * σ ^ 2)) =
      32 * (R : ℝ) * ε ^ 2 / σ ^ 2 := by
    field_simp [hL0, hσ0]
    ring
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hσ)).2
  nlinarith

/-- The Gaussian location certificate with both the exact product KL calculation
and the binary-testing bound discharged internally. -/
noncomputable def canonicalGaussianLocationProofCertificateExact
    (R : ℕ) (Lbar σ ε : ℝ)
    (hL : 0 < Lbar) (hσ : 0 < σ) (hε : 0 < ε)
    (hR : (R : ℝ) ≤ σ ^ 2 / (256 * ε ^ 2)) :
    GaussianLocationProofCertificate R Lbar σ ε :=
  canonicalGaussianLocationProofCertificateOfSignError R Lbar σ ε hL hσ hε
    (canonicalGaussian_sign_error_of_kl_le_eighth R Lbar σ ε hL hσ hε
      (canonicalGaussian_kl_le_eighth R Lbar σ ε hL hσ hε hR))

/-- Proposition 4.6, now assembled without any KL or Pinsker hypotheses. -/
theorem canonicalProposition46 : Proposition46Statement := by
  apply proposition46_of_location_certificates (1 / 256) (by norm_num)
  intro R Lbar σ ε hL hε hσ hR
  have hR' : (R : ℝ) ≤ σ ^ 2 / (256 * ε ^ 2) := by
    convert hR using 1 <;> field_simp [ne_of_gt hε] <;> ring
  exact ⟨canonicalGaussianLocationProofCertificateExact
    R Lbar σ ε hL hσ hε hR'⟩

/-- v43 Proposition 4.6 with an explicit arbitrary internal algorithmic seed law.  The Gaussian
location certificate is unchanged; the new sum-risk averaging lemma is the only extra layer. -/
theorem canonicalProposition46Randomized :
    Proposition46RandomizedStatement.{uΩ} := by
  apply proposition46_randomized_of_location_certificates (1 / 256) (by norm_num)
  intro R Lbar σ ε hL hε hσ hR
  have hR' : (R : ℝ) ≤ σ ^ 2 / (256 * ε ^ 2) := by
    convert hR using 1 <;> field_simp [ne_of_gt hε] <;> ring
  exact ⟨canonicalGaussianLocationProofCertificateExact
    R Lbar σ ε hL hσ hε hR'⟩

/-- The legacy complete scope statement, retained verbatim for backwards compatibility. -/
theorem canonicalScopeStatement : ScopeStatement :=
  ⟨canonicalTheorem33, canonicalTheorem44, canonicalProposition46⟩

/-- v43 complete scope statement: both chain lower bounds and Proposition 4.6 with explicit
internal algorithmic randomness. -/
theorem canonicalScopeStatementV43 : ScopeStatementV43.{uΩ} :=
  ⟨canonicalTheorem33, canonicalTheorem44, canonicalProposition46Randomized⟩

end NCSCPureStochasticLB.PaperExact
