import ManuscriptAS

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- Full manuscript (26), including the noise-free branch. -/
def manuscriptASRate (M Δ ε κ σ : ℝ) : ℝ :=
  (M * Δ / ε ^ 2) * max 1 (min (κ * σ ^ 2 / ε ^ 2) (κ * Real.sqrt κ * σ / ε))

theorem manuscriptASRate_noise_free (M Δ ε κ : ℝ) :
    manuscriptASRate M Δ ε κ 0 = M * Δ / ε ^ 2 := by simp [manuscriptASRate]

theorem manuscriptASRate_le_bvRate (M Δ ε κ σ : ℝ) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) :
    manuscriptASRate M Δ ε κ σ ≤ bvRate M Δ ε κ σ := by
  exact mul_le_mul_of_nonneg_left (max_le_max_left 1 (min_le_left _ _))
    (div_nonneg (mul_nonneg hM hΔ) (sq_nonneg ε))

namespace ManuscriptASProblem

theorem chain_rate_threshold (P : ManuscriptASProblem) :
    (1 / (32768 * 12 * max 155 manuscriptS)) *
      asChainRate P.M P.Δ P.ε (P.M / P.μ) P.p ≤ (P.T : ℝ) / (4 * P.p) := by
  have hbase : 0 ≤ P.M * P.Δ / P.ε ^ 2 := by have := P.M_pos; have := P.Δ_pos; positivity
  have hmax : 0 < max 155 manuscriptS := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc : 0 ≤ (1 : ℝ) / (32768 * 12 * max 155 manuscriptS) := by positivity
  have hp := P.p_pos
  have hroot := Real.sqrt_pos.2 hp
  have hr2 := Real.sq_sqrt (le_of_lt hp)
  have hmul : (1 / (32768 * 12 * max 155 manuscriptS)) *
      asChainRate P.M P.Δ P.ε (P.M / P.μ) P.p ≤ P.scale / (8 * P.p) := by
    by_cases hh : P.μ / (4 * 155) ≤ P.M * Real.sqrt P.p / (4 * manuscriptS)
    · have hid : P.scale / (8 * P.p) =
          (1 / (32768 * 12 * 155)) * (P.M * P.Δ / P.ε ^ 2) * (1 / P.p) := by
        unfold scale
        rw [P.calibration.q_sq]
        change (P.Δ * min (P.μ / (4 * 155)) (P.M * Real.sqrt P.p / (4 * manuscriptS)) /
          (4 * Δ₀ * (256 * P.ε ^ 2 / (P.M / P.μ)))) / (8 * P.p) = _
        rw [min_eq_left hh]
        field_simp [Δ₀, ne_of_gt P.M_pos, ne_of_gt P.μ_pos, ne_of_gt P.ε_pos, ne_of_gt hp]
        <;> ring_nf
        <;> field_simp [ne_of_gt P.μ_pos, ne_of_gt P.ε_pos, ne_of_gt hp]
        <;> ring
      rw [hid]
      have hconst : (1 : ℝ) / (32768 * 12 * max 155 manuscriptS) ≤ 1 / (32768 * 12 * 155) := by
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith [le_max_left (155 : ℝ) manuscriptS]
      calc
        _ ≤ (1 / (32768 * 12 * max 155 manuscriptS)) * (P.M * P.Δ / P.ε ^ 2) * (1 / P.p) := by
          unfold asChainRate
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left
            (min_le_left (1 / P.p) ((P.M / P.μ) / Real.sqrt P.p)) (mul_nonneg hc hbase)
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hbase) (by positivity)
    · have hid : P.scale / (8 * P.p) =
          (1 / (32768 * 12 * manuscriptS)) * (P.M * P.Δ / P.ε ^ 2) * ((P.M / P.μ) / Real.sqrt P.p) := by
        unfold scale
        rw [P.calibration.q_sq]
        change (P.Δ * min (P.μ / (4 * 155)) (P.M * Real.sqrt P.p / (4 * manuscriptS)) /
          (4 * Δ₀ * (256 * P.ε ^ 2 / (P.M / P.μ)))) / (8 * P.p) = _
        rw [min_eq_right (le_of_not_ge hh)]
        field_simp [Δ₀, ne_of_gt P.M_pos, ne_of_gt P.μ_pos, ne_of_gt P.ε_pos,
          ne_of_gt hp, ne_of_gt hroot, ne_of_gt manuscriptS_pos]
        ring_nf
        field_simp [ne_of_gt P.μ_pos, ne_of_gt P.ε_pos, ne_of_gt hp, ne_of_gt manuscriptS_pos]
        ring_nf
      rw [hid]
      have hconst : (1 : ℝ) / (32768 * 12 * max 155 manuscriptS) ≤ 1 / (32768 * 12 * manuscriptS) := by
        apply one_div_le_one_div_of_le (mul_pos (by norm_num) manuscriptS_pos)
        nlinarith [le_max_right (155 : ℝ) manuscriptS]
      calc
        _ ≤ (1 / (32768 * 12 * max 155 manuscriptS)) * (P.M * P.Δ / P.ε ^ 2) * ((P.M / P.μ) / Real.sqrt P.p) := by
          unfold asChainRate
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left
            (min_le_right (1 / P.p) ((P.M / P.μ) / Real.sqrt P.p)) (mul_nonneg hc hbase)
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hbase)
          (le_of_lt (div_pos (div_pos P.M_pos P.μ_pos) hroot))
  calc
    _ ≤ P.scale / (8 * P.p) := hmul
    _ = (P.scale / 2) / (4 * P.p) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right P.scale_half_le_T (by positivity)

theorem mixed_factor_lower (P : ManuscriptASProblem) :
    (1 / (256 * g₀ ^ 2)) * max 1 (min ((P.M / P.μ) * P.σ ^ 2 / P.ε ^ 2)
      ((P.M / P.μ) * Real.sqrt (P.M / P.μ) * P.σ / P.ε)) ≤
      min (1 / P.p) ((P.M / P.μ) / Real.sqrt P.p) := by
  let k := P.M / P.μ
  let a := k * P.σ ^ 2 / P.ε ^ 2
  let t := Real.sqrt k * P.σ / P.ε
  have hk : 0 < k := div_pos P.M_pos P.μ_pos
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) P.σ_nonneg) (le_of_lt P.ε_pos)
  have ht2 : t ^ 2 = a := by dsimp [t, a]; rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hk)]
  have hc : 0 ≤ (1 : ℝ) / (256 * g₀ ^ 2) := by norm_num [g₀]
  have hi := P.toManuscriptBVProblem.inverse_probability_factor
  change (1 / (256 * g₀ ^ 2)) * max 1 a ≤ 1 / P.p at hi
  have hp := P.p_pos
  have hs := Real.sqrt_pos.2 hp
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  have hap : a * P.p ≤ 256 * g₀ ^ 2 := by
    have hh := (le_div_iff₀ hp).1 hi
    have hm := mul_le_mul_of_nonneg_right (le_max_right 1 a) (le_of_lt hp)
    norm_num [g₀] at *
    nlinarith only [hh, hm]
  have hroot : t * Real.sqrt P.p ≤ 16 * g₀ := by
    have he : (t * Real.sqrt P.p) ^ 2 = a * P.p := by rw [mul_pow, ht2, hs2]
    have hn := mul_nonneg ht (le_of_lt hs)
    norm_num [g₀] at *
    nlinarith only [he, hap, hn]
  have hlinear : (1 / (256 * g₀ ^ 2)) * t ≤ 1 / Real.sqrt P.p := by
    apply (le_div_iff₀ hs).2
    norm_num [g₀] at *
    nlinarith only [hroot]
  have hrootle : Real.sqrt P.p ≤ 1 := by
    have := P.p_le_one
    nlinarith [Real.sqrt_nonneg P.p]
  have hone : (1 : ℝ) ≤ k / Real.sqrt P.p := by
    apply (le_div_iff₀ hs).2
    have : 8 ≤ k := P.kappa_ge
    linarith
  have hc1 : (1 : ℝ) / (256 * g₀ ^ 2) ≤ 1 := by norm_num [g₀]
  have hform : (P.M / P.μ) * Real.sqrt (P.M / P.μ) * P.σ / P.ε = k * t := by dsimp [k, t]; ring
  rw [hform]
  change (1 / (256 * g₀ ^ 2)) * max 1 (min a (k * t)) ≤ min (1 / P.p) (k / Real.sqrt P.p)
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (max_le_max_left 1 (min_le_left a (k * t))) hc).trans hi
  · rw [mul_max_of_nonneg _ _ hc]
    apply max_le
    · simpa using hc1.trans hone
    · calc
        _ ≤ (1 / (256 * g₀ ^ 2)) * (k * t) := mul_le_mul_of_nonneg_left (min_le_right a (k * t)) hc
        _ = k * ((1 / (256 * g₀ ^ 2)) * t) := by ring
        _ ≤ k * (1 / Real.sqrt P.p) := mul_le_mul_of_nonneg_left hlinear (le_of_lt hk)
        _ = _ := by ring

theorem rate_threshold (P : ManuscriptASProblem) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ ≤
      (P.T : ℝ) / (4 * P.p) := by
  have hmax : 0 < max 155 manuscriptS := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_left P.mixed_factor_lower
    (show 0 ≤ (1 / (32768 * 12 * max 155 manuscriptS)) * (P.M * P.Δ / P.ε ^ 2) by
      have := P.M_pos; have := P.Δ_pos; positivity)
  have he : manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ =
      (1 / (32768 * 12 * max 155 manuscriptS)) * (P.M * P.Δ / P.ε ^ 2) *
      ((1 / (256 * g₀ ^ 2)) * max 1 (min ((P.M / P.μ) * P.σ ^ 2 / P.ε ^ 2)
        ((P.M / P.μ) * Real.sqrt (P.M / P.μ) * P.σ / P.ε))) := by
    unfold manuscriptASRateConstant manuscriptASRate; ring
  rw [he]
  exact hm.trans (by simpa [asChainRate, mul_assoc] using P.chain_rate_threshold)

universe u

theorem randomized_moments (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hR : (R : ℝ) ≤ (P.T : ℝ) / (4 * P.p)) :
    ENNReal.ofReal (5 * P.ε) ≤ internalRandomNormRisk ρ P.p P.population.gradPhi A ∧
      ENNReal.ofReal ((100 / 3 : ℝ) * P.ε ^ 2) ≤
        internalRandomStationarityRisk ρ P.p P.population.gradPhi A :=
  ⟨internalRandomNormRisk_lower ρ P.p _ A _ (fun ω => (P.moments (A ω) hR).1),
    internalRandomStationarityRisk_lower ρ P.p _ A _ (fun ω => (P.moments (A ω) hR).2)⟩

theorem randomized_round_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) :
    (P.T : ℝ) / (4 * P.p) < (R : ℝ) := by
  by_contra hn
  have hm := P.randomized_moments ρ A (le_of_not_gt hn)
  rcases hsuccess with h | h
  · have hs : ENNReal.ofReal P.ε < ENNReal.ofReal (5 * P.ε) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith [P.ε_pos])).2 (by linarith [P.ε_pos])
    exact (not_lt_of_ge (hm.1.trans h)) hs
  · have hs : ENNReal.ofReal (P.ε ^ 2) < ENNReal.ofReal ((100 / 3 : ℝ) * P.ε ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) (sq_pos_of_pos P.ε_pos))).2
        (by nlinarith [sq_pos_of_pos P.ε_pos])
    exact (not_lt_of_ge (hm.2.trans h)) hs

theorem randomized_rate_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) :
    manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ < (R : ℝ) :=
  P.rate_threshold.trans_lt (P.randomized_round_lower ρ A hsuccess)

theorem randomized_gradient_lower (P : ManuscriptASProblem) {Ω : Type u} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {R K : ℕ}
    (A : Ω → BernoulliRun P.T R K P.oracle)
    (hsuccess : internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
      internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2))
    (hbatch : ∀ ω w, ValidBatchSizes ((A ω).trace w)) :
    ∀ ω w, manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
      (returnedGradientCount ((A ω).trace w) : ℝ) := by
  intro ω w
  have hc := (gradientCountAccounting P.T R K ((A ω).trace w) (hbatch ω w)).1
  have hcast : (R : ℝ) ≤ (returnedGradientCount ((A ω).trace w) : ℝ) := by exact_mod_cast hc
  exact (P.randomized_rate_lower ρ A hsuccess).trans_le hcast

/-- Theorem 5.1's fixed-instance construction and full rate in the bounded-round trace model.
Neither the instance nor the constants depend on the simultaneous-query bound K. -/
theorem fixed_instance_lower_bound (P : ManuscriptASProblem)
    {Ω : Type u} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
    InNCSCClass P.population P.M P.μ P.Δ ∧
    OracleUnbiased P.population (bernoulliLaw P.p) P.oracle ∧
    OracleBoundedVariance P.population (bernoulliLaw P.p) P.oracle P.σ ∧
    OracleAveragedSmooth (bernoulliLaw P.p) P.oracle P.M ∧
    ∀ (R K : ℕ) (A : Ω → BernoulliRun P.T R K P.oracle),
      (internalRandomNormRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal P.ε ∨
       internalRandomStationarityRisk ρ P.p P.population.gradPhi A ≤ ENNReal.ofReal (P.ε ^ 2)) →
      (∀ ω w, ValidBatchSizes ((A ω).trace w)) →
      ∀ ω w, manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ <
        (returnedGradientCount ((A ω).trace w) : ℝ) :=
  ⟨P.in_class, P.unbiased, P.variance, P.averaged_smooth,
    fun _ _ A hs hb => P.randomized_gradient_lower ρ A hs hb⟩

end ManuscriptASProblem
end NCSCPureStochasticLB.PaperExact
