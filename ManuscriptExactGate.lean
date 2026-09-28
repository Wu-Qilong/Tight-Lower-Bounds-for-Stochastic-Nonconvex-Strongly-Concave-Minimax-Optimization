import PaperAlignment

/-! The manuscript's literal derivative-supremum gate constant, not merely an upper bound. -/
noncomputable section
namespace NCSCPureStochasticLB.PaperExact

theorem gammaGate_hasDerivAt (t : ℝ) :
    HasDerivAt GammaGate (LambdaGate t / gateDenom) t := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (lambdaGate_intervalIntegrable (1 / 4) t)
    lambdaGate_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    lambdaGate_continuous.continuousAt
  exact h.div_const gateDenom

theorem gammaGate_deriv (t : ℝ) : deriv GammaGate t = LambdaGate t / gateDenom :=
  (gammaGate_hasDerivAt t).deriv

theorem lambdaGate_le_peak (t : ℝ) : LambdaGate t ≤ Real.exp (-(16 / 25 : ℝ)) := by
  by_cases ht : (1 / 4 : ℝ) < t ∧ t < 1 / 2
  · have hd : 0 < 100 * (t - 1 / 4) * (1 / 2 - t) := by
      rcases ht with ⟨h1, h2⟩
      exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr h1)) (sub_pos.mpr h2)
    have hb : 100 * (t - 1 / 4) * (1 / 2 - t) ≤ 25 / 16 := by
      nlinarith [sq_nonneg (t - 3 / 8)]
    have hi : (16 / 25 : ℝ) ≤ 1 / (100 * (t - 1 / 4) * (1 / 2 - t)) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith
    simp only [LambdaGate, if_pos ht]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  · simp only [LambdaGate, if_neg ht]
    exact (Real.exp_pos _).le

theorem lambdaGate_peak : LambdaGate (3 / 8) = Real.exp (-(16 / 25 : ℝ)) := by
  norm_num [LambdaGate]

/-- Exactly `sup_t |Γ'(t)|` in Appendix B.3; the supremum is attained at `3/8`. -/
def paperMGamma : ℝ := sSup (Set.range (fun t : ℝ => |deriv GammaGate t|))

theorem paperMGamma_eq : paperMGamma = Real.exp (-(16 / 25 : ℝ)) / gateDenom := by
  have hb : ∀ t : ℝ, |deriv GammaGate t| ≤ Real.exp (-(16 / 25 : ℝ)) / gateDenom := by
    intro t
    rw [gammaGate_deriv, abs_of_nonneg (div_nonneg (lambdaGate_nonneg _) gateDenom_pos.le)]
    exact div_le_div_of_nonneg_right (lambdaGate_le_peak t) gateDenom_pos.le
  have ha : |deriv GammaGate (3 / 8)| = Real.exp (-(16 / 25 : ℝ)) / gateDenom := by
    rw [gammaGate_deriv, lambdaGate_peak, abs_of_pos (div_pos (Real.exp_pos _) gateDenom_pos)]
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact hb t)
  · rw [← ha]
    exact le_csSup ⟨_, by rintro _ ⟨t, rfl⟩; exact hb t⟩ ⟨3 / 8, rfl⟩

theorem paperMGamma_pos : 0 < paperMGamma := by
  rw [paperMGamma_eq]
  exact div_pos (Real.exp_pos _) gateDenom_pos

theorem paperMGamma_le_explicit : paperMGamma ≤ explicitMGamma := by
  rw [paperMGamma_eq, explicitMGamma, ← one_div]
  exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by norm_num)) gateDenom_pos.le

theorem gammaGate_lipschitz_paper (s t : ℝ) :
    |GammaGate s - GammaGate t| ≤ paperMGamma * |s - t| := by
  rw [gammaGate_sub_eq, abs_div, abs_of_pos gateDenom_pos, paperMGamma_eq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := LambdaGate) (C := Real.exp (-(16 / 25 : ℝ))) (a := t) (b := s) (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lambdaGate_nonneg x)]
      exact lambdaGate_le_peak x)
  rw [Real.norm_eq_abs] at hb
  calc
    _ ≤ (Real.exp (-(16 / 25 : ℝ)) * |s - t|) / gateDenom :=
      div_le_div_of_nonneg_right (by simpa [mul_comm] using hb) gateDenom_pos.le
    _ = _ := by ring

def paperSmoothGateCertificate : SmoothGateCertificate paperMGamma where
  mΓ_nonneg := paperMGamma_pos.le
  gamma_zero := fun _ ht => gammaGate_zero_of_le_quarter ht
  gamma_one := fun _ ht => gammaGate_one_of_half_le ht
  gamma_range := gammaGate_range_all
  gamma_lipschitz := gammaGate_lipschitz_paper
  theta_sandwich := fun u i => ⟨thetaGate_lower_explicit u i, thetaGate_upper_explicit u i⟩

end NCSCPureStochasticLB.PaperExact
