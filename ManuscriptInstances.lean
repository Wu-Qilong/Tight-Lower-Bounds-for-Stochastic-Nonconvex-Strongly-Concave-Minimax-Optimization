import ManuscriptCalibration

noncomputable section
namespace NCSCPureStochasticLB.PaperExact

/-- Pathwise progress from a single common Bernoulli seed, independent of calibration. -/
def BernoulliPairGrowth {T : ℕ} (O : StochasticOracle T Bool) : Prop :=
  ∀ x y z, pairProg (O.Gx x y z) (O.Gy x y z) ≤
    pairProg x y + if z then 1 else 0

theorem lifted_pair_growth {T : ℕ} (B : BaseOracle T) (P : LiftParameters)
    (hb : ∀ u z, prog 0 (B.g u z) ≤ prog 0 u + if z then 1 else 0) :
    BernoulliPairGrowth (liftedOracle B P) := by
  intro x y z
  have hx := liftedGx_prog_le_pairProg P x y z
  have hy := hb (P.β • y) z
  have hs := prog_zero_smul_le P.β y
  have hq := prog_zero_smul_le P.q (B.g (P.β • y) z)
  have hd := lift_dual_coupling_prog_le_pairProg P x y
  have hsub := prog_zero_sub_le_max (P.q • B.g (P.β • y) z)
    (P.ν • (y - P.γ • x))
  have hyp : prog 0 y ≤ pairProg x y := Nat.le_max_right _ _
  change max (prog 0 (liftedGx P x y z))
    (prog 0 (P.q • B.g (P.β • y) z - P.ν • (y - P.γ • x))) ≤ _
  omega

theorem response_progress_prefix {T R K : ℕ} {O : StochasticOracle T Bool}
    (hg : BernoulliPairGrowth O) (A : BernoulliRun T R K O) (w : RoundWorld R) :
    ∀ n : ℕ, n ≤ R → ∀ s : Fin R, s.1 < n → ∀ k : Fin K, ∀ r : Vec T × Vec T,
      (A.trace w).response s k = some r → pairProg r.1 r.2 ≤ roundSuccessPrefixR w n := by
  intro n
  induction n with
  | zero => intro hn s hs; omega
  | succ n ih =>
    intro hn s hs k r hrs
    have hnr : n < R := by omega
    have hprefix := roundSuccessPrefixR_succ w n hnr
    by_cases hsn : s.1 < n
    · have hprev := ih (Nat.le_of_lt hnr) s hsn k r hrs
      omega
    · have hseqval : s.1 = n := by omega
      have hseq : s = (⟨n, hnr⟩ : Fin R) := Fin.ext hseqval
      subst s
      let t : Fin R := ⟨n, hnr⟩
      have hprior : ∀ s' : Fin R, s'.1 < t.1 → ∀ k' : Fin K,
          ∀ r' : Vec T × Vec T, (A.trace w).response s' k' = some r' →
            pairProg r'.1 r'.2 ≤ roundSuccessPrefixR w n := by
        intro s' hs' k' r' hrs'
        exact ih (Nat.le_of_lt hnr) s' hs' k' r' hrs'
      cases hq : (A.trace w).query t k with
      | none =>
        have hc := A.response_consistent w t k
        rw [hq, hrs] at hc
        simp at hc
      | some q =>
        have hqprog := zeroRespecting_query_pairProg_le
          (A.trace w) (A.zero_respecting w) t (roundSuccessPrefixR w n) hprior k q hq
        have hc := A.response_consistent w t k
        rw [hq, hrs] at hc
        have hrpair : r = (O.Gx q.1 q.2 (w t), O.Gy q.1 q.2 (w t)) := Option.some.inj hc
        rw [hrpair]
        have hg' := hg q.1 q.2 (w t)
        have hp : roundSuccessPrefixR w (n + 1) =
            roundSuccessPrefixR w n + if w t then 1 else 0 := by
          simpa [t, seedSuccessIncrement] using hprefix
        simp only [Prod.fst, Prod.snd]
        omega

/-- This constructs the progress witness for arbitrary parameters from oracle support,
so the hard-event theorem no longer requires an unproved progress certificate. -/
def pairGrowthRunProgress {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (p : ℝ) (hg : BernoulliPairGrowth O) (A : BernoulliRun T R K O) :
    RunProgressWitness hT p A where
  inc := seedSuccessIncrement
  zero_one := seedSuccessIncrement_zero_one
  adapted := seedSuccessIncrement_adapted
  reveal_prob := by intro t w; rw [seedSuccessIncrement_reveal_prob]
  unfinished_implies_terminal_unrevealed := by
    intro w hsum hrev
    rcases hrev with ⟨s, k, r, hrs, hmem⟩
    have hrb := response_progress_prefix hg A w R (Nat.le_refl R) s s.2 k r hrs
    rw [roundSuccessPrefixR_total] at hrb
    have hidx := index_succ_le_pairProg_of_mem_psupp hmem
    have hlast : (lastIndexOfPos hT).1 + 1 = T := by simp [lastIndexOfPos]; omega
    rw [hlast] at hidx
    omega

def manuscriptBVBase {T : ℕ} (C : ExplicitZeroChainCertificate T) (p : ℝ) : BaseOracle T :=
  ⟨bvBaseOracle C p⟩

def manuscriptASBase {T : ℕ} (C : ExplicitZeroChainCertificate T) (p : ℝ) : BaseOracle T :=
  ⟨asBaseOracle C p⟩

theorem manuscriptBV_pair_growth {T : ℕ} (C : ExplicitZeroChainCertificate T)
    (P : LiftParameters) (p : ℝ) : BernoulliPairGrowth (liftedOracle (manuscriptBVBase C p) P) := by
  apply lifted_pair_growth
  intro u z
  cases z
  · simpa [manuscriptBVBase] using bvBaseOracle_false_prog_le_zero C p u
  · simpa [manuscriptBVBase] using bvBaseOracle_true_prog_le_succ_zero C p u

theorem manuscriptAS_pair_growth {T : ℕ} {mΓ : ℝ} (C : ExplicitZeroChainCertificate T)
    (P : LiftParameters) (p : ℝ) (Gate : SmoothGateCertificate mΓ) :
    BernoulliPairGrowth (liftedOracle (manuscriptASBase C p) P) := by
  apply lifted_pair_growth
  intro u z
  cases z
  · simpa [manuscriptASBase] using asBaseOracle_false_prog_le_zero' C Gate p u
  · simpa [manuscriptASBase] using asBaseOracle_true_prog_le_succ_zero C p u

namespace ManuscriptCalibration

def population {T : ℕ} (P : ManuscriptCalibration) (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) : PopulationObjective T :=
  populationFromLift C B P.lift (canonicalLiftPropertiesCertificate C B P.lift)

theorem smooth_budget (P : ManuscriptCalibration) (hk : 8 ≤ P.M / P.μ) :
    P.lift.ν * (1 + P.lift.γ ^ 2) + ℓ₀ * P.lift.h ≤ P.M / 2 := by
  have hmu : 8 * P.μ ≤ P.M := (le_div_iff₀ P.μ_pos).1 hk
  have hh : ℓ₀ * P.lift.h ≤ P.μ / 4 := by
    change 152 * P.h ≤ P.μ / 4
    linarith [P.ell_h_le, P.h_pos]
  have hn := mul_le_mul_of_nonneg_right P.nu_le (show 0 ≤ 1 + P.gamma ^ 2 by positivity)
  have he : (5 * P.μ / 4) * (1 + P.gamma ^ 2) = 5 * P.μ / 4 + 5 * P.M / 16 := by
    rw [P.gamma_sq]; field_simp [ne_of_gt P.μ_pos]; ring
  rw [he] at hn
  change P.lift.ν * (1 + P.gamma ^ 2) + ℓ₀ * P.lift.h ≤ _
  linarith

theorem in_class {T : ℕ} (P : ManuscriptCalibration) (C : ExplicitZeroChainCertificate T)
    (B : BaseOracle T) (Δ : ℝ) (hk : 8 ≤ P.M / P.μ)
    (hgap : P.lift.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.μ) ≤ Δ) :
    InNCSCClass (P.population C B) P.M P.μ Δ := by
  have hm : 2 * P.μ ≤ 2 * P.lift.μ := by change 2 * P.μ ≤ 2 * (P.μ + 3 * P.h); linarith [P.h_pos]
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ P.q ^ 2 * g₀ ^ 2 by positivity)
    (show 0 < 2 * P.μ by have := P.μ_pos; positivity) hm
  have hgap' : P.lift.α * Δ₀ * T + P.lift.q ^ 2 * g₀ ^ 2 / (2 * P.lift.μ) ≤ Δ := by
    change P.lift.α * Δ₀ * T + P.q ^ 2 * g₀ ^ 2 / (2 * P.lift.μ) ≤ Δ
    linarith
  have hs := populationFromLift_jointSmooth_of_bound C B P.lift
    (canonicalLiftPropertiesCertificate C B P.lift) P.M
    (P.smooth_budget hk |>.trans (by linarith [P.M_pos]))
  exact ⟨hs, P.stronglyConcave C,
    populationFromLift_initialGap_of_bound C B P.lift
      (canonicalLiftPropertiesCertificate C B P.lift) Δ hgap',
    populationFromLift_bddBelow C B P.lift (canonicalLiftPropertiesCertificate C B P.lift)⟩

theorem bv_moments {T R K : ℕ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hT : 8 ≤ T)
    (A : BernoulliRun T R K (liftedOracle (manuscriptBVBase C p) P.lift))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    5 * P.ε ≤ stationarityNormRisk p (canonicalLiftGradPhi C P.lift) A ∧
      (100 / 3 : ℝ) * P.ε ^ 2 ≤ stationarityRisk p (canonicalLiftGradPhi C P.lift) A :=
  P.hard_event_moments C (manuscriptBVBase C p) p hp hp1 hT A
    (pairGrowthRunProgress C.dim_pos p (manuscriptBV_pair_growth C P.lift p) A) hR

theorem as_moments {T R K : ℕ} {mΓ : ℝ} (P : ManuscriptCalibration)
    (C : ExplicitZeroChainCertificate T) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (Gate : SmoothGateCertificate mΓ) (hT : 8 ≤ T)
    (A : BernoulliRun T R K (liftedOracle (manuscriptASBase C p) P.lift))
    (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    5 * P.ε ≤ stationarityNormRisk p (canonicalLiftGradPhi C P.lift) A ∧
      (100 / 3 : ℝ) * P.ε ^ 2 ≤ stationarityRisk p (canonicalLiftGradPhi C P.lift) A :=
  P.hard_event_moments C (manuscriptASBase C p) p hp hp1 hT A
    (pairGrowthRunProgress C.dim_pos p (manuscriptAS_pair_growth C P.lift p Gate) A) hR

end ManuscriptCalibration
end NCSCPureStochasticLB.PaperExact
