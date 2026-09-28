import NCSCPureStochasticLB

noncomputable section
namespace NCSCPureStochasticLB.PaperExact

/-- Sum out one coordinate of a finite independent Bernoulli tape. -/
theorem roundExpect_split (p : ℝ) {R : ℕ} (t : Fin R) (f : RoundWorld R → ℝ) :
    roundExpect p f =
      ∑ v : ({s : Fin R // s ≠ t} → Bool),
        (∏ s, bernoulliMass p (v s)) *
          (p * f ((Equiv.funSplitAt t Bool).symm (true, v)) +
          (1 - p) * f ((Equiv.funSplitAt t Bool).symm (false, v))) := by
  classical
  let e := Equiv.funSplitAt t Bool
  have hw (b : Bool) (v : ({s : Fin R // s ≠ t} → Bool)) :
      roundWeight p (e.symm (b, v)) = bernoulliMass p b * ∏ s, bernoulliMass p (v s) := by
    unfold roundWeight
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)]
    have hv : (∏ s ∈ Finset.univ.erase t, bernoulliMass p (e.symm (b, v) s)) =
        ∏ s : {s : Fin R // s ≠ t}, bernoulliMass p (v s) := by
      rw [Finset.prod_subtype (p := fun s : Fin R => s ≠ t) (Finset.univ.erase t) (by simp)]
      apply Finset.prod_congr rfl
      intro s _
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, s.property]
    change bernoulliMass p (e.symm (b, v) t) *
      (∏ s ∈ Finset.univ.erase t, bernoulliMass p (e.symm (b, v) s)) = _
    rw [hv]
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  unfold roundExpect
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [hw]
  simp [bernoulliMass]
  ring

/-- The conditional reveal bound implies an unconditional expected increment bound,
for every p in [0,1], without the old p<1/2 split. -/
theorem roundExpect_increment_le {R : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (inc : Fin R → RoundWorld R → ℕ)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p) (t : Fin R) :
    roundExpect p (fun w => (inc t w : ℝ)) ≤ p := by
  classical
  let e := Equiv.funSplitAt t Bool
  have hcast (w : RoundWorld R) : (inc t w : ℝ) = if inc t w = 1 then 1 else 0 := by
    rcases h01 t w with h | h <;> simp [h]
  have hs (v : ({s : Fin R // s ≠ t} → Bool)) (b : Bool) :
      setRoundSeed (e.symm (false, v)) t b = e.symm (b, v) := by
    funext s
    by_cases h : s = t
    · subst s; simp [setRoundSeed, e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [setRoundSeed, e, Equiv.funSplitAt, Equiv.piSplitAt, h]
  rw [roundExpect_split p t]
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    mul_le_mul_of_nonneg_left (hreveal t (e.symm (false, v)))
      (show 0 ≤ ∏ s, bernoulliMass p (v s) from
        Finset.prod_nonneg (fun s _ => by cases v s <;> simp [bernoulliMass, hp0, sub_nonneg.mpr hp1])))
  simp only [oneRoundRevealProb, hs, ← hcast] at hbound
  have hmass : (∑ v : ({s : Fin R // s ≠ t} → Bool), ∏ s, bernoulliMass p (v s)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [bernoulliMass]
  simpa only [← Finset.sum_mul, hmass, one_mul] using hbound

/-- Total expected progress is at most Rp. -/
theorem roundExpect_total_progress_le {R : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (inc : Fin R → RoundWorld R → ℕ)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p) :
    roundExpect p (fun w => ∑ t, (inc t w : ℝ)) ≤ (R : ℝ) * p := by
  classical
  have he : roundExpect p (fun w => ∑ t, (inc t w : ℝ)) =
      ∑ t, roundExpect p (fun w => (inc t w : ℝ)) := by
    unfold roundExpect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  calc
    _ ≤ ∑ _t : Fin R, p := Finset.sum_le_sum (fun t _ =>
      roundExpect_increment_le p hp0 hp1 inc h01 hreveal t)
    _ = _ := by simp

/-- The exact finite-product progress inequality underlying Lemma 3.5.
No restriction on R and no small-p hypothesis is imposed. -/
theorem progress_probability_exact (R T : ℕ) (p : ℝ)
    (inc : Fin R → RoundWorld R → ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p) (hT : 0 < T) :
    1 - p * R / T ≤ roundProb p {w | (∑ t : Fin R, inc t w) < T} := by
  classical
  let Bad : Set (RoundWorld R) := {w | T ≤ ∑ t, inc t w}
  have hpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hpoint (w : RoundWorld R) :
      (T : ℝ) * (if w ∈ Bad then 1 else 0) ≤ ∑ t : Fin R, (inc t w : ℝ) := by
    by_cases hb : w ∈ Bad
    · have hc : (T : ℝ) ≤ ∑ t : Fin R, (inc t w : ℝ) := by exact_mod_cast hb
      simpa [hb] using hc
    · simp only [hb, ↓reduceIte, mul_zero]
      positivity
  have hm : (T : ℝ) * roundProb p Bad ≤
      roundExpect p (fun w => ∑ t : Fin R, (inc t w : ℝ)) := by
    unfold roundProb roundExpect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    have h := mul_le_mul_of_nonneg_left (hpoint w) (roundWeight_nonneg p hp0 hp1 w)
    by_cases hw : w ∈ Bad <;> simpa [hw, mul_assoc, mul_left_comm, mul_comm] using h
  have hb : roundProb p Bad ≤ p * R / T := by
    apply (le_div_iff₀ hpos).mpr
    have he := roundExpect_total_progress_le p hp0 hp1 inc h01 hreveal
    nlinarith
  have hc : {w : RoundWorld R | (∑ t : Fin R, inc t w) < T} = Badᶜ := by
    ext w; simp [Bad, not_le]
  rw [hc, roundProb_compl]
  linarith

/-- Lemma 3.5's exact terminal-coordinate conclusion for any existing run witness.
This is the concrete Bernoulli interface, not a claim about arbitrary seed spaces. -/
theorem lemma35_bernoulli_paper {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : BernoulliRun T R K O) (W : RunProgressWitness hT p A) :
    1 - p * R / T ≤ roundProb p (terminalUnrevealedEvent hT A) := by
  exact (progress_probability_exact R T p W.inc hp0 hp1 W.zero_one W.reveal_prob hT).trans
    (roundProb_mono p hp0 hp1 W.unfinished_implies_terminal_unrevealed)

/-- Lemma 3.5's support conclusion, with one-based coordinates in [1,T-1]. -/
theorem lemma35_bernoulli_support_paper {T R K : ℕ} {O : StochasticOracle T Bool}
    (hT : 0 < T) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : BernoulliRun T R K O) (W : RunProgressWitness hT p A) :
    1 - p * R / T ≤ roundProb p {w | ∀ i ∈ supp (A.trace w).output, i.1 + 1 ≤ T - 1} := by
  apply (lemma35_bernoulli_paper hT p hp0 hp1 A W).trans
  apply roundProb_mono p hp0 hp1
  intro w hw i hi
  have hz := output_terminal_zero_of_unrevealed hT A w hw
  have hne : i ≠ lastIndexOfPos hT := by
    intro he
    subst i
    simp [supp, hz] at hi
  have hiv : i.1 ≠ T - 1 := by
    intro h
    apply hne
    apply Fin.ext
    simpa [lastIndexOfPos] using h
  have := i.2
  omega

/-- The 3/4 consequence now follows from the exact probability inequality. -/
theorem progress_three_quarters_from_exact (R T : ℕ) (p : ℝ)
    (inc : Fin R → RoundWorld R → ℕ) (hp : 0 < p) (hp1 : p ≤ 1)
    (h01 : ∀ t w, inc t w = 0 ∨ inc t w = 1)
    (hreveal : ∀ t w, oneRoundRevealProb p inc t w ≤ p)
    (hT : 0 < T) (hR : (R : ℝ) ≤ (T : ℝ) / (4 * p)) :
    (3 / 4 : ℝ) ≤ roundProb p {w | (∑ t : Fin R, inc t w) < T} := by
  have h := progress_probability_exact R T p inc hp.le hp1 h01 hreveal hT
  have hpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hr := (le_div_iff₀ (show 0 < 4 * p by positivity)).mp hR
  have hb : p * R / T ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  linarith

end NCSCPureStochasticLB.PaperExact
