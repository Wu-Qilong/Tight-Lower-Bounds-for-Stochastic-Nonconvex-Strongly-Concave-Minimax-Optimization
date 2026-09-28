import ManuscriptOnlineRisk

noncomputable section
namespace NCSCPureStochasticLB.PaperExact

def batchJointSupport {T K : ℕ} (r : OnlineBatch T K) : Set (Fin T ⊕ Fin T) :=
  {c | ∃ k z, r k = some z ∧ c ∈ jointSupport z}

def prependOnlineTrace {T H K : ℕ} (q r : OnlineBatch T K) (tr : InteractionTrace T H K) :
    InteractionTrace T (H + 1) K :=
  ⟨Fin.cases q tr.query, Fin.cases r tr.response, tr.output⟩

theorem prepend_revealed_zero {T H K : ℕ} (q r : OnlineBatch T K) (tr : InteractionTrace T H K) :
    jointRevealedBefore (prependOnlineTrace q r tr) 0 = ∅ := by
  ext c
  simp [jointRevealedBefore]

theorem prepend_revealed_succ {T H K : ℕ} (q r : OnlineBatch T K) (tr : InteractionTrace T H K)
    (t : Fin H) : jointRevealedBefore (prependOnlineTrace q r tr) t.succ =
      batchJointSupport r ∪ jointRevealedBefore tr t := by
  ext c
  simp [jointRevealedBefore, prependOnlineTrace, batchJointSupport, Fin.exists_fin_succ]

theorem prepend_revealed_all {T H K : ℕ} (q r : OnlineBatch T K) (tr : InteractionTrace T H K) :
    jointRevealedAll (prependOnlineTrace q r tr) = batchJointSupport r ∪ jointRevealedAll tr := by
  ext c
  simp [jointRevealedAll, prependOnlineTrace, batchJointSupport, Fin.exists_fin_succ]

theorem prepend_call_count {T H K : ℕ} (q r : OnlineBatch T K) (tr : InteractionTrace T H K) :
    returnedGradientCount (prependOnlineTrace q r tr) = onlineBatchSize q + returnedGradientCount tr := by
  unfold returnedGradientCount
  rw [Fin.sum_univ_succ]
  rfl

/-- Support relative to coordinates already revealed before this subtree is entered. -/
def RelativeSupported {T H K : ℕ} (S : Set (Fin T ⊕ Fin T)) (tr : InteractionTrace T H K) : Prop :=
  (∀ t k q, tr.query t k = some q → jointSupport q ⊆ S ∪ jointRevealedBefore tr t) ∧
    jointSupport (tr.output, 0) ⊆ S ∪ jointRevealedAll tr

def BatchSupported {T K : ℕ} (S : Set (Fin T ⊕ Fin T)) (q : OnlineBatch T K) : Prop :=
  ∀ k z, q k = some z → jointSupport z ⊆ S

theorem relative_supported_empty {T H K : ℕ} (tr : InteractionTrace T H K) :
    RelativeSupported ∅ tr ↔ StandardZeroRespectingTrace tr := by
  simp [RelativeSupported, StandardZeroRespectingTrace]

theorem relative_supported_prepend {T H K : ℕ} (S : Set (Fin T ⊕ Fin T))
    (q r : OnlineBatch T K) (tr : InteractionTrace T H K) :
    RelativeSupported S (prependOnlineTrace q r tr) ↔
      BatchSupported S q ∧ RelativeSupported (S ∪ batchJointSupport r) tr := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro k z hz
      have hh := h.1 0 k z hz
      simpa [prepend_revealed_zero] using hh
    · intro t k z hz
      have hh := h.1 t.succ k z hz
      simpa only [prepend_revealed_succ, Set.union_assoc] using hh
    · have hh := h.2
      rw [prepend_revealed_all] at hh
      simpa only [Set.union_assoc] using hh
  · rintro ⟨hq, ht⟩
    constructor
    · intro t
      refine Fin.cases ?_ (fun t => ?_) t
      · intro k z hz
        simpa only [prepend_revealed_zero, Set.union_empty] using hq k z hz
      · intro k z hz
        simpa only [prepend_revealed_succ, Set.union_assoc] using ht.1 t k z hz
    · change jointSupport (tr.output, 0) ⊆ S ∪ jointRevealedAll (prependOnlineTrace q r tr)
      rw [prepend_revealed_all, ← Set.union_assoc]
      exact ht.2

namespace OnlinePolicy

variable {T H K : ℕ}

theorem relative_halt_iff (O : StochasticOracle T Bool) (S : Set (Fin T ⊕ Fin T)) (x : Vec T)
    (w : RoundWorld H) : RelativeSupported S ((halt (K := K) x).execute O w) ↔
      jointSupport (x, 0) ⊆ S := by
  simp [RelativeSupported, execute, jointRevealedAll]

theorem relative_halt_zero (O : StochasticOracle T Bool) (S : Set (Fin T ⊕ Fin T))
    (w : RoundWorld H) : RelativeSupported S ((halt (K := K) 0).execute O w) := by
  rw [relative_halt_iff]
  intro c hc
  cases c <;> simp [jointSupport] at hc

/-- A causal support/budget guard. It uses only the already revealed coordinates and
remaining call budget, not the oracle, its law, or any hidden seed. -/
def repair (S : Set (Fin T ⊕ Fin T)) (B : ℕ) : {H : ℕ} → OnlinePolicy T K H → OnlinePolicy T K H
  | _, .halt x => by
    classical
    exact if jointSupport (x, 0) ⊆ S then .halt x else .halt 0
  | _, .ask q next => by
    classical
    exact if BatchSupported S q.points ∧ onlineBatchSize q.points ≤ B then
      .ask q (fun r => repair (S ∪ batchJointSupport r) (B - onlineBatchSize q.points) (next r))
    else .halt 0

theorem repair_legal_relative (O : StochasticOracle T Bool) (P : OnlinePolicy T K H) :
    ∀ S B w, RelativeSupported S ((P.repair S B).execute O w) ∧
      returnedGradientCount ((P.repair S B).execute O w) ≤ B := by
  classical
  induction P with
  | halt x =>
    intro S B w
    by_cases hx : jointSupport (x, 0) ⊆ S
    · simp only [repair, if_pos hx]
      exact ⟨(relative_halt_iff O S x w).mpr hx, by simp [execute, returnedGradientCount, batchSize]⟩
    · simp only [repair, if_neg hx]
      exact ⟨relative_halt_zero O S w, by simp [execute, returnedGradientCount, batchSize]⟩
  | ask q next ih =>
    intro S B w
    by_cases hq : BatchSupported S q.points ∧ onlineBatchSize q.points ≤ B
    · simp only [repair, if_pos hq]
      change RelativeSupported S (prependOnlineTrace q.points (answer O q.points (w 0)) _) ∧
        returnedGradientCount (prependOnlineTrace q.points (answer O q.points (w 0)) _) ≤ B
      have ht := ih (answer O q.points (w 0)) (S ∪ batchJointSupport (answer O q.points (w 0)))
        (B - onlineBatchSize q.points) (fun t => w t.succ)
      refine ⟨(relative_supported_prepend _ _ _ _).mpr ⟨hq.1, ht.1⟩, ?_⟩
      rw [prepend_call_count]
      exact (Nat.add_le_add_left ht.2 _).trans_eq (Nat.add_sub_of_le hq.2)
    · simp only [repair, if_neg hq]
      exact ⟨relative_halt_zero O S w, by simp [execute, returnedGradientCount, batchSize]⟩

/-- On a legal execution the guard preserves the entire trace, not just its risk. -/
theorem repair_preserves_legal_trace (O : StochasticOracle T Bool) (P : OnlinePolicy T K H) :
    ∀ S B w, RelativeSupported S (P.execute O w) → returnedGradientCount (P.execute O w) ≤ B →
      (P.repair S B).execute O w = P.execute O w := by
  classical
  induction P with
  | halt x =>
    intro S B w hs hb
    have hx := (relative_halt_iff O S x w).mp hs
    simp [repair, hx]
  | ask q next ih =>
    intro S B w hs hb
    change RelativeSupported S (prependOnlineTrace q.points (answer O q.points (w 0)) _) at hs
    have ht := (relative_supported_prepend _ _ _ _).mp hs
    change returnedGradientCount (prependOnlineTrace q.points (answer O q.points (w 0)) _) ≤ B at hb
    rw [prepend_call_count] at hb
    have hq : BatchSupported S q.points ∧ onlineBatchSize q.points ≤ B := ⟨ht.1, by omega⟩
    have hb' : returnedGradientCount ((next (answer O q.points (w 0))).execute O (fun t => w t.succ)) ≤
        B - onlineBatchSize q.points := by omega
    have he := ih (answer O q.points (w 0)) (S ∪ batchJointSupport (answer O q.points (w 0)))
      (B - onlineBatchSize q.points) (fun t => w t.succ) ht.2 hb'
    simp only [repair, if_pos hq, execute]
    rw [he]

theorem repair_call_count_le (O : StochasticOracle T Bool) (P : OnlinePolicy T K H) :
    ∀ S B w, returnedGradientCount ((P.repair S B).execute O w) ≤
      returnedGradientCount (P.execute O w) := by
  classical
  induction P with
  | halt x =>
    intro S B w
    by_cases hx : jointSupport (x, 0) ⊆ S <;>
      simp [repair, hx, execute, returnedGradientCount, batchSize]
  | ask q next ih =>
    intro S B w
    by_cases hq : BatchSupported S q.points ∧ onlineBatchSize q.points ≤ B
    · simp only [repair, if_pos hq]
      change returnedGradientCount (prependOnlineTrace q.points (answer O q.points (w 0)) _) ≤
        returnedGradientCount (prependOnlineTrace q.points (answer O q.points (w 0)) _)
      rw [prepend_call_count, prepend_call_count]
      exact Nat.add_le_add_left (ih (answer O q.points (w 0)) _ _ (fun t => w t.succ)) _
    · simp [repair, hq, execute, returnedGradientCount, batchSize]

def repairBudget (P : OnlinePolicy T K H) : OnlinePolicy T K H := P.repair ∅ H

theorem repairBudget_legal (O : StochasticOracle T Bool) (P : OnlinePolicy T K H) :
    P.repairBudget.LegalOn O H := by
  intro w
  have h := P.repair_legal_relative O ∅ H w
  exact ⟨(relative_supported_empty _).mp h.1, h.2⟩

theorem repairBudget_preserves (O : StochasticOracle T Bool) (P : OnlinePolicy T K H)
    (w : RoundWorld H) (hs : StandardZeroRespectingTrace (P.execute O w))
    (hb : returnedGradientCount (P.execute O w) ≤ H) :
    P.repairBudget.execute O w = P.execute O w :=
  P.repair_preserves_legal_trace O ∅ H w ((relative_supported_empty _).mpr hs) hb

end OnlinePolicy
end NCSCPureStochasticLB.PaperExact
