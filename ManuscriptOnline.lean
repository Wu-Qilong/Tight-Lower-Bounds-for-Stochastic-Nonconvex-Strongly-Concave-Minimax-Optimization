import ManuscriptBudgetComplexity

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact

/-- A simultaneous batch is fixed before its response is seen. -/
abbrev OnlineBatch (T K : ℕ) := Fin K → Option (Vec T × Vec T)

def onlineBatchSize {T K : ℕ} (q : OnlineBatch T K) : ℕ :=
  ∑ k, if (q k).isSome then 1 else 0

structure NonemptyOnlineBatch (T K : ℕ) where
  points : OnlineBatch T K
  size_pos : 1 ≤ onlineBatchSize points
  size_le : onlineBatchSize points ≤ K

/-- A bounded online decision tree. Its continuation receives responses, never hidden seeds
or an oracle/objective argument. Internal random choices can select the tree initially. -/
inductive OnlinePolicy (T K : ℕ) : ℕ → Type
  | halt {H : ℕ} (output : Vec T) : OnlinePolicy T K H
  | ask {H : ℕ} (batch : NonemptyOnlineBatch T K)
      (next : OnlineBatch T K → OnlinePolicy T K H) : OnlinePolicy T K (H + 1)

namespace OnlinePolicy

variable {T K H : ℕ}

def answer {Seed : Type} (O : StochasticOracle T Seed) (q : OnlineBatch T K) (ξ : Seed) :
    OnlineBatch T K := fun k =>
  match q k with
  | none => none
  | some z => some (O.Gx z.1 z.2 ξ, O.Gy z.1 z.2 ξ)

/-- Direct online execution on a finite stream, padding only after a halt. -/
def execute {Seed : Type} (O : StochasticOracle T Seed) :
    {H : ℕ} → OnlinePolicy T K H → (Fin H → Seed) → InteractionTrace T H K
  | _, .halt x, _ => ⟨fun _ _ => none, fun _ _ => none, x⟩
  | _, .ask q next, w =>
    let r := answer O q.points (w 0)
    let tail := execute O (next r) (fun t => w t.succ)
    ⟨Fin.cases q.points tail.query, Fin.cases r tail.response, tail.output⟩

def stop {Seed : Type} (O : StochasticOracle T Seed) :
    {H : ℕ} → OnlinePolicy T K H → (Fin H → Seed) → ℕ
  | _, .halt _, _ => 0
  | _, .ask q next, w => (stop O (next (answer O q.points (w 0))) (fun t => w t.succ)) + 1

theorem stop_le {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w, P.stop O w ≤ H := by
  induction P with
  | halt x => intro w; exact Nat.zero_le _
  | ask q next ih => intro w; exact Nat.succ_le_succ (ih _ _)

theorem response_consistent {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w, OracleConsistentTrace O w (P.execute O w) := by
  induction P with
  | halt x => intro w t k; rfl
  | ask q next ih =>
    intro w t k
    refine Fin.cases ?_ (fun t => ?_) t
    · rfl
    · exact ih _ _ t k

theorem queries_causal {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w w' t,
      (∀ s : Fin H, s.val < t.val → ∀ k,
        (P.execute O w).response s k = (P.execute O w').response s k) →
      (P.execute O w).query t = (P.execute O w').query t := by
  induction P with
  | halt x => intros; rfl
  | ask q next ih =>
    intro w w' t
    refine Fin.cases ?_ (fun t => ?_) t
    · intro hp; rfl
    · intro hp
      have he : answer O q.points (w 0) = answer O q.points (w' 0) := by
        funext k
        exact hp 0 (by simp) k
      simp only [execute, Fin.cases_succ]
      rw [← he]
      apply ih
      intro s hs k
      have hh := hp s.succ (by simpa using hs) k
      simpa only [execute, Fin.cases_succ, ← he] using hh

theorem output_causal {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w w', (∀ t k, (P.execute O w).response t k = (P.execute O w').response t k) →
      (P.execute O w).output = (P.execute O w').output := by
  induction P with
  | halt x => intros; rfl
  | ask q next ih =>
    intro w w' hp
    have he : answer O q.points (w 0) = answer O q.points (w' 0) := funext (hp 0)
    simp only [execute]
    rw [← he]
    apply ih
    intro t k
    simpa only [execute, Fin.cases_succ, ← he] using hp t.succ k

theorem stop_causal {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w w' n, n ≤ H →
      (∀ t : Fin H, t.val < n → ∀ k,
        (P.execute O w).response t k = (P.execute O w').response t k) →
      (P.stop O w ≤ n ↔ P.stop O w' ≤ n) := by
  induction P with
  | halt x => intros; rfl
  | ask q next ih =>
    intro w w' n hn hp
    cases n with
    | zero => simp [stop]
    | succ n =>
      have he : answer O q.points (w 0) = answer O q.points (w' 0) := by
        funext k; exact hp 0 (by simp) k
      simp only [stop, Nat.succ_le_succ_iff]
      rw [← he]
      apply ih _ _ _ n (by omega)
      intro t ht k
      simpa only [execute, Fin.cases_succ, ← he] using hp t.succ (by simpa using ht) k

theorem active_batch {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w t, t.val < P.stop O w →
      1 ≤ batchSize (P.execute O w) t ∧ batchSize (P.execute O w) t ≤ K := by
  induction P with
  | halt x => intro w t ht; simp [stop] at ht
  | ask q next ih =>
    intro w t
    refine Fin.cases ?_ (fun t => ?_) t
    · intro ht; exact ⟨q.size_pos, q.size_le⟩
    · intro ht
      exact ih _ _ t (by simpa [stop] using ht)

theorem inactive_query {Seed : Type} (O : StochasticOracle T Seed) (P : OnlinePolicy T K H) :
    ∀ w t, P.stop O w ≤ t.val → ∀ k, (P.execute O w).query t k = none := by
  induction P with
  | halt x => intros; rfl
  | ask q next ih =>
    intro w t
    refine Fin.cases ?_ (fun t => ?_) t
    · intro ht; simp [stop] at ht
    · intro ht k
      exact ih _ _ t (by simpa [stop] using ht) k

/-- These are the paper's support and pathwise budget restrictions, not assumptions of
causality or of the desired lower bound. The execution is computed from the online tree. -/
def LegalOn (O : StochasticOracle T Bool) (N : ℕ) (P : OnlinePolicy T K H) : Prop :=
  ∀ w, StandardZeroRespectingTrace (P.execute O w) ∧ returnedGradientCount (P.execute O w) ≤ N

theorem halt_zero_legal (O : StochasticOracle T Bool) (N H K : ℕ) :
    LegalOn O N (OnlinePolicy.halt (H := H) (K := K) 0) := by
  intro w
  constructor
  · constructor
    · intro t k q h; cases h
    · intro c hc; cases c <;> simp [execute, jointSupport] at hc
  · simp [execute, returnedGradientCount, batchSize]

def toBudgetRun (O : StochasticOracle T Bool) (P : OnlinePolicy T K H)
    (h : P.LegalOn O H) : BudgetStandardRun T H K O where
  trace := P.execute O
  causal_queries := P.queries_causal O
  causal_output := P.output_causal O
  response_consistent := P.response_consistent O
  zero_respecting := fun w => (h w).1
  stop := P.stop O
  stop_le := P.stop_le O
  causal_stop := P.stop_causal O
  active_batch := P.active_batch O
  inactive_query := P.inactive_query O
  calls_le := fun w => (h w).2

theorem toBudgetRun_trace (O : StochasticOracle T Bool) (P : OnlinePolicy T K H)
    (h : P.LegalOn O H) (w : RoundWorld H) : (P.toBudgetRun O h).trace w = P.execute O w := rfl

end OnlinePolicy
end NCSCPureStochasticLB.PaperExact
