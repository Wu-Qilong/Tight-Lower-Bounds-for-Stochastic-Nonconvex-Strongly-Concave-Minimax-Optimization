import ManuscriptBudgetHorizon

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact
namespace Rectangular

universe u

/-- A paper-style ordered list of m queries occupies the first m slots. -/
def orderedBatch {dx dy : ℕ} (K m : ℕ) (q : Fin m → Pair dx dy) : Batch dx dy K :=
  fun k => if h : k.val < m then some (q ⟨k.val, h⟩) else none

theorem sum_prefix_slots (K m : ℕ) (hm : m ≤ K) :
    (∑ k : Fin K, if k.val < m then (1 : ℕ) else 0) = m := by
  induction K generalizing m with
  | zero =>
    have he : m = 0 := by omega
    subst m
    simp
  | succ K ih =>
    by_cases h : m ≤ K
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      rw [ih m h]
      simp [not_lt.mpr h]
    · have he : m = K + 1 := by omega
      subst m
      simp

theorem orderedBatch_size {dx dy : ℕ} (K m : ℕ) (q : Fin m → Pair dx dy) (hm : m ≤ K) :
    batchSize (orderedBatch K m q) = m := by
  unfold batchSize
  have he (k : Fin K) : (if (orderedBatch K m q k).isSome then (1 : ℕ) else 0) =
      if k.val < m then 1 else 0 := by
    by_cases h : k.val < m <;> simp [orderedBatch, h]
  simp_rw [he]
  exact sum_prefix_slots K m hm

def NonemptyBatch.ofOrdered {dx dy K m : ℕ} (q : Fin m → Pair dx dy) (hm0 : 1 ≤ m) (hmK : m ≤ K) :
    NonemptyBatch dx dy K :=
  ⟨orderedBatch K m q, by rw [orderedBatch_size K m q hmK]; exact hm0,
    by rw [orderedBatch_size K m q hmK]; exact hmK⟩

theorem answer_orderedBatch {dx dy K m : ℕ} {Seed : Type} (O : Oracle dx dy Seed)
    (q : Fin m → Pair dx dy) (ξ : Seed) :
    answer O (orderedBatch K m q) ξ =
      orderedBatch K m (fun k => (O.Gx (q k).1 (q k).2 ξ, O.Gy (q k).1 (q k).2 ξ)) := by
  funext k
  by_cases h : k.val < m <;> simp [answer, orderedBatch, h]

theorem orderedBatch_measurable {X : Type*} [MeasurableSpace X] {dx dy K m : ℕ}
    (q : X → (Fin m → Pair dx dy)) (hq : Measurable q) :
    Measurable (fun x => encode (orderedBatch K m (q x))) := by
  apply measurable_pi_lambda
  intro k
  by_cases h : k.val < m
  · simp only [encode, orderedBatch, dif_pos h]
    exact measurable_const.prodMk ((measurable_pi_apply (⟨k.val, h⟩ : Fin m)).comp hq)
  · simp only [encode, orderedBatch, dif_neg h]
    exact measurable_const

/-- A variable-length ordered batch with its usual disjoint-union measurable space. -/
abbrev OrderedQueries (dx dy K : ℕ) := Σ m : Fin (K + 1), Fin m.val → Pair dx dy

def OrderedQueries.code {dx dy K : ℕ} (q : OrderedQueries dx dy K) : Code dx dy K :=
  encode (orderedBatch K q.1.val q.2)

theorem OrderedQueries.code_measurable {dx dy K : ℕ} :
    Measurable (@OrderedQueries.code dx dy K) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro m
  exact (orderedBatch_measurable (K := K) (q := fun q : Fin m.val → Pair dx dy => q) measurable_id) hs

abbrev PositiveOrderedQueries (dx dy K : ℕ) := {q : OrderedQueries dx dy K // 1 ≤ q.1.val}

def PositiveOrderedQueries.toNative {dx dy K : ℕ} (q : PositiveOrderedQueries dx dy K) :
    NonemptyBatch dx dy K :=
  NonemptyBatch.ofOrdered q.val.2 q.property (Nat.le_of_lt_succ q.val.1.isLt)

theorem PositiveOrderedQueries.toNative_size {dx dy K : ℕ} (q : PositiveOrderedQueries dx dy K) :
    batchSize q.toNative.points = q.val.1.val :=
  orderedBatch_size K q.val.1.val q.val.2 (Nat.le_of_lt_succ q.val.1.isLt)

theorem PositiveOrderedQueries.toNative_measurable {dx dy K : ℕ} :
    Measurable (fun q : PositiveOrderedQueries dx dy K => encode q.toNative.points) :=
  OrderedQueries.code_measurable.comp measurable_subtype_coe

/-- An operational random-tape algorithm with arbitrary measurable memory.
The state spaces and rules may vary with the round. They have no instance, oracle,
or hidden oracle-seed argument. Updates see only the chosen queries and responses. -/
structure MemoryAlgorithm (Ω : Type u) [MeasurableSpace Ω] (dx dy K : ℕ) where
  State : ℕ → Type u
  stateSpace : ∀ n, MeasurableSpace (State n)
  initial : Ω → State 0
  initial_measurable : @Measurable Ω (State 0) _ (stateSpace 0) initial
  domain : ∀ n, Set (State n)
  domain_measurable : ∀ n, @MeasurableSet (State n) (stateSpace n) (domain n)
  stop : ∀ n, domain n → Bool
  stop_measurable : ∀ n, letI := stateSpace n; Measurable (stop n)
  output : ∀ n, {s : domain n // stop n s = true} → Vec dx
  output_measurable : ∀ n, letI := stateSpace n; Measurable (output n)
  batch : ∀ n, {s : domain n // stop n s ≠ true} → NonemptyBatch dx dy K
  batch_measurable : ∀ n, letI := stateSpace n; Measurable (fun s => encode (batch n s).points)
  advance : ∀ n, State n × (Code dx dy K × Code dx dy K) → State (n + 1)
  advance_measurable : ∀ n, letI := stateSpace n; letI := stateSpace (n + 1); Measurable (advance n)

attribute [instance] MemoryAlgorithm.stateSpace

def historyInit {Ω : Type u} {dx dy K n : ℕ} (s : History Ω dx dy K (n + 1)) : History Ω dx dy K n :=
  (s.1, fun t => s.2 t.castSucc)

theorem historyInit_measurable {Ω : Type u} [MeasurableSpace Ω] {dx dy K n : ℕ} :
    Measurable (@historyInit Ω dx dy K n) :=
  measurable_fst.prodMk (measurable_pi_lambda _ (fun t => (measurable_pi_apply t.castSucc).comp measurable_snd))

theorem historyInit_append {Ω : Type u} {dx dy K n : ℕ} (s : History Ω dx dy K n)
    (r : Code dx dy K × Code dx dy K) : historyInit (append s r) = s := by
  apply Prod.ext
  · rfl
  · funext t
    simp [historyInit, append]

namespace MemoryAlgorithm
variable {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ}

/-- Replay arbitrary recorded history to reconstruct memory, without an oracle. -/
def replay (A : MemoryAlgorithm Ω dx dy K) : ∀ n, History Ω dx dy K n → A.State n
  | 0, s => A.initial s.1
  | n + 1, s => A.advance n (A.replay n (historyInit s), s.2 (Fin.last n))

theorem replay_measurable (A : MemoryAlgorithm Ω dx dy K) : ∀ n, Measurable (A.replay n) := by
  intro n
  induction n with
  | zero => exact A.initial_measurable.comp measurable_fst
  | succ n ih =>
    exact (A.advance_measurable n).comp
      ((ih.comp historyInit_measurable).prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd))

theorem replay_append (A : MemoryAlgorithm Ω dx dy K) (n : ℕ) (s : History Ω dx dy K n)
    (r : Code dx dy K × Code dx dy K) :
    A.replay (n + 1) (append s r) = A.advance n (A.replay n s, r) := by
  change A.advance n (A.replay n (historyInit (append s r)), (append s r).2 (Fin.last n)) = _
  rw [historyInit_append]
  simp only [append, Fin.lastCases_last]

def replayDomain (A : MemoryAlgorithm Ω dx dy K) (n : ℕ)
    (s : {s : History Ω dx dy K n | A.replay n s ∈ A.domain n}) : A.domain n :=
  ⟨A.replay n s.val, s.property⟩

theorem replayDomain_measurable (A : MemoryAlgorithm Ω dx dy K) (n : ℕ) :
    Measurable (A.replayDomain n) :=
  ((A.replay_measurable n).comp measurable_subtype_coe).subtype_mk

def toPolicy (A : MemoryAlgorithm Ω dx dy K) : Policy Ω dx dy K where
  domain n := {s | A.replay n s ∈ A.domain n}
  domain_measurable n := (A.domain_measurable n).preimage (A.replay_measurable n)
  stop n s := A.stop n (A.replayDomain n s)
  stop_measurable n := (A.stop_measurable n).comp (A.replayDomain_measurable n)
  output n s := A.output n ⟨A.replayDomain n s.val, s.property⟩
  output_measurable n := (A.output_measurable n).comp
    (((A.replayDomain_measurable n).comp measurable_subtype_coe).subtype_mk)
  batch n s := A.batch n ⟨A.replayDomain n s.val, s.property⟩
  batch_measurable n := (A.batch_measurable n).comp
    (((A.replayDomain_measurable n).comp measurable_subtype_coe).subtype_mk)

/-- Independent operational semantics on memory states, with genuine stopping. -/
def run? {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (O : Oracle dx dy Seed) :
    (H n : ℕ) → A.State n → (Fin H → Seed) → Option (Trace dx dy H K)
  | 0, n, x, _ => by
    classical
    exact if hd : x ∈ A.domain n then
      if hs : A.stop n ⟨x, hd⟩ = true then some (haltTrace (A.output n ⟨⟨x, hd⟩, hs⟩) dy 0 K)
      else none
    else none
  | H + 1, n, x, w => by
    classical
    exact if hd : x ∈ A.domain n then
      if hs : A.stop n ⟨x, hd⟩ = true then some (haltTrace (A.output n ⟨⟨x, hd⟩, hs⟩) dy (H + 1) K)
      else
        let q := (A.batch n ⟨⟨x, hd⟩, hs⟩).points
        let r := answer O q (w 0)
        (A.run? O H (n + 1) (A.advance n (x, encode q, encode r))
          (fun t => w t.succ)).map (prepend q r)
    else none

theorem toPolicy_run {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed),
      A.toPolicy.run? O H n s w = A.run? O H n (A.replay n s) w := by
  classical
  intro H
  induction H with
  | zero =>
    intro n s w
    by_cases hd : A.replay n s ∈ A.domain n
    · by_cases hs : A.stop n ⟨A.replay n s, hd⟩ = true <;>
        simp [Policy.run?, run?, toPolicy, replayDomain, hd, hs]
    · simp [Policy.run?, run?, toPolicy, hd]
  | succ H ih =>
    intro n s w
    by_cases hd : A.replay n s ∈ A.domain n
    · by_cases hs : A.stop n ⟨A.replay n s, hd⟩ = true
      · simp [Policy.run?, run?, toPolicy, replayDomain, hd, hs]
      · simp [Policy.run?, run?, toPolicy, replayDomain, hd, hs]
        apply congrArg (Option.map _)
        change A.toPolicy.run? O H (n + 1) _ _ = _
        rw [ih, replay_append]
    · simp [Policy.run?, run?, toPolicy, hd]

theorem toPolicy_initial_run {Seed : Type} (A : MemoryAlgorithm Ω dx dy K)
    (O : Oracle dx dy Seed) (H : ℕ) (ω : Ω) (w : Fin H → Seed) :
    A.toPolicy.run? O H 0 (ω, Fin.elim0) w = A.run? O H 0 (A.initial ω) w :=
  A.toPolicy_run O H 0 _ w

/-- Representation is constructed, not assumed as an input certificate. -/
theorem exists_history_representation (A : MemoryAlgorithm Ω dx dy K) :
    ∃ P : Policy Ω dx dy K, ∀ (Seed : Type) (O : Oracle dx dy Seed) H ω (w : Fin H → Seed),
      P.run? O H 0 (ω, Fin.elim0) w = A.run? O H 0 (A.initial ω) w :=
  ⟨A.toPolicy, fun _ O H ω w => A.toPolicy_initial_run O H ω w⟩

def trace {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (O : Oracle dx dy Seed) (N : ℕ)
    (z : Ω × (Fin N → Seed)) : Trace dx dy N K :=
  (A.run? O N 0 (A.initial z.1) z.2).getD (haltTrace 0 dy N K)

theorem toPolicy_trace {Seed : Type} (A : MemoryAlgorithm Ω dx dy K)
    (O : Oracle dx dy Seed) (N : ℕ) (z : Ω × (Fin N → Seed)) :
    MeasuredOracle.trace A.toPolicy O N z = A.trace O N z := by
  simp only [MeasuredOracle.trace, trace, toPolicy_initial_run]

def loss {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (c : StationarityCriterion)
    (O : Oracle dx dy Seed) (g : Vec dx → Vec dx) (N : ℕ) (z : Ω × (Fin N → Seed)) : ℝ≥0∞ :=
  match c with
  | .norm => ENNReal.ofReal ‖g (A.trace O N z).output‖
  | .squared => ENNReal.ofReal (‖g (A.trace O N z).output‖ ^ 2)

theorem toPolicy_loss {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (c : StationarityCriterion)
    (O : Oracle dx dy Seed) (g : Vec dx → Vec dx) (N : ℕ) (z : Ω × (Fin N → Seed)) :
    MeasuredOracle.loss A.toPolicy c O g N z = A.loss c O g N z := by
  cases c <;> simp only [MeasuredOracle.loss, loss, toPolicy_trace]

theorem trace_measurable {Seed : Type} [MeasurableSpace Seed] (A : MemoryAlgorithm Ω dx dy K)
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (N : ℕ) : Measurable (A.trace O N) := by
  have he : A.trace O N = MeasuredOracle.trace A.toPolicy O N :=
    funext (fun z => (A.toPolicy_trace O N z).symm)
  rw [he]
  exact A.toPolicy.trace_measurable O hO N

theorem loss_measurable {Seed : Type} [MeasurableSpace Seed] (A : MemoryAlgorithm Ω dx dy K)
    (c : StationarityCriterion) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (g : Vec dx → Vec dx) (hg : Measurable g) (N : ℕ) : Measurable (A.loss c O g N) := by
  have he : A.loss c O g N = MeasuredOracle.loss A.toPolicy c O g N :=
    funext (fun z => (A.toPolicy_loss c O g N z).symm)
  rw [he]
  exact MeasuredOracle.loss_measurable A.toPolicy c O hO g hg N

/-- Path-dependent finite termination under a pathwise call budget, before any compilation. -/
def EventualBudget {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (O : Oracle dx dy Seed) (N : ℕ) : Prop :=
  ∀ ω (w : ℕ → Seed), ∃ H, ∃ tr : Trace dx dy H K,
    A.run? O H 0 (A.initial ω) (fun t => w t.val) = some tr ∧ calls tr ≤ N

theorem eventualBudget_iff_toPolicy {Seed : Type} (A : MemoryAlgorithm Ω dx dy K)
    (O : Oracle dx dy Seed) (N : ℕ) : A.EventualBudget O N ↔ A.toPolicy.EventualBudget O N := by
  simp only [EventualBudget, Policy.EventualBudget, Policy.runNat?, toPolicy_initial_run]

theorem eventualBudget_iff_finite {Seed : Type} [Nonempty Seed] (A : MemoryAlgorithm Ω dx dy K)
    (O : Oracle dx dy Seed) (N : ℕ) : A.EventualBudget O N ↔
      ∀ z : Ω × (Fin N → Seed), ∃ tr, A.run? O N 0 (A.initial z.1) z.2 = some tr ∧ calls tr ≤ N := by
  rw [eventualBudget_iff_toPolicy, Policy.eventualBudget_iff_finite]
  simp only [toPolicy_initial_run]

end MemoryAlgorithm

namespace Policy
variable {Ω : Type u} [MeasurableSpace Ω] {dx dy K : ℕ}

/-- Every history policy is itself a memory machine: retain the full history. -/
def toMemory (P : Policy Ω dx dy K) : MemoryAlgorithm Ω dx dy K where
  State n := History Ω dx dy K n
  stateSpace _ := inferInstance
  initial ω := (ω, Fin.elim0)
  initial_measurable := measurable_id.prodMk measurable_const
  domain := P.domain
  domain_measurable := P.domain_measurable
  stop := P.stop
  stop_measurable := P.stop_measurable
  output := P.output
  output_measurable := P.output_measurable
  batch := P.batch
  batch_measurable := P.batch_measurable
  advance _ z := append z.1 z.2
  advance_measurable _ := append_measurable

theorem toMemory_run {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed) :
    ∀ H n (s : History Ω dx dy K n) (w : Fin H → Seed),
      P.toMemory.run? O H n s w = P.run? O H n s w := by
  classical
  intro H
  induction H with
  | zero => intro n s w; rfl
  | succ H ih =>
    intro n s w
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp [MemoryAlgorithm.run?, run?, toMemory, hd, hs]
      · simp [MemoryAlgorithm.run?, run?, toMemory, hd, hs]
        apply congrArg (Option.map _)
        exact ih _ _ _
    · simp [MemoryAlgorithm.run?, run?, toMemory, hd]

theorem exists_memory_representation (P : Policy Ω dx dy K) :
    ∃ A : MemoryAlgorithm Ω dx dy K, ∀ (Seed : Type) (O : Oracle dx dy Seed) H ω (w : Fin H → Seed),
      A.run? O H 0 (A.initial ω) w = P.run? O H 0 (ω, Fin.elim0) w :=
  ⟨P.toMemory, fun _ O H ω w => P.toMemory_run O H 0 (ω, Fin.elim0) w⟩

theorem toMemory_trace {Seed : Type} (P : Policy Ω dx dy K)
    (O : Oracle dx dy Seed) (N : ℕ) (z : Ω × (Fin N → Seed)) :
    P.toMemory.trace O N z = MeasuredOracle.trace P O N z := by
  simp only [MemoryAlgorithm.trace, MeasuredOracle.trace, toMemory_run]
  rfl

theorem toMemory_loss {Seed : Type} (P : Policy Ω dx dy K) (c : StationarityCriterion)
    (O : Oracle dx dy Seed) (g : Vec dx → Vec dx) (N : ℕ) (z : Ω × (Fin N → Seed)) :
    P.toMemory.loss c O g N z = MeasuredOracle.loss P c O g N z := by
  cases c <;> simp only [MemoryAlgorithm.loss, MeasuredOracle.loss, toMemory_trace]

theorem toMemory_replay (P : Policy Ω dx dy K) :
    ∀ n (s : History Ω dx dy K n), P.toMemory.replay n s = s := by
  intro n
  induction n with
  | zero =>
    intro s
    apply Prod.ext
    · rfl
    · funext t
      exact Fin.elim0 t
  | succ n ih =>
    intro s
    change append (P.toMemory.replay n (historyInit s)) (s.2 (Fin.last n)) = s
    rw [ih]
    apply Prod.ext
    · rfl
    · funext t
      refine Fin.lastCases ?_ (fun j => ?_) t
      · simp [append]
      · simp [append, historyInit]

theorem toMemory_toPolicy_run {Seed : Type} (P : Policy Ω dx dy K) (O : Oracle dx dy Seed)
    (H n : ℕ) (s : History Ω dx dy K n) (w : Fin H → Seed) :
    P.toMemory.toPolicy.run? O H n s w = P.run? O H n s w := by
  rw [MemoryAlgorithm.toPolicy_run, toMemory_replay, toMemory_run]

end Policy

theorem MemoryAlgorithm.toPolicy_toMemory_initial_run {Ω : Type u} [MeasurableSpace Ω]
    {dx dy K : ℕ} {Seed : Type} (A : MemoryAlgorithm Ω dx dy K) (O : Oracle dx dy Seed)
    (H : ℕ) (ω : Ω) (w : Fin H → Seed) :
    A.toPolicy.toMemory.run? O H 0 (ω, Fin.elim0) w = A.run? O H 0 (A.initial ω) w := by
  rw [Policy.toMemory_run, MemoryAlgorithm.toPolicy_initial_run]

end Rectangular

namespace MemoryModel
universe u

/-- One operational algorithm per pair of dimensions, with its own independent internal law. -/
structure Family (K : ℕ) where
  Seed : ℕ → ℕ → Type u
  seedSpace : ∀ dx dy, MeasurableSpace (Seed dx dy)
  law : ∀ dx dy, @Measure (Seed dx dy) (seedSpace dx dy)
  probability : ∀ dx dy, @IsProbabilityMeasure (Seed dx dy) (seedSpace dx dy) (law dx dy)
  algorithm : ∀ dx dy, @Rectangular.MemoryAlgorithm (Seed dx dy) (seedSpace dx dy) dx dy K

attribute [instance] Family.seedSpace Family.probability

def Family.compile {K : ℕ} (A : Family.{u} K) : Rectangular.Family.{u} K where
  Seed := A.Seed
  seedSpace := A.seedSpace
  law := A.law
  probability := A.probability
  policy dx dy := (A.algorithm dx dy).toPolicy

def Family.ofHistory {K : ℕ} (A : Rectangular.Family.{u} K) : Family.{u} K where
  Seed := A.Seed
  seedSpace := A.seedSpace
  law := A.law
  probability := A.probability
  algorithm dx dy := (A.policy dx dy).toMemory

def Legal {K : ℕ} (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I →
    (∀ z : A.Seed I.dx I.dy × (Fin N → I.Seed), ∃ tr,
      (A.algorithm I.dx I.dy).run? I.oracle N 0 ((A.algorithm I.dx I.dy).initial z.1) z.2 = some tr ∧
        Rectangular.calls tr ≤ N) ∧
    ∀ᵐ z ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N),
      Rectangular.StandardSupport ((A.algorithm I.dx I.dy).trace I.oracle N z)

def risk {K : ℕ} (A : Family.{u} K) (c : StationarityCriterion) (m : StationarityObjective)
    (M : ℝ) (N : ℕ) (I : MeasuredOracle.Instance) : ℝ≥0∞ :=
  ∫⁻ z, (A.algorithm I.dx I.dy).loss c I.oracle (MeasuredOracle.Instance.field m M I) N z
    ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N)

theorem compile_legal_iff {K N : ℕ} (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) :
    MeasuredOracle.Legal A.compile valid N ↔ Legal A valid N := by
  simp only [MeasuredOracle.Legal, Legal, Family.compile,
    Rectangular.MemoryAlgorithm.toPolicy_initial_run, Rectangular.MemoryAlgorithm.toPolicy_trace]

theorem compile_risk {K : ℕ} (A : Family.{u} K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : MeasuredOracle.Instance) :
    MeasuredOracle.risk A.compile c m M N I = risk A c m M N I := by
  simp only [MeasuredOracle.risk, risk, Family.compile, Rectangular.MemoryAlgorithm.toPolicy_loss]

theorem ofHistory_legal_iff {K N : ℕ} (A : Rectangular.Family.{u} K)
    (valid : MeasuredOracle.Instance → Prop) : Legal (Family.ofHistory A) valid N ↔ MeasuredOracle.Legal A valid N := by
  simp only [Legal, MeasuredOracle.Legal, Family.ofHistory,
    Rectangular.Policy.toMemory_run, Rectangular.Policy.toMemory_trace]
  rfl

theorem ofHistory_risk {K : ℕ} (A : Rectangular.Family.{u} K) (c : StationarityCriterion)
    (m : StationarityObjective) (M : ℝ) (N : ℕ) (I : MeasuredOracle.Instance) :
    risk (Family.ofHistory A) c m M N I = MeasuredOracle.risk A c m M N I := by
  simp only [risk, MeasuredOracle.risk, Family.ofHistory, Rectangular.Policy.toMemory_loss]

def EventualLegal {K : ℕ} (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) (N : ℕ) : Prop :=
  ∀ I, valid I → (A.algorithm I.dx I.dy).EventualBudget I.oracle N ∧
    ∀ᵐ z ∂(A.law I.dx I.dy).prod (iidRoundMeasure I.law N),
      Rectangular.StandardSupport ((A.algorithm I.dx I.dy).trace I.oracle N z)

theorem eventualLegal_iff {K N : ℕ} (A : Family.{u} K) (valid : MeasuredOracle.Instance → Prop) :
    EventualLegal A valid N ↔ Legal A valid N := by
  unfold EventualLegal Legal
  apply forall_congr'
  intro I
  letI := I.seed_nonempty
  apply forall_congr'
  intro hI
  exact and_congr_left (fun _ => (A.algorithm I.dx I.dy).eventualBudget_iff_finite I.oracle N)

abbrev BudgetAlgorithm (valid : MeasuredOracle.Instance → Prop) (K N : ℕ) :=
  {A : Family.{u} K // Legal A valid N}

def complexity (valid : MeasuredOracle.Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) : ℝ≥0∞ :=
  uniformBudgetComplexity valid
    (fun N (A : BudgetAlgorithm.{u} valid K N) I => risk A.val c m M N I) (c.target ε)

/-- Equality, not merely a one-sided lower bound for a convenient algorithm subclass. -/
theorem complexity_eq_history (valid : MeasuredOracle.Instance → Prop) (K : ℕ)
    (c : StationarityCriterion) (m : StationarityObjective) (M ε : ℝ) :
    complexity.{u} valid K c m M ε = MeasuredOracle.complexity.{u} valid K c m M ε := by
  apply le_antisymm
  · apply uniformBudgetComplexity_le_of_restriction valid valid
      (fun N (A : BudgetAlgorithm.{u} valid K N) I => risk A.val c m M N I)
      (fun N (A : MeasuredOracle.BudgetAlgorithm.{u} valid K N) I => MeasuredOracle.risk A.val c m M N I)
      id (fun _ h => h) (fun _ A => ⟨Family.ofHistory A.val, (ofHistory_legal_iff A.val valid).mpr A.property⟩)
    intro N A I hI
    exact le_of_eq (ofHistory_risk A.val c m M N I)
  · apply uniformBudgetComplexity_le_of_restriction valid valid
      (fun N (A : MeasuredOracle.BudgetAlgorithm.{u} valid K N) I => MeasuredOracle.risk A.val c m M N I)
      (fun N (A : BudgetAlgorithm.{u} valid K N) I => risk A.val c m M N I)
      id (fun _ h => h) (fun _ A => ⟨A.val.compile, (compile_legal_iff A.val valid).mpr A.property⟩)
    intro N A I hI
    exact le_of_eq (compile_risk A.val c m M N I)

theorem bv_complexity_lower (P : ManuscriptBVProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptBVRateConstant * bvRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity.{u} (fun I => I.ValidBV P.M P.μ P.Δ P.σ ∧ I.RegularFor m P.M) K c m P.M P.ε := by
  rw [complexity_eq_history]
  exact P.regular_measured_complexity_lower hK c m

theorem as_complexity_lower (P : ManuscriptASProblem) {K : ℕ} (hK : 1 ≤ K)
    (c : StationarityCriterion) (m : StationarityObjective) :
    ENNReal.ofReal (manuscriptASRateConstant * manuscriptASRate P.M P.Δ P.ε (P.M / P.μ) P.σ) ≤
      complexity.{u} (fun I => I.ValidAS P.M P.μ P.Δ P.σ ∧ I.RegularFor m P.M) K c m P.M P.ε := by
  rw [complexity_eq_history]
  exact P.regular_measured_complexity_lower hK c m

end MemoryModel
end NCSCPureStochasticLB.PaperExact
