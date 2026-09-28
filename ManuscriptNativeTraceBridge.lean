import ManuscriptTapeCoordinates

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace NCSCPureStochasticLB.PaperExact.Rectangular.KernelPolicy
variable {dx dy K : ℕ}

/-- An absolute-index workspace used only to compare two execution recursions. -/
abbrev TraceWorkspace (dx dy K : ℕ) := Bool × Vec dx × (ℕ → Code dx dy K × Code dx dy K)

def workspaceView (n : ℕ) (d : TraceWorkspace dx dy K) : ExecutionState dx dy K n :=
  (d.1, d.2.1, fun i => d.2.2 i.val)

def workspaceStep {Seed : Type} (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed)
    (n : ℕ) (d : TraceWorkspace dx dy K) (u : ℕ → ℝ) (ξ : Seed) : TraceWorkspace dx dy K :=
  let a := sample P n (workspaceView n d).2.2 (u n)
  if d.1 = true then
    (true, d.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none)))
  else if a.val.1 = true then
    (true, a.val.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none)))
  else
    let q := decode a.val.2.2
    (false, 0, Function.update d.2.2 n (encode q, encode (answer O q ξ)))

def workspaceRun {Seed : Type} (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) :
    ℕ → ℕ → TraceWorkspace dx dy K → (ℕ → ℝ) → (ℕ → Seed) → TraceWorkspace dx dy K
  | 0, _, d, _, _ => d
  | H + 1, n, d, u, v => workspaceRun P O H (n + 1) (workspaceStep P O n d u (v n)) u v

theorem workspaceStep_before {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (ξ : Seed) (j : ℕ) (hj : j < n) :
    (workspaceStep P O n d u ξ).2.2 j = d.2.2 j := by
  simp only [workspaceStep]
  split
  · simp [Function.update_of_ne (by omega : j ≠ n)]
  · split <;> simp [Function.update_of_ne (by omega : j ≠ n)]

theorem workspaceRun_before {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (v : ℕ → Seed) (j : ℕ) (hj : j < n) :
    (workspaceRun P O H n d u v).2.2 j = d.2.2 j := by
  induction H generalizing n d with
  | zero => rfl
  | succ H ih =>
    rw [workspaceRun, ih (n + 1) _ (by omega), workspaceStep_before P O n d u (v n) j hj]

theorem workspaceRun_stopped {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (v : ℕ → Seed) (hd : d.1 = true) :
    (workspaceRun P O H n d u v).1 = true ∧
    (workspaceRun P O H n d u v).2.1 = d.2.1 ∧
    ∀ j, n ≤ j → j < n + H → (workspaceRun P O H n d u v).2.2 j =
      (encode (fun _ => none), encode (fun _ => none)) := by
  induction H generalizing n d with
  | zero => exact ⟨hd, rfl, fun j h₁ h₂ => by omega⟩
  | succ H ih =>
    simp only [workspaceRun, workspaceStep, hd, if_pos]
    obtain ⟨hf, ho, hh⟩ := ih (n + 1)
      (true, d.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none))) rfl
    refine ⟨hf, ho, ?_⟩
    intro j hj hj'
    by_cases he : j = n
    · subst j
      rw [workspaceRun_before P O H (n + 1) _ u v n (by omega)]
      simp
    · exact hh j (by omega) (by omega)

def workspaceResult (H n : ℕ) (d : TraceWorkspace dx dy K) : Option (Trace dx dy H K) :=
  if d.1 = true then some ⟨(fun i => decode (d.2.2 (n + i.val)).1),
    (fun i => decode (d.2.2 (n + i.val)).2), d.2.1⟩ else none

theorem workspaceResult_prepend (H n : ℕ) (d : TraceWorkspace dx dy K)
    (q r : Batch dx dy K) (h : d.2.2 n = (encode q, encode r)) :
    workspaceResult (H + 1) n d = (workspaceResult H (n + 1) d).map (prepend q r) := by
  by_cases hd : d.1 = true
  · simp only [workspaceResult, if_pos hd]
    apply congrArg some
    change Trace.mk _ _ _ = Trace.mk _ _ _
    rw [Trace.mk.injEq]
    refine ⟨?_, ?_, rfl⟩
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [prepend, h, decode_encode]
      · simp [prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [prepend, h, decode_encode]
      · simp [prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp [workspaceResult, hd]

theorem workspaceResult_stopped {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (v : ℕ → Seed) (hd : d.1 = true) :
    workspaceResult H n (workspaceRun P O (H + 1) n d u v) = some (haltTrace d.2.1 dy H K) := by
  obtain ⟨hf, ho, hh⟩ := workspaceRun_stopped P O (H + 1) n d u v hd
  simp only [workspaceResult, hf, if_pos, ho, Option.some.injEq,
    haltTrace, Trace.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · funext i
    rw [hh (n + i.val) (by omega) (by omega)]
    exact decode_encode _
  · funext i
    rw [hh (n + i.val) (by omega) (by omega)]
    exact decode_encode _

theorem workspaceView_update (n : ℕ) (d : TraceWorkspace dx dy K)
    (b : Bool) (x : Vec dx) (r : Code dx dy K × Code dx dy K) :
    workspaceView (n + 1) (b, x, Function.update d.2.2 n r) =
      (b, x, Fin.lastCases r (workspaceView n d).2.2) := by
  dsimp only [workspaceView]
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [workspaceView]
  · simp [workspaceView, Function.update_of_ne (by omega : j.val ≠ n)]

theorem prepend_empty_halt (x : Vec dx) (H : ℕ) :
    prepend (fun _ => none) (fun _ => none) (haltTrace x dy H K) =
      haltTrace x dy (H + 1) K := by
  simp only [prepend, haltTrace, Trace.mk.injEq, and_true]
  constructor <;> funext i <;> refine Fin.cases rfl (fun _ => rfl) i

/-- Full pointwise native trace equality, including budget exhaustion. -/
theorem workspaceRun_native {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (v : ℕ → Seed) (hd : d.1 ≠ true) :
    workspaceResult H n (workspaceRun P O (H + 1) n d u v) =
      execute P O H n (workspaceView n d).2.2 u (fun i => v (n + i.val)) := by
  induction H generalizing n d with
  | zero =>
    simp only [workspaceRun, workspaceStep, if_neg hd, execute]
    split
    · simp only [workspaceResult, if_pos, Option.some.injEq, haltTrace, Trace.mk.injEq, and_true]
      constructor <;> funext i <;> exact Fin.elim0 i
    · simp [workspaceResult]
  | succ H ih =>
    let a := sample P n (workspaceView n d).2.2 (u n)
    let q := decode a.val.2.2
    let r := answer O q (v n)
    by_cases ha : a.val.1 = true
    · have ha' : (sample P n (workspaceView n d).2.2 (u n)).val.1 = true := ha
      let d' : TraceWorkspace dx dy K :=
        (true, a.val.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none)))
      have hh : (workspaceRun P O (H + 1) (n + 1) d' u v).2.2 n =
          (encode (fun _ => none), encode (fun _ => none)) := by
        rw [workspaceRun_before P O (H + 1) (n + 1) d' u v n (by omega)]
        simp [d']
      change workspaceResult (H + 1) n
        (workspaceRun P O (H + 1) (n + 1) (workspaceStep P O n d u (v n)) u v) = _
      have hs : workspaceStep P O n d u (v n) = d' := by
        simp [workspaceStep, hd, ha', d', a]
      rw [hs, workspaceResult_prepend H n _ _ _ hh,
        workspaceResult_stopped P O H (n + 1) d' u v rfl]
      simp [execute, ha', d', a, prepend_empty_halt]
    · have ha' : (sample P n (workspaceView n d).2.2 (u n)).val.1 ≠ true := ha
      let d' : TraceWorkspace dx dy K := (false, 0, Function.update d.2.2 n (encode q, encode r))
      have hh : (workspaceRun P O (H + 1) (n + 1) d' u v).2.2 n = (encode q, encode r) := by
        rw [workspaceRun_before P O (H + 1) (n + 1) d' u v n (by omega)]
        simp [d']
      have hs : workspaceStep P O n d u (v n) = d' := by
        simp [workspaceStep, hd, ha', d', q, r, a]
      change workspaceResult (H + 1) n
        (workspaceRun P O (H + 1) (n + 1) (workspaceStep P O n d u (v n)) u v) = _
      rw [hs, workspaceResult_prepend H n _ q r hh, ih (n + 1) d' (by simp [d'])]
      have hv := workspaceView_update n d false 0 (encode q, encode r)
      change workspaceView (n + 1) d' = _ at hv
      rw [hv]
      simp [execute, ha', q, r, a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem workspaceRun_succ_last {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (v : ℕ → Seed) :
    workspaceRun P O (H + 1) n d u v =
      workspaceStep P O (n + H) (workspaceRun P O H n d u v) u (v (n + H)) := by
  induction H generalizing n d with
  | zero => rfl
  | succ H ih =>
    rw [workspaceRun, ih]
    simp only [workspaceRun, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem workspaceStep_view {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (n : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (ξ : Seed) :
    workspaceView (n + 1) (workspaceStep P O n d u ξ) =
      sampledStep P O n (workspaceView n d) (u n, ξ) := by
  have hf : (workspaceView n d).1 = d.1 := rfl
  have ho : (workspaceView n d).2.1 = d.2.1 := rfl
  by_cases hd : d.1 = true
  · simp only [workspaceStep, if_pos hd, sampledStep, advanceState, hf, ho,
      workspaceView_update, if_pos hd]
  · by_cases ha : (sample P n (workspaceView n d).2.2 (u n)).val.1 = true
    · simp only [workspaceStep, if_neg hd, if_pos ha, sampledStep, advanceState, hf,
        workspaceView_update, if_neg hd, if_pos ha]
    · simp only [workspaceStep, if_neg hd, if_neg ha, sampledStep, advanceState, hf,
        workspaceView_update, if_neg hd, if_neg ha, query, answerCode_encode]

theorem workspaceRun_forward {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (N : ℕ) (d : TraceWorkspace dx dy K)
    (u : ℕ → ℝ) (v : ℕ → Seed) :
    workspaceView N (workspaceRun P O N 0 d u v) =
      IndexedKernelRun.run (sampledStep P O) (workspaceView 0 d) N
        (IndexedKernelRun.pack N (fun i => (u i.val, v i.val))) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [workspaceRun_succ_last]
    simp only [Nat.zero_add, workspaceStep_view, ih, IndexedKernelRun.run, IndexedKernelRun.pack,
      Fin.val_last]
    rfl

def initialWorkspace : TraceWorkspace dx dy K :=
  (false, 0, fun _ => (encode (fun _ => none), encode (fun _ => none)))

def initialExecutionState : ExecutionState dx dy K 0 := workspaceView 0 initialWorkspace

/-- Drop the final decision slot; retain failure when no stop occurred within budget. -/
def forwardResult (H : ℕ) (s : ExecutionState dx dy K (H + 1)) : Option (Trace dx dy H K) :=
  if s.1 = true then some ⟨(fun i => decode (s.2.2 i.castSucc).1),
    (fun i => decode (s.2.2 i.castSucc).2), s.2.1⟩ else none

theorem workspaceResult_forward (H : ℕ) (d : TraceWorkspace dx dy K) :
    workspaceResult H 0 d = forwardResult H (workspaceView (H + 1) d) := by
  simp [workspaceResult, forwardResult, workspaceView]

/-- The missing full trajectory bridge: exact partial traces for every pair of tapes. -/
theorem forwardResult_eq_native {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H : ℕ) (u : ℕ → ℝ) (v : ℕ → Seed) :
    forwardResult H
      (IndexedKernelRun.run (sampledStep P O) initialExecutionState (H + 1)
        (IndexedKernelRun.pack (H + 1) (fun i => (u i.val, v i.val)))) =
      (toPolicy P).run? O H 0 (u, Fin.elim0) (fun i => v i.val) := by
  rw [show initialExecutionState = workspaceView 0 (initialWorkspace (dx := dx) (dy := dy) (K := K)) from rfl,
    ← workspaceRun_forward, ← workspaceResult_forward,
    workspaceRun_native P O H 0 initialWorkspace u v (by simp [initialWorkspace]), execute_eq_run]
  simp only [Nat.zero_add]
  congr 2
  · funext i
    exact Fin.elim0 i

theorem forwardResult_eq_native_finite {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H : ℕ) (u : ℕ → ℝ) (w : Fin (H + 1) → Seed) :
    forwardResult H
      (IndexedKernelRun.run (sampledStep P O) initialExecutionState (H + 1)
        (IndexedKernelRun.pack (H + 1) (fun i => (u i.val, w i)))) =
      (toPolicy P).run? O H 0 (u, Fin.elim0) (fun i => w i.castSucc) := by
  let v : ℕ → Seed := fun j => w ⟨j % (H + 1), Nat.mod_lt _ (by omega)⟩
  have hv (i : Fin (H + 1)) : v i.val = w i := by
    dsimp [v]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hpair : (fun i : Fin (H + 1) => (u i.val, v i.val)) =
      (fun i => (u i.val, w i)) := by funext i; rw [hv]
  have hseed : (fun i : Fin H => v i.val) = (fun i => w i.castSucc) :=
    funext (fun i => hv i.castSucc)
  have h := forwardResult_eq_native P O H u v
  rw [hpair, hseed] at h
  exact h

def forwardCompleteCode (H : ℕ) (s : ExecutionState dx dy K (H + 1)) :
    Bool × TraceCode dx dy H K := ((forwardResult H s).isSome, partialCode (forwardResult H s))

theorem forwardCompleteCode_measurable (H : ℕ) : Measurable (@forwardCompleteCode dx dy K H) := by
  have he : (@forwardCompleteCode dx dy K H) = fun s =>
      if s.1 = true then (true, (fun i => encode (decode (s.2.2 i.castSucc).1)),
        (fun i => encode (decode (s.2.2 i.castSucc).2)), s.2.1)
      else (false, haltCode 0 dy H K) := by
    funext s
    by_cases hs : s.1 = true <;>
      simp [forwardCompleteCode, forwardResult, hs, partialCode, Trace.code, haltCode, haltTrace, encode]
    rfl
  rw [he]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) _ measurable_const
  apply measurable_const.prodMk
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ (fun i => normalizedCode_measurable.comp
      (((measurable_pi_apply i.castSucc).comp measurable_snd.snd).fst))
  · exact (measurable_pi_lambda _ (fun i => normalizedCode_measurable.comp
      (((measurable_pi_apply i.castSucc).comp measurable_snd.snd).snd))).prodMk measurable_snd.fst

theorem forwardState_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (N : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × (Fin N → Seed) =>
      IndexedKernelRun.run (sampledStep P O) initialExecutionState N
        (IndexedKernelRun.pack N (fun i => (z.1 i.val, z.2 i)))) :=
  (IndexedKernelRun.run_measurable _ (sampledStep_measurable P O hO) _ _).comp
    ((IndexedKernelRun.pack_measurable N).comp (measurable_pi_lambda _
      (fun i => ((measurable_pi_apply i.val).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))))

/-- End-to-end law equality on the existing native interface, with H oracle draws.
The right side is the independently defined original-kernel composition. -/
theorem native_kernel_execution_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ) :
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))).map
      (fun z => completeCode P O H 0 Fin.elim0 z.1 z.2) =
    (IndexedKernelRun.law (executionKernel P O ρ) initialExecutionState (H + 1)).map
      (forwardCompleteCode H) := by
  rw [← native_execution_dummy_seed_law P O hO ρ H 0 Fin.elim0]
  have h := congrArg (Measure.map (forwardCompleteCode (dx := dx) (dy := dy) (K := K) H))
    (separated_execution_law P O hO ρ initialExecutionState (H + 1))
  rw [Measure.map_map (forwardCompleteCode_measurable H) (forwardState_measurable P O hO (H + 1))] at h
  simpa only [Function.comp_def, forwardCompleteCode, forwardResult_eq_native_finite,
    completeCode, execute_eq_run] using h

/-- Success, stopping-output and trace events have their original-kernel probabilities. -/
theorem native_kernel_execution_event {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ)
    (B : Set (Bool × TraceCode dx dy H K)) (hB : MeasurableSet B) :
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ)))
      ((fun z => completeCode P O H 0 Fin.elim0 z.1 z.2) ⁻¹' B) =
    IndexedKernelRun.law (executionKernel P O ρ) initialExecutionState (H + 1)
      ((forwardCompleteCode H) ⁻¹' B) := by
  have h := congrArg (fun μ : Measure (Bool × TraceCode dx dy H K) => μ B)
    (native_kernel_execution_law P O hO ρ H)
  dsimp only at h
  rw [Measure.map_apply (completeCode_measurable P O hO H 0 Fin.elim0) hB,
    Measure.map_apply (forwardCompleteCode_measurable H) hB] at h
  exact h

/-- Every nonnegative measurable native trace loss has the original-kernel expectation. -/
theorem native_kernel_execution_risk {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ)
    (loss : Bool × TraceCode dx dy H K → ENNReal) (hloss : Measurable loss) :
    (∫⁻ z, loss (completeCode P O H 0 Fin.elim0 z.1 z.2)
      ∂(internalTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ)))) =
    ∫⁻ s, loss (forwardCompleteCode H s)
      ∂IndexedKernelRun.law (executionKernel P O ρ) initialExecutionState (H + 1) := by
  rw [← lintegral_map hloss (completeCode_measurable P O hO H 0 Fin.elim0),
    native_kernel_execution_law P O hO ρ H, lintegral_map hloss (forwardCompleteCode_measurable H)]

end NCSCPureStochasticLB.PaperExact.Rectangular.KernelPolicy
