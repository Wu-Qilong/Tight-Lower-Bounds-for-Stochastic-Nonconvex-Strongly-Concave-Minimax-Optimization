import ManuscriptMemoryCoordinates

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NCSCPureStochasticLB.PaperExact.Rectangular.StochasticMemory
open KernelPolicy
variable {dx dy K : ℕ}

/-- Fixing all tapes yields a deterministic action script. This is only a proof
device; it does not expose future oracle seeds to the algorithm. -/
def scriptStep {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (n : ℕ) (d : TraceWorkspace dx dy K) (ξ : Seed) : TraceWorkspace dx dy K :=
  if d.1 = true then
    (true, d.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none)))
  else if (a n).val.1 = true then
    (true, (a n).val.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none)))
  else
    (false, 0, Function.update d.2.2 n
      (encode (decode (a n).val.2.2), encode (answer O (decode (a n).val.2.2) ξ)))

def scriptWorkspace {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (v : ℕ → Seed) : ℕ → ℕ → TraceWorkspace dx dy K → TraceWorkspace dx dy K
  | 0, _, d => d
  | H + 1, n, d => scriptWorkspace O a v H (n + 1) (scriptStep O a n d (v n))

def scriptExecute {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K) :
    (H n : ℕ) → (Fin H → Seed) → Option (Trace dx dy H K)
  | 0, n, _ => if (a n).val.1 = true then some (haltTrace (a n).val.2.1 dy 0 K) else none
  | H + 1, n, w => if (a n).val.1 = true then some (haltTrace (a n).val.2.1 dy (H + 1) K)
    else (scriptExecute O a H (n + 1) (fun i => w i.succ)).map
      (prepend (decode (a n).val.2.2) (answer O (decode (a n).val.2.2) (w 0)))

theorem script_before {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (v : ℕ → Seed) (H n : ℕ) (d : TraceWorkspace dx dy K) (j : ℕ) (hj : j < n) :
    (scriptWorkspace O a v H n d).2.2 j = d.2.2 j := by
  induction H generalizing n d with
  | zero => rfl
  | succ H ih =>
    rw [scriptWorkspace, ih (n + 1) _ (by omega)]
    simp only [scriptStep]
    split
    · simp [Function.update_of_ne (by omega : j ≠ n)]
    · split <;> simp [Function.update_of_ne (by omega : j ≠ n)]

theorem script_stopped {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (v : ℕ → Seed) (H n : ℕ) (d : TraceWorkspace dx dy K) (hd : d.1 = true) :
    (scriptWorkspace O a v H n d).1 = true ∧
    (scriptWorkspace O a v H n d).2.1 = d.2.1 ∧
    ∀ j, n ≤ j → j < n + H → (scriptWorkspace O a v H n d).2.2 j =
      (encode (fun _ => none), encode (fun _ => none)) := by
  induction H generalizing n d with
  | zero => exact ⟨hd, rfl, fun j h₁ h₂ => by omega⟩
  | succ H ih =>
    simp only [scriptWorkspace, scriptStep, hd, if_pos]
    obtain ⟨hf, ho, hh⟩ := ih (n + 1)
      (true, d.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none))) rfl
    refine ⟨hf, ho, ?_⟩
    intro j hj hj'
    by_cases he : j = n
    · subst j
      rw [script_before O a v H (n + 1) _ n (by omega)]
      simp
    · exact hh j (by omega) (by omega)

theorem script_result_stopped {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (v : ℕ → Seed) (H n : ℕ) (d : TraceWorkspace dx dy K) (hd : d.1 = true) :
    workspaceResult H n (scriptWorkspace O a v (H + 1) n d) = some (haltTrace d.2.1 dy H K) := by
  obtain ⟨hf, ho, hh⟩ := script_stopped O a v (H + 1) n d hd
  simp only [workspaceResult, hf, if_pos, ho, Option.some.injEq, haltTrace, Trace.mk.injEq, and_true]
  constructor <;> funext i <;> rw [hh (n + i.val) (by omega) (by omega)] <;> exact decode_encode _

theorem script_native {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (v : ℕ → Seed) (H n : ℕ) (d : TraceWorkspace dx dy K) (hd : d.1 ≠ true) :
    workspaceResult H n (scriptWorkspace O a v (H + 1) n d) =
      scriptExecute O a H n (fun i => v (n + i.val)) := by
  induction H generalizing n d with
  | zero =>
    simp only [scriptWorkspace, scriptStep, if_neg hd, scriptExecute]
    split
    · simp only [workspaceResult, if_pos, Option.some.injEq, haltTrace, Trace.mk.injEq, and_true]
      constructor <;> funext i <;> exact Fin.elim0 i
    · simp [workspaceResult]
  | succ H ih =>
    by_cases ha : (a n).val.1 = true
    · let d' : TraceWorkspace dx dy K :=
        (true, (a n).val.2.1, Function.update d.2.2 n (encode (fun _ => none), encode (fun _ => none)))
      have hh : (scriptWorkspace O a v (H + 1) (n + 1) d').2.2 n =
          (encode (fun _ => none), encode (fun _ => none)) := by
        rw [script_before O a v (H + 1) (n + 1) d' n (by omega)]
        simp [d']
      change workspaceResult (H + 1) n
        (scriptWorkspace O a v (H + 1) (n + 1) (scriptStep O a n d (v n))) = _
      rw [show scriptStep O a n d (v n) = d' by simp [scriptStep, hd, ha, d'],
        workspaceResult_prepend H n _ _ _ hh, script_result_stopped O a v H (n + 1) d' rfl]
      simp [scriptExecute, ha, d', prepend_empty_halt]
    · let q := decode (a n).val.2.2
      let r := answer O q (v n)
      let d' : TraceWorkspace dx dy K := (false, 0, Function.update d.2.2 n (encode q, encode r))
      have hh : (scriptWorkspace O a v (H + 1) (n + 1) d').2.2 n = (encode q, encode r) := by
        rw [script_before O a v (H + 1) (n + 1) d' n (by omega)]
        simp [d']
      change workspaceResult (H + 1) n
        (scriptWorkspace O a v (H + 1) (n + 1) (scriptStep O a n d (v n))) = _
      rw [show scriptStep O a n d (v n) = d' by simp [scriptStep, hd, ha, d', q, r],
        workspaceResult_prepend H n _ q r hh, ih (n + 1) d' (by simp [d'])]
      simp [scriptExecute, ha, q, r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem script_succ_last {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (v : ℕ → Seed) (H n : ℕ) (d : TraceWorkspace dx dy K) :
    scriptWorkspace O a v (H + 1) n d =
      scriptStep O a (n + H) (scriptWorkspace O a v H n d) (v (n + H)) := by
  induction H generalizing n d with
  | zero => rfl
  | succ H ih =>
    rw [scriptWorkspace, ih]
    simp only [scriptWorkspace, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem script_step_view {Seed : Type} (O : Oracle dx dy Seed) (a : ℕ → Action dx dy K)
    (n : ℕ) (d : TraceWorkspace dx dy K) (ξ : Seed) :
    workspaceView (n + 1) (scriptStep O a n d ξ) = advanceState O n (workspaceView n d) (a n) ξ := by
  by_cases hd : d.1 = true
  · simp only [scriptStep, if_pos hd, workspaceView_update, advanceState,
      show (workspaceView n d).1 = d.1 from rfl, if_pos hd,
      show (workspaceView n d).2.1 = d.2.1 from rfl]
  · by_cases ha : (a n).val.1 = true
    · simp only [scriptStep, if_neg hd, if_pos ha, workspaceView_update,
        advanceState, show (workspaceView n d).1 = d.1 from rfl, if_neg hd, if_pos ha]
    · simp only [scriptStep, if_neg hd, if_neg ha, workspaceView_update,
        advanceState, show (workspaceView n d).1 = d.1 from rfl, if_neg hd, if_neg ha,
        query, answerCode_encode]

/-- Private memory along fixed tapes. Post-stop values are auxiliary padding. -/
def privatePath (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (u : RandomTape) (v : ℕ → Seed) : (n : ℕ) → M.State n
  | 0 => initialSample M u.1
  | n + 1 => roundSample M O n (privatePath M O u v n) ((u.2.1 n, v n), u.2.2 n)

def actionScript (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (u : RandomTape) (v : ℕ → Seed) (n : ℕ) : Action dx dy K :=
  decisionSample M n (privatePath M O u v n) (u.2.1 n)

theorem script_eq_memory (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (u : RandomTape) (v : ℕ → Seed) (H n : ℕ) :
    scriptExecute O (actionScript M O u v) H n (fun i => v (n + i.val)) =
      (toMemory M).run? O H n (u, privatePath M O u v n) (fun i => v (n + i.val)) := by
  induction H generalizing n with
  | zero => simp [scriptExecute, MemoryAlgorithm.run?, toMemory, actionAt, actionScript]
  | succ H ih =>
    by_cases ha : (actionScript M O u v n).val.1 = true
    · simp [scriptExecute, MemoryAlgorithm.run?, toMemory, actionAt, actionScript] at ha ⊢
      simp [ha]
    · have ha' : (decisionSample M n (privatePath M O u v n) (u.2.1 n)).val.1 ≠ true := ha
      simp only [scriptExecute, if_neg ha]
      rw [show (fun i : Fin H => v (n + i.succ.val)) =
          (fun i => v (n + 1 + i.val)) by funext i; congr 1; simp only [Fin.val_succ]; omega, ih]
      simp [MemoryAlgorithm.run?, toMemory, actionAt, actionScript, privatePath,
        roundSample, roundInput, query, ha', answerCode_encode,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rfl

theorem separatedRun_succ (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (N : ℕ) (u : RandomTape) (w : Fin (N + 1) → Seed) :
    separatedRun M O (N + 1) (u, w) =
      jointSample M O N (separatedRun M O N (u, fun i => w i.castSucc))
        ((u.2.1 N, w (Fin.last N)), u.2.2 N) := rfl

theorem separatedRun_script (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (N : ℕ) (u : RandomTape) (v : ℕ → Seed) :
    separatedRun M O N (u, fun i => v i.val) =
      (workspaceView N (scriptWorkspace O (actionScript M O u v) v N 0 initialWorkspace),
        privatePath M O u v N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [separatedRun_succ]
    change jointSample M O N (separatedRun M O N (u, fun i => v i.val))
      ((u.2.1 N, v N), u.2.2 N) = _
    rw [ih, script_succ_last]
    simp only [Nat.zero_add, script_step_view]
    rfl

/-- Exact partial-trace equality for every fixed collection of tapes. -/
theorem forward_memory_eq_native (M : Model dx dy K) {Seed : Type} (O : Oracle dx dy Seed)
    (H : ℕ) (u : RandomTape) (v : ℕ → Seed) :
    forwardResult H (separatedRun M O (H + 1) (u, fun i => v i.val)).1 =
      (toMemory M).run? O H 0 ((toMemory M).initial u) (fun i => v i.val) := by
  rw [separatedRun_script, ← workspaceResult_forward,
    script_native O (actionScript M O u v) v H 0 initialWorkspace (by simp [initialWorkspace]),
    script_eq_memory]
  simp only [Nat.zero_add]
  rfl

theorem forward_memory_eq_native_finite (M : Model dx dy K) {Seed : Type}
    (O : Oracle dx dy Seed) (H : ℕ) (u : RandomTape) (w : Fin (H + 1) → Seed) :
    forwardResult H (separatedRun M O (H + 1) (u, w)).1 =
      (toMemory M).run? O H 0 ((toMemory M).initial u) (fun i => w i.castSucc) := by
  let v : ℕ → Seed := fun j => w ⟨j % (H + 1), Nat.mod_lt _ (by omega)⟩
  have hv (i : Fin (H + 1)) : v i.val = w i := by
    dsimp [v]
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  have hvec : (fun i : Fin (H + 1) => v i.val) = w := funext hv
  have hseed : (fun i : Fin H => v i.val) = (fun i => w i.castSucc) :=
    funext (fun i => hv i.castSucc)
  have h := forward_memory_eq_native M O H u v
  rw [hvec, hseed] at h
  exact h

/-- Native memory execution has the projected original-kernel law. This joins
the pointwise trace bridge to the independent-coordinate probability bridge. -/
theorem native_memory_kernel_law (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))).map (nativeCompleteCode M O H) =
    (IndexedKernelRun.initializedLaw (jointKernel M O hO ρ)
      (M.initial.map (jointInitial M)) (H + 1)).map (fun s => forwardCompleteCode H s.1) := by
  rw [← native_dummy_seed_law M O hO ρ H]
  have h := projected_joint_execution_law M O hO ρ H
  have hp (z : RandomTape × (Fin (H + 1) → Seed)) :
      forwardResult H (separatedRun M O (H + 1) z).1 =
        (toMemory M).run? O H 0 ((toMemory M).initial z.1) (fun i => z.2 i.castSucc) :=
    forward_memory_eq_native_finite M O H z.1 z.2
  simpa only [forwardCompleteCode, hp, nativeCompleteCode] using h

theorem native_memory_kernel_event (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ)
    (B : Set (Bool × TraceCode dx dy H K)) (hB : MeasurableSet B) :
    (randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))) ((nativeCompleteCode M O H) ⁻¹' B) =
    IndexedKernelRun.initializedLaw (jointKernel M O hO ρ)
      (M.initial.map (jointInitial M)) (H + 1) ((fun s => forwardCompleteCode H s.1) ⁻¹' B) := by
  have h := congrArg (fun μ : Measure (Bool × TraceCode dx dy H K) => μ B)
    (native_memory_kernel_law M O hO ρ H)
  have hm : Measurable (fun s : JointState M (H + 1) => forwardCompleteCode H s.1) :=
    (forwardCompleteCode_measurable H).comp measurable_fst
  dsimp only at h
  rw [Measure.map_apply (nativeCompleteCode_measurable M O hO H) hB,
    Measure.map_apply hm hB] at h
  exact h

theorem native_memory_kernel_risk (M : Model dx dy K) {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H : ℕ)
    (loss : Bool × TraceCode dx dy H K → ENNReal) (hloss : Measurable loss) :
    (∫⁻ z, loss (nativeCompleteCode M O H z) ∂(randomTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ)))) =
    ∫⁻ s, loss (forwardCompleteCode H s.1) ∂IndexedKernelRun.initializedLaw
      (jointKernel M O hO ρ) (M.initial.map (jointInitial M)) (H + 1) := by
  have hm : Measurable (fun s : JointState M (H + 1) => forwardCompleteCode H s.1) :=
    (forwardCompleteCode_measurable H).comp measurable_fst
  rw [← lintegral_map hloss (nativeCompleteCode_measurable M O hO H),
    native_memory_kernel_law M O hO ρ H, lintegral_map hloss hm]

end NCSCPureStochasticLB.PaperExact.Rectangular.StochasticMemory
