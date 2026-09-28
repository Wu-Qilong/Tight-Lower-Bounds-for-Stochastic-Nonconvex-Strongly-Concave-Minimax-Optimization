import ManuscriptKernelPolicy
import ManuscriptTraceEvents

noncomputable section
open MeasureTheory
namespace NCSCPureStochasticLB.PaperExact.Rectangular.KernelPolicy

variable {dx dy K : ℕ}

/-- Direct execution of the sampler, without the native policy's dependent subtypes.
At zero remaining oracle calls a final internal decision is still required. -/
def execute {Seed : Type} (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) :
    (H n : ℕ) → Transcript dx dy K n → (ℕ → ℝ) →
      (Fin H → Seed) → Option (Trace dx dy H K)
  | 0, n, s, u, _ =>
    let a := sample P n s (u n)
    if a.val.1 = true then some (haltTrace a.val.2.1 dy 0 K) else none
  | H + 1, n, s, u, w =>
    let a := sample P n s (u n)
    if a.val.1 = true then some (haltTrace a.val.2.1 dy (H + 1) K) else
      let q := decode a.val.2.2
      let r := answer O q (w 0)
      (execute P O H (n + 1) (Fin.lastCases (encode q, encode r) s) u
        (fun t => w t.succ)).map (prepend q r)

/-- Exact agreement includes early stopping, output, queries, answers, and budget failure. -/
theorem execute_eq_run {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : Transcript dx dy K n)
    (u : ℕ → ℝ) (w : Fin H → Seed) :
    execute P O H n s u w = (toPolicy P).run? O H n (u, s) w := by
  induction H generalizing n with
  | zero => simp [execute, Policy.run?, toPolicy, decisionAt]
  | succ H ih =>
    simp only [execute, Policy.run?, toPolicy, Set.mem_univ, dite_true, decisionAt]
    split
    · rfl
    · simpa only [continueBatch, append] using
        congrArg (Option.map (prepend _ _)) (ih (n + 1) _ _)

/-- No internal coordinate outside the inclusive decision window can affect execution.
The inclusive endpoint is essential: a budget of H oracle calls permits H+1 decisions. -/
theorem execute_prefix_congr {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : Transcript dx dy K n)
    (u v : ℕ → ℝ) (w : Fin H → Seed)
    (h : ∀ j, n ≤ j → j ≤ n + H → u j = v j) :
    execute P O H n s u w = execute P O H n s v w := by
  induction H generalizing n with
  | zero => simp only [execute, h n (by omega) (by omega)]
  | succ H ih =>
    have hn := h n (by omega) (by omega)
    simp only [execute, hn]
    split
    · rfl
    · apply congrArg
      apply ih
      intro j hj hj'
      exact h j (by omega) (by omega)

theorem run_prefix_congr {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : Transcript dx dy K n)
    (u v : ℕ → ℝ) (w : Fin H → Seed)
    (h : ∀ j, n ≤ j → j ≤ n + H → u j = v j) :
    (toPolicy P).run? O H n (u, s) w = (toPolicy P).run? O H n (v, s) w := by
  rw [← execute_eq_run, ← execute_eq_run]
  exact execute_prefix_congr P O H n s u v w h

/-- Success flag plus the entire encoded trace. Unlike a fallback output alone,
this distinguishes budget exhaustion from successful output of zero. -/
def completeCode {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : Transcript dx dy K n)
    (u : ℕ → ℝ) (w : Fin H → Seed) : Bool × TraceCode dx dy H K :=
  ((execute P O H n s u w).isSome, partialCode (execute P O H n s u w))

theorem completeCode_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (H n : ℕ) (s : Transcript dx dy K n) :
    Measurable (fun z : (ℕ → ℝ) × (Fin H → Seed) => completeCode P O H n s z.1 z.2) := by
  have hi : Measurable (fun z : (ℕ → ℝ) × (Fin H → Seed) => ((z.1, s), z.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hs := ((toPolicy P).runSummary_measurable O hO H n).comp hi
  have ht := ((toPolicy P).runCode_measurable O hO H n).comp hi
  simpa only [completeCode, execute_eq_run, Function.comp_def,
    Policy.summary_defined, Policy.runCode_eq_run] using hs.fst.prodMk ht

/-- The finite decision window, including the final stopping decision. -/
def decisionWindow (n H : ℕ) : Finset ℕ := Finset.Icc n (n + H)

def extendWindow (n H : ℕ) (u : (j : decisionWindow n H) → ℝ) : ℕ → ℝ :=
  fun j => if h : j ∈ decisionWindow n H then u ⟨j, h⟩ else 0

theorem extendWindow_measurable (n H : ℕ) : Measurable (extendWindow n H) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j ∈ decisionWindow n H
  · simpa only [extendWindow, dif_pos h] using
      (measurable_pi_apply (⟨j, h⟩ : decisionWindow n H))
  · simpa only [extendWindow, dif_neg h] using
      (measurable_const : Measurable (fun _ : (j : decisionWindow n H) → ℝ => (0 : ℝ)))

theorem execute_restrict {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (H n : ℕ) (s : Transcript dx dy K n)
    (u : ℕ → ℝ) (w : Fin H → Seed) :
    execute P O H n s u w =
      execute P O H n s (extendWindow n H ((decisionWindow n H).restrict u)) w := by
  apply execute_prefix_congr
  intro j hj hj'
  have hm : j ∈ decisionWindow n H := Finset.mem_Icc.mpr ⟨hj, hj'⟩
  simp [extendWindow, hm, Finset.restrict]

/-- Full execution of the native compiled policy has exactly the finite-product law.
The oracle-seed law may be arbitrary; only its independence of the internal tape is used. -/
theorem completeCode_finite_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (H n : ℕ) (s : Transcript dx dy K n) (ν : Measure (Fin H → Seed)) [SFinite ν] :
    (internalTapeLaw.prod ν).map (fun z => completeCode P O H n s z.1 z.2) =
      ((Measure.pi (fun _ : decisionWindow n H => KernelRandomization.uniform)).prod ν).map
        (fun z => completeCode P O H n s (extendWindow n H z.1) z.2) := by
  have hr : Measurable (fun u : ℕ → ℝ => (decisionWindow n H).restrict u) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  have he : Measurable (fun z : ((j : decisionWindow n H) → ℝ) × (Fin H → Seed) =>
      completeCode P O H n s (extendWindow n H z.1) z.2) :=
    (completeCode_measurable P O hO H n s).comp
      ((extendWindow_measurable n H).prodMap measurable_id)
  have hm := Measure.map_prod_map internalTapeLaw ν hr measurable_id
  rw [Measure.map_id, internalTapeLaw_restrict] at hm
  rw [hm, Measure.map_map he (hr.prodMap measurable_id)]
  congr 1
  funext z
  simp only [Function.comp_def, Prod.map, id_eq, completeCode]
  rw [← execute_restrict]

/-- The success flag prevents the fallback encoding from losing information. -/
theorem complete_encoding_injective (H : ℕ) : Function.Injective
    (fun t : Option (Trace dx dy H K) => (t.isSome, partialCode t)) := by
  intro a b h
  cases a with
  | none => cases b <;> simp_all
  | some a =>
    cases b with
    | none => simp_all
    | some b =>
      have hc : a.code = b.code := congrArg Prod.snd h
      exact congrArg some (Trace.code_injective hc)

/-- Every measurable statistic of the complete execution has the same distribution. -/
theorem execution_statistic_finite_law {Seed X : Type} [MeasurableSpace Seed]
    [MeasurableSpace X] (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (H n : ℕ) (s : Transcript dx dy K n) (ν : Measure (Fin H → Seed)) [SFinite ν]
    (f : Bool × TraceCode dx dy H K → X) (hf : Measurable f) :
    (internalTapeLaw.prod ν).map (fun z => f (completeCode P O H n s z.1 z.2)) =
      ((Measure.pi (fun _ : decisionWindow n H => KernelRandomization.uniform)).prod ν).map
        (fun z => f (completeCode P O H n s (extendWindow n H z.1) z.2)) := by
  have he : Measurable (fun z : ((j : decisionWindow n H) → ℝ) × (Fin H → Seed) =>
      completeCode P O H n s (extendWindow n H z.1) z.2) :=
    (completeCode_measurable P O hO H n s).comp
    ((extendWindow_measurable n H).prodMap
      (measurable_id : Measurable (id : (Fin H → Seed) → (Fin H → Seed))))
  simpa only [Measure.map_map hf (completeCode_measurable P O hO H n s),
    Measure.map_map hf he, Function.comp_def] using
      congrArg (Measure.map f) (completeCode_finite_law P O hO H n s ν)

/-- Equality of nonnegative expected risks, without an integrability assumption. -/
theorem execution_risk_finite_eq {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (H n : ℕ) (s : Transcript dx dy K n) (ν : Measure (Fin H → Seed)) [SFinite ν]
    (loss : Bool × TraceCode dx dy H K → ENNReal) (hloss : Measurable loss) :
    (∫⁻ z, loss (completeCode P O H n s z.1 z.2) ∂(internalTapeLaw.prod ν)) =
      ∫⁻ z, loss (completeCode P O H n s (extendWindow n H z.1) z.2)
        ∂((Measure.pi (fun _ : decisionWindow n H => KernelRandomization.uniform)).prod ν) := by
  have he : Measurable (fun z : ((j : decisionWindow n H) → ℝ) × (Fin H → Seed) =>
      completeCode P O H n s (extendWindow n H z.1) z.2) :=
    (completeCode_measurable P O hO H n s).comp
    ((extendWindow_measurable n H).prodMap
      (measurable_id : Measurable (id : (Fin H → Seed) → (Fin H → Seed))))
  rw [← lintegral_map hloss (completeCode_measurable P O hO H n s),
    ← lintegral_map hloss he, completeCode_finite_law P O hO H n s ν]

end NCSCPureStochasticLB.PaperExact.Rectangular.KernelPolicy
