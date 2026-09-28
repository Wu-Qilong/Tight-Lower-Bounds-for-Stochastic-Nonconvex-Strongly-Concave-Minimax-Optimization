import ManuscriptKernelExecution

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact
namespace IndexedKernelRun

variable {A : ℕ → Type} [∀ n, MeasurableSpace (A n)]
variable {E : Type} [MeasurableSpace E]

/-- Independent fresh seeds, in chronological nested-product order. -/
def Tape (E : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Tape E n × E

instance tapeMeasurableSpace [MeasurableSpace E] : (n : ℕ) → MeasurableSpace (Tape E n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => by
    letI := tapeMeasurableSpace n
    exact inferInstanceAs (MeasurableSpace (Tape E n × E))

def tapeLaw (ρ : Measure E) : (n : ℕ) → Measure (Tape E n)
  | 0 => Measure.dirac ()
  | n + 1 => (tapeLaw ρ n).prod ρ

instance tapeLaw_probability (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsProbabilityMeasure (tapeLaw ρ n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ n ih => change IsProbabilityMeasure ((tapeLaw ρ n).prod ρ); infer_instance

def run (f : ∀ n, A n → E → A (n + 1)) (a₀ : A 0) : (n : ℕ) → Tape E n → A n
  | 0, _ => a₀
  | n + 1, w => f n (run f a₀ n w.1) w.2

theorem run_measurable (f : ∀ n, A n → E → A (n + 1))
    (hf : ∀ n, Measurable (Function.uncurry (f n))) (a₀ : A 0) (n : ℕ) :
    Measurable (run f a₀ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hf n).comp ((ih.comp measurable_fst).prodMk measurable_snd)

/-- Defined directly by kernel composition, without reference to a sampler. -/
def law (η : ∀ n, Kernel (A n) (A (n + 1))) (a₀ : A 0) : (n : ℕ) → Measure (A n)
  | 0 => Measure.dirac a₀
  | n + 1 => η n ∘ₘ law η a₀ n

theorem independent_step {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (η : Kernel X Y) (ρ : Measure E) [SFinite ρ] (f : X → E → Y)
    (hf : Measurable (Function.uncurry f)) (hlaw : ∀ a, ρ.map (f a) = η a)
    (μ : Measure X) [SFinite μ] :
    (μ.prod ρ).map (Function.uncurry f) = η ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs), Measure.bind_apply hs η.aemeasurable]
  apply lintegral_congr
  intro a
  have ha := congrArg (fun m : Measure Y => m s) (hlaw a)
  have hm : Measurable (f a) := hf.comp
    (measurable_const.prodMk measurable_id : Measurable (fun u : E => (a, u)))
  change (ρ.map (f a)) s = (η a) s at ha
  rw [Measure.map_apply hm hs] at ha
  exact ha

/-- Adaptive composition theorem for growing state/history spaces. -/
theorem run_law (η : ∀ n, Kernel (A n) (A (n + 1)))
    (ρ : Measure E) [IsProbabilityMeasure ρ]
    (f : ∀ n, A n → E → A (n + 1))
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hlaw : ∀ n a, ρ.map (f n a) = η n a) (a₀ : A 0) (n : ℕ) :
    (tapeLaw ρ n).map (run f a₀ n) = law η a₀ n := by
  induction n with
  | zero => simp [tapeLaw, run, law]
  | succ n ih =>
    have hr := run_measurable f hf a₀ n
    have hp := hr.prodMap (measurable_id : Measurable (id : E → E))
    change ((tapeLaw ρ n).prod ρ).map
      (Function.uncurry (f n) ∘ Prod.map (run f a₀ n) id) = η n ∘ₘ law η a₀ n
    rw [← Measure.map_map (hf n) hp, ← Measure.map_prod_map _ _ hr measurable_id,
      Measure.map_id, independent_step (η n) ρ (f n) (hf n) (hlaw n), ih]

end IndexedKernelRun

namespace Rectangular.KernelPolicy
variable {dx dy K : ℕ}

/-- Absorbing stopping flag, output, and the entire padded observation history. -/
abbrev ExecutionState (dx dy K n : ℕ) := Bool × Vec dx × Transcript dx dy K n

/-- A stopped process preserves its output and appends only empty observations. -/
def advanceState {Seed : Type} (O : Oracle dx dy Seed) (n : ℕ)
    (s : ExecutionState dx dy K n) (a : Action dx dy K) (ξ : Seed) :
    ExecutionState dx dy K (n + 1) :=
  if s.1 = true then
    (true, s.2.1, Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.2.2)
  else if a.val.1 = true then
    (true, a.val.2.1, Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.2.2)
  else
    (false, 0, Fin.lastCases (query a, answerCode O (query a) ξ) s.2.2)

theorem advanceState_measurable {Seed : Type} [MeasurableSpace Seed]
    (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (fun z : ExecutionState dx dy K n × (Action dx dy K × Seed) =>
      advanceState O n z.1 z.2.1 z.2.2) := by
  have hh : ∀ (f : ExecutionState dx dy K n × (Action dx dy K × Seed) →
      Code dx dy K × Code dx dy K), Measurable f →
      Measurable (fun z => (Fin.lastCases (f z) z.1.2.2 : Fin (n + 1) →
        Code dx dy K × Code dx dy K)) := by
    intro f hf
    apply measurable_pi_lambda
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.lastCases_last] using hf
    · simpa only [Fin.lastCases_castSucc] using
        (measurable_pi_apply i).comp (measurable_fst.snd.snd :
          Measurable (fun z : ExecutionState dx dy K n × (Action dx dy K × Seed) => z.1.2.2))
  apply Measurable.ite (measurableSet_eq_fun measurable_fst.fst measurable_const)
  · exact measurable_const.prodMk (measurable_fst.snd.fst.prodMk (hh _ measurable_const))
  · apply Measurable.ite
      (measurableSet_eq_fun (measurable_subtype_coe.comp measurable_snd.fst).fst measurable_const)
    · exact measurable_const.prodMk
        ((measurable_subtype_coe.comp measurable_snd.fst).snd.fst.prodMk (hh _ measurable_const))
    · exact measurable_const.prodMk (measurable_const.prodMk (hh _
        ((query_measurable.comp measurable_snd.fst).prodMk
          (answerCode_measurable O hO _ (query_measurable.comp measurable_snd.fst)
            _ measurable_snd.snd))))

/-- Original decision kernel with an independent oracle seed; no sampler appears. -/
def executionKernel {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed)
    (ρ : Measure Seed) (n : ℕ) :
    Kernel (ExecutionState dx dy K n) (ExecutionState dx dy K (n + 1)) :=
  (Kernel.id ×ₖ ((P.decision n).comap (fun s : ExecutionState dx dy K n => s.2.2)
    measurable_snd.snd ×ₖ Kernel.const _ ρ)).map
      (fun z => advanceState O n z.1 z.2.1 z.2.2)

instance executionKernel_markov {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ) :
    IsMarkovKernel (executionKernel P O ρ n) := by
  exact Kernel.IsMarkovKernel.map _ (advanceState_measurable O hO n)

def sampledStep {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (n : ℕ) (s : ExecutionState dx dy K n) (z : ℝ × Seed) :
    ExecutionState dx dy K (n + 1) := advanceState O n s (sample P n s.2.2 z.1) z.2

theorem sampledStep_measurable {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O) (n : ℕ) :
    Measurable (Function.uncurry (sampledStep P O n)) :=
  (advanceState_measurable O hO n).comp
    (measurable_fst.prodMk (((sample_measurable P n).comp
      (measurable_fst.snd.snd.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))

theorem sampledStep_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ) (s : ExecutionState dx dy K n) :
    (KernelRandomization.uniform.prod ρ).map (sampledStep P O n s) =
      executionKernel P O ρ n s := by
  have hf : Measurable (sample P n s.2.2) := (sample_measurable P n).comp
    (measurable_const.prodMk measurable_id : Measurable (fun u : ℝ => (s.2.2, u)))
  have hg : Measurable (fun z : Action dx dy K × Seed => advanceState O n s z.1 z.2) :=
    (advanceState_measurable O hO n).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (Prod.mk s : Action dx dy K × Seed →
      ExecutionState dx dy K n × (Action dx dy K × Seed)) :=
    measurable_const.prodMk measurable_id
  rw [executionKernel, Kernel.map_apply _ (advanceState_measurable O hO n),
    Kernel.prod_apply, Kernel.id_apply, Kernel.prod_apply, Kernel.comap_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (advanceState_measurable O hO n) hm]
  change (KernelRandomization.uniform.prod ρ).map
    ((fun z : Action dx dy K × Seed => advanceState O n s z.1 z.2) ∘
      Prod.map (sample P n s.2.2) id) = _
  rw [← Measure.map_map hg (hf.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id, sample_law]
  rfl

/-- Full finite-horizon law of the absorbing history process, uniformly in the oracle. -/
theorem sampled_execution_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (s₀ : ExecutionState dx dy K 0) (N : ℕ) :
    (IndexedKernelRun.tapeLaw (KernelRandomization.uniform.prod ρ) N).map
      (IndexedKernelRun.run (sampledStep P O) s₀ N) =
    IndexedKernelRun.law (executionKernel P O ρ) s₀ N :=
  IndexedKernelRun.run_law _ _ _ (sampledStep_measurable P O hO)
    (sampledStep_law P O hO ρ) s₀ N

/-- Once stopped, neither later actions nor later oracle seeds change the output. -/
theorem advanceState_stopped {Seed : Type} (O : Oracle dx dy Seed) (n : ℕ)
    (s : ExecutionState dx dy K n) (a : Action dx dy K) (ξ : Seed) (hs : s.1 = true) :
    advanceState O n s a ξ =
      (true, s.2.1, Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.2.2) := by
  simp only [advanceState, hs, if_pos]

theorem executionKernel_stopped {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ)
    (s : ExecutionState dx dy K n) (hs : s.1 = true) :
    executionKernel P O ρ n s = Measure.dirac
      (true, s.2.1, Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.2.2) := by
  rw [← sampledStep_law P O hO ρ n s]
  have hf : sampledStep P O n s = fun _ : ℝ × Seed =>
      (true, s.2.1, Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.2.2) := by
    funext z
    exact advanceState_stopped O n s _ _ hs
  rw [hf, Measure.map_const]
  simp

/-- An active stopping decision has precisely the native policy's output. -/
theorem sampledStep_stop {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (n : ℕ) (s : ExecutionState dx dy K n)
    (u : ℕ → ℝ) (ξ : Seed) (hs : s.1 ≠ true)
    (ha : (decisionAt P n (u, s.2.2)).val.1 = true) :
    sampledStep P O n s (u n, ξ) =
      (true, (toPolicy P).output n ⟨⟨(u, s.2.2), Set.mem_univ _⟩, ha⟩,
        Fin.lastCases (encode (fun _ => none), encode (fun _ => none)) s.2.2) := by
  rw [toPolicy_output]
  change advanceState O n s (decisionAt P n (u, s.2.2)) ξ = _
  simp [advanceState, hs, ha]

/-- Active continuation records exactly the native compiled batch and same-seed response. -/
theorem sampledStep_continue {Seed : Type} (P : RandomizedPolicy dx dy K)
    (O : Oracle dx dy Seed) (n : ℕ) (s : ExecutionState dx dy K n)
    (u : ℕ → ℝ) (ξ : Seed) (hs : s.1 ≠ true)
    (ha : (decisionAt P n (u, s.2.2)).val.1 ≠ true) :
    let q := ((toPolicy P).batch n ⟨⟨(u, s.2.2), Set.mem_univ _⟩, ha⟩).points
    sampledStep P O n s (u n, ξ) =
      (false, 0, Fin.lastCases (encode q, encode (answer O q ξ)) s.2.2) := by
  dsimp only
  rw [toPolicy_batch]
  change advanceState O n s (decisionAt P n (u, s.2.2)) ξ = _
  simp [advanceState, hs, ha, query, answerCode_encode]

/-- Every measurable event of the whole stopped history has the original kernel probability. -/
theorem sampled_execution_event {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (s₀ : ExecutionState dx dy K 0) (N : ℕ) (B : Set (ExecutionState dx dy K N))
    (hB : MeasurableSet B) :
    IndexedKernelRun.tapeLaw (KernelRandomization.uniform.prod ρ) N
      ((IndexedKernelRun.run (sampledStep P O) s₀ N) ⁻¹' B) =
      IndexedKernelRun.law (executionKernel P O ρ) s₀ N B := by
  have h := congrArg (fun μ : Measure (ExecutionState dx dy K N) => μ B)
    (sampled_execution_law P O hO ρ s₀ N)
  dsimp only at h
  rw [Measure.map_apply (IndexedKernelRun.run_measurable _ (sampledStep_measurable P O hO) s₀ N) hB] at h
  exact h

/-- In particular, nonnegative stopped-output or history losses have equal expectations. -/
theorem sampled_execution_risk {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (s₀ : ExecutionState dx dy K 0) (N : ℕ)
    (loss : ExecutionState dx dy K N → ENNReal) (hloss : Measurable loss) :
    (∫⁻ w, loss (IndexedKernelRun.run (sampledStep P O) s₀ N w)
      ∂IndexedKernelRun.tapeLaw (KernelRandomization.uniform.prod ρ) N) =
    ∫⁻ s, loss s ∂IndexedKernelRun.law (executionKernel P O ρ) s₀ N := by
  rw [← lintegral_map hloss
    (IndexedKernelRun.run_measurable _ (sampledStep_measurable P O hO) _ _),
    sampled_execution_law P O hO ρ s₀ N]

end Rectangular.KernelPolicy
end NCSCPureStochasticLB.PaperExact
