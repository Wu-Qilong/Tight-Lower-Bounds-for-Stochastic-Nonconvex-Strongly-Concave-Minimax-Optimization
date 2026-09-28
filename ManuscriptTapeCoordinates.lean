import ManuscriptKernelComposition

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace NCSCPureStochasticLB.PaperExact
namespace IndexedKernelRun
variable {E : Type} [MeasurableSpace E]

/-- Convert a usual finite vector into the chronological nested tape. -/
def pack : (n : ℕ) → (Fin n → E) → Tape E n
  | 0, _ => ()
  | n + 1, w => (pack n (fun i => w i.castSucc), w (Fin.last n))

theorem pack_measurable (n : ℕ) : Measurable (@pack E n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp (measurable_pi_lambda _
      (fun i => measurable_pi_apply i.castSucc))).prodMk (measurable_pi_apply (Fin.last n))

theorem finite_split_law (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) => ρ)).map
      (fun w => ((fun i : Fin n => w i.castSucc), w (Fin.last n))) =
      (Measure.pi (fun _ : Fin n => ρ)).prod ρ := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ρ) (Fin.last n)).map_eq
  have h' := congrArg (Measure.map Prod.swap) h
  rw [Measure.map_map measurable_swap
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).measurable,
    Measure.prod_swap] at h'
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove, Fin.succAbove_last] using h'

theorem pack_law (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ρ)).map (pack n) = tapeLaw ρ n := by
  induction n with
  | zero => simp [pack, tapeLaw, Measure.map_const]
  | succ n ih =>
    have hs : Measurable (fun w : Fin (n + 1) → E =>
        ((fun i : Fin n => w i.castSucc), w (Fin.last n))) :=
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)).prodMk
        (measurable_pi_apply (Fin.last n))
    change (Measure.pi (fun _ : Fin (n + 1) => ρ)).map
      (Prod.map (pack n) id ∘ (fun w => ((fun i : Fin n => w i.castSucc), w (Fin.last n)))) = _
    rw [← Measure.map_map ((pack_measurable n).prodMap measurable_id) hs,
      finite_split_law, ← Measure.map_prod_map _ _ (pack_measurable n) measurable_id,
      Measure.map_id, ih]
    rfl

/-- Dropping an unused final draw preserves the law of the preceding oracle seeds. -/
theorem drop_last_law (ρ : Measure E) [IsProbabilityMeasure ρ] (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) => ρ)).map
      (fun w => fun i : Fin n => w i.castSucc) = Measure.pi (fun _ : Fin n => ρ) := by
  have hs : Measurable (fun w : Fin (n + 1) → E =>
      ((fun i : Fin n => w i.castSucc), w (Fin.last n))) :=
    (measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)).prodMk
      (measurable_pi_apply (Fin.last n))
  have h := congrArg (Measure.map Prod.fst) (finite_split_law ρ n)
  rw [Measure.map_map measurable_fst hs, Measure.map_fst_prod] at h
  simpa only [Function.comp_def, measure_univ, one_smul] using h

/-- Coordinate pairing preserves the independence of internal and external seeds. -/
theorem paired_vector_law {F : Type} [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => ν))).map
      (fun z i => (z.1 i, z.2 i)) = Measure.pi (fun _ : Fin n => μ.prod ν) := by
  exact (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow E F (Fin n))
    (measurePreserving_arrowProdEquivProdArrow E F (Fin n)
      (fun _ => μ) (fun _ => ν))).map_eq

theorem paired_pack_law {F : Type} [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => ν))).map
      (fun z => pack n (fun i => (z.1 i, z.2 i))) = tapeLaw (μ.prod ν) n := by
  have hp : Measurable (fun z : (Fin n → E) × (Fin n → F) => fun i => (z.1 i, z.2 i)) :=
    measurable_pi_lambda _ (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have h := pack_law (μ.prod ν) n
  rw [← paired_vector_law μ ν n, Measure.map_map (pack_measurable n) hp] at h
  exact h

end IndexedKernelRun
namespace Rectangular.KernelPolicy
variable {dx dy K : ℕ}

def rangeFinEquiv (n : ℕ) : (Finset.range n) ≃ Fin n where
  toFun i := ⟨i.val, Finset.mem_range.mp i.property⟩
  invFun i := ⟨i.val, Finset.mem_range.mpr i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The first n coordinates of the fixed infinite internal tape are independent uniforms. -/
theorem internalTapeLaw_prefix (n : ℕ) :
    internalTapeLaw.map (fun u => fun i : Fin n => u i.val) =
      Measure.pi (fun _ : Fin n => KernelRandomization.uniform) := by
  have h := Measure.pi_map_piCongrLeft (rangeFinEquiv n)
    (fun _ : Fin n => KernelRandomization.uniform)
  rw [← internalTapeLaw_restrict (Finset.range n),
    Measure.map_map (MeasurableEquiv.piCongrLeft _ _).measurable
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))] at h
  exact h

/-- The original separate infinite/internal and finite/external laws give the nested pair tape. -/
theorem internal_oracle_pack_law {Seed : Type} [MeasurableSpace Seed]
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (n : ℕ) :
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin n => ρ))).map
      (fun z => IndexedKernelRun.pack n (fun i => (z.1 i.val, z.2 i))) =
      IndexedKernelRun.tapeLaw (KernelRandomization.uniform.prod ρ) n := by
  have hi : Measurable (fun u : ℕ → ℝ => fun i : Fin n => u i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hp : Measurable (fun z : (Fin n → ℝ) × (Fin n → Seed) =>
      IndexedKernelRun.pack n (fun i => (z.1 i, z.2 i))) :=
    (IndexedKernelRun.pack_measurable n).comp (measurable_pi_lambda _
      (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have hm := Measure.map_prod_map internalTapeLaw (Measure.pi (fun _ : Fin n => ρ)) hi measurable_id
  rw [Measure.map_id, internalTapeLaw_prefix] at hm
  have h := IndexedKernelRun.paired_pack_law KernelRandomization.uniform ρ n
  rw [hm, Measure.map_map hp (hi.prodMap measurable_id)] at h
  exact h

/-- Forward absorbing execution, now using the same separated tape laws as native policies. -/
theorem separated_execution_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (s₀ : ExecutionState dx dy K 0) (n : ℕ) :
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin n => ρ))).map
      (fun z => IndexedKernelRun.run (sampledStep P O) s₀ n
        (IndexedKernelRun.pack n (fun i => (z.1 i.val, z.2 i)))) =
      IndexedKernelRun.law (executionKernel P O ρ) s₀ n := by
  have hp : Measurable (fun z : (ℕ → ℝ) × (Fin n → Seed) =>
      IndexedKernelRun.pack n (fun i => (z.1 i.val, z.2 i))) :=
    (IndexedKernelRun.pack_measurable n).comp (measurable_pi_lambda _
      (fun i => ((measurable_pi_apply i.val).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have h := sampled_execution_law P O hO ρ s₀ n
  rw [← internal_oracle_pack_law ρ n,
    Measure.map_map (IndexedKernelRun.run_measurable _ (sampledStep_measurable P O hO) _ _) hp] at h
  exact h

/-- Adding the final, unused oracle draw does not change any native partial execution. -/
theorem native_execution_dummy_seed_law {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (H n : ℕ) (s : Transcript dx dy K n) :
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin (H + 1) => ρ))).map
      (fun z => completeCode P O H n s z.1 (fun i => z.2 i.castSucc)) =
    (internalTapeLaw.prod (Measure.pi (fun _ : Fin H => ρ))).map
      (fun z => completeCode P O H n s z.1 z.2) := by
  have hd : Measurable (fun w : Fin (H + 1) → Seed => fun i : Fin H => w i.castSucc) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)
  have h := Measure.map_prod_map internalTapeLaw (Measure.pi (fun _ : Fin (H + 1) => ρ))
    (measurable_id : Measurable (id : (ℕ → ℝ) → (ℕ → ℝ))) hd
  rw [Measure.map_id, IndexedKernelRun.drop_last_law] at h
  rw [h, Measure.map_map (completeCode_measurable P O hO H n s) (measurable_id.prodMap hd)]
  rfl

/-- Expected losses under the separate tape laws equal those of original kernel composition. -/
theorem separated_execution_risk {Seed : Type} [MeasurableSpace Seed]
    (P : RandomizedPolicy dx dy K) (O : Oracle dx dy Seed) (hO : JointlyMeasurable O)
    (ρ : Measure Seed) [IsProbabilityMeasure ρ] (s₀ : ExecutionState dx dy K 0) (n : ℕ)
    (loss : ExecutionState dx dy K n → ENNReal) (hloss : Measurable loss) :
    (∫⁻ z, loss (IndexedKernelRun.run (sampledStep P O) s₀ n
      (IndexedKernelRun.pack n (fun i => (z.1 i.val, z.2 i))))
      ∂(internalTapeLaw.prod (Measure.pi (fun _ : Fin n => ρ)))) =
    ∫⁻ s, loss s ∂IndexedKernelRun.law (executionKernel P O ρ) s₀ n := by
  have hp : Measurable (fun z : (ℕ → ℝ) × (Fin n → Seed) =>
      IndexedKernelRun.run (sampledStep P O) s₀ n
        (IndexedKernelRun.pack n (fun i => (z.1 i.val, z.2 i)))) :=
    (IndexedKernelRun.run_measurable _ (sampledStep_measurable P O hO) _ _).comp
      ((IndexedKernelRun.pack_measurable n).comp (measurable_pi_lambda _
        (fun i => ((measurable_pi_apply i.val).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))))
  rw [← lintegral_map hloss hp, separated_execution_law P O hO ρ s₀ n]

end Rectangular.KernelPolicy
end NCSCPureStochasticLB.PaperExact
