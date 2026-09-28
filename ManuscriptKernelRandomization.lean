import Mathlib

/-! Constructive steps toward the kernel-to-random-tape representation.
No sampler-existence axiom is used. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped ProbabilityTheory

namespace NCSCPureStochasticLB.PaperExact.KernelRandomization

variable {A : Type*} [MeasurableSpace A]
variable (κ : Kernel A ℝ)

/-- Random numbers strictly between the two endpoints. -/
abbrev OpenUnit := Ioo (0 : ℝ) 1

/-- The generalized inverse of the kernel's CDF. -/
def quantile (a : A) (u : OpenUnit) : ℝ :=
  sInf {r : ℝ | (u : ℝ) ≤ cdf (κ a) r}

theorem quantile_set_nonempty (a : A) (u : OpenUnit) :
    ({r : ℝ | (u : ℝ) ≤ cdf (κ a) r} : Set ℝ).Nonempty := by
  obtain ⟨r, hr⟩ := ((tendsto_cdf_atTop (μ := κ a)).eventually
    (eventually_gt_nhds u.property.2)).exists
  exact ⟨r, hr.le⟩

theorem quantile_set_bddBelow (a : A) (u : OpenUnit) :
    BddBelow {r : ℝ | (u : ℝ) ≤ cdf (κ a) r} := by
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atBot (μ := κ a)).eventually
    (eventually_lt_nhds u.property.1)).exists
  refine ⟨b, ?_⟩
  intro r hr
  by_contra h
  have := (monotone_cdf (μ := κ a)) (le_of_not_ge h)
  exact (not_le_of_gt hb) (hr.trans this)

theorem quantile_lt_iff (a : A) (u : OpenUnit) (x : ℝ) :
    quantile κ a u < x ↔ ∃ r : ℝ, (u : ℝ) ≤ cdf (κ a) r ∧ r < x := by
  exact csInf_lt_iff (quantile_set_bddBelow κ a u) (quantile_set_nonempty κ a u)

theorem quantile_le_iff (a : A) (u : OpenUnit) (x : ℝ) :
    quantile κ a u ≤ x ↔ (u : ℝ) ≤ cdf (κ a) x := by
  constructor
  · intro hx
    rw [← (cdf (κ a)).iInf_Ioi_eq x]
    apply le_ciInf
    intro r
    obtain ⟨s, hs, hsr⟩ := (quantile_lt_iff κ a u r).mp (hx.trans_lt r.property)
    exact hs.trans ((monotone_cdf (μ := κ a)) hsr.le)
  · intro hx
    exact csInf_le (quantile_set_bddBelow κ a u) hx

theorem quantile_lt_iff_rat (a : A) (u : OpenUnit) (x : ℝ) :
    quantile κ a u < x ↔ ∃ q : ℚ, (q : ℝ) < x ∧ (u : ℝ) ≤ cdf (κ a) q := by
  constructor
  · intro hx
    obtain ⟨r, hr, hrx⟩ := (quantile_lt_iff κ a u x).mp hx
    obtain ⟨q, hrq, hqx⟩ := exists_rat_btwn hrx
    exact ⟨q, hqx, hr.trans ((monotone_cdf (μ := κ a)) hrq.le)⟩
  · rintro ⟨q, hqx, hq⟩
    exact ((quantile_le_iff κ a u q).mpr hq).trans_lt hqx

variable [IsMarkovKernel κ]

/-- Joint, not merely state-by-state, measurability of the inverse CDF. -/
theorem quantile_measurable : Measurable (fun z : A × OpenUnit => quantile κ z.1 z.2) := by
  apply measurable_of_Iio
  intro x
  simp only [preimage, mem_Iio, quantile_lt_iff_rat, setOf_exists]
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : (q : ℝ) < x
  · simp only [hq, true_and]
    have hc : Measurable (fun a : A => cdf (κ a) (q : ℝ)) := by
      simp_rw [cdf_eq_real, measureReal_def]
      exact (κ.measurable_coe measurableSet_Iic).ennreal_toReal
    exact measurableSet_le (measurable_subtype_coe.comp measurable_snd) (hc.comp measurable_fst)
  · simp only [hq, false_and, setOf_false]
    exact MeasurableSet.empty

/-- Lebesgue probability on the open unit interval, carried by the real line. -/
def uniform : Measure ℝ := volume.restrict (Ioo 0 1)

instance uniform_probability : IsProbabilityMeasure uniform := by
  constructor
  simp [uniform, Real.volume_Ioo]

/-- The values at and outside the endpoints are immaterial to the seed law. -/
def toOpen (u : ℝ) : OpenUnit :=
  if h : u ∈ Ioo (0 : ℝ) 1 then ⟨u, h⟩ else ⟨1 / 2, by constructor <;> norm_num⟩

theorem toOpen_measurable : Measurable toOpen := by
  unfold toOpen
  exact measurable_id.dite measurable_const measurableSet_Ioo

/-- A jointly measurable real-valued sampler, defined at every seed. -/
def realSampler (a : A) (u : ℝ) : ℝ := quantile κ a (toOpen u)

theorem realSampler_measurable : Measurable (fun z : A × ℝ => realSampler κ z.1 z.2) :=
  (quantile_measurable κ).comp
    (measurable_fst.prodMk (toOpen_measurable.comp measurable_snd))

theorem uniform_Iic {c : ℝ} (hc1 : c ≤ 1) :
    uniform (Iic c) = ENNReal.ofReal c := by
  rw [uniform, Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1 =ᵐ[volume] Ioc 0 1)]
  rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioc_of_le hc1, Real.volume_Ioc]
  simp

/-- Inverse-transform sampling realizes every state of a real Markov kernel exactly. -/
theorem realSampler_map (a : A) : uniform.map (realSampler κ a) = κ a := by
  have hm : Measurable (realSampler κ a) :=
    (realSampler_measurable κ).comp
      (measurable_const.prodMk measurable_id : Measurable (fun u : ℝ => (a, u)))
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hm measurableSet_Iic]
  have he : (realSampler κ a ⁻¹' Iic x) =ᵐ[uniform] Iic (cdf (κ a) x) := by
    change ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      (realSampler κ a u ≤ x) = (u ≤ cdf (κ a) x)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with u hu
    apply propext
    simp only [realSampler, toOpen, dif_pos hu, quantile_le_iff]
  rw [measure_congr he, uniform_Iic (cdf_le_one (μ := κ a) x),
    ofReal_cdf]

/-- One fixed, state-independent seed law represents a real transition kernel. -/
theorem real_kernel_randomization :
    ∃ f : A → ℝ → ℝ, Measurable (Function.uncurry f) ∧ ∀ a, uniform.map (f a) = κ a :=
  ⟨realSampler κ, realSampler_measurable κ, realSampler_map κ⟩

/-- Standard-Borel kernel randomization with a common, history-independent seed law.
The target is nonempty, as are the algorithm's action and memory spaces. -/
theorem standardBorel_kernel_randomization {B : Type*} [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B] (η : Kernel A B) [IsMarkovKernel η] :
    ∃ f : A → ℝ → B, Measurable (Function.uncurry f) ∧ ∀ a, uniform.map (f a) = η a := by
  classical
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv B
  let enc : B → ℝ := fun b => (e b).val
  have henc : Measurable enc := measurable_subtype_coe.comp e.measurable
  let dec : ℝ → B := fun r => if h : r ∈ s then e.symm ⟨r, h⟩ else Classical.choice ‹Nonempty B›
  have hdec : Measurable dec := e.symm.measurable.dite measurable_const hs
  have hleft : dec ∘ enc = id := by
    funext b
    simp [dec, enc]
  let ηr := η.map enc
  haveI : IsMarkovKernel ηr := Kernel.IsMarkovKernel.map η henc
  let f : A → ℝ → B := fun a u => dec (realSampler ηr a u)
  refine ⟨f, hdec.comp (realSampler_measurable ηr), ?_⟩
  intro a
  have hm : Measurable (realSampler ηr a) := (realSampler_measurable ηr).comp
    (measurable_const.prodMk measurable_id : Measurable (fun u : ℝ => (a, u)))
  change uniform.map (dec ∘ realSampler ηr a) = η a
  rw [← Measure.map_map hdec hm, realSampler_map]
  change ((η.map enc) a).map dec = η a
  rw [Kernel.map_apply η henc, Measure.map_map hdec henc, hleft, Measure.map_id]

/-- A fresh independent uniform seed implements one adaptive transition under
an arbitrary input-state law, not just at individual deterministic states. -/
theorem independent_seed_step {B : Type*} [MeasurableSpace B]
    (η : Kernel A B) [IsMarkovKernel η] (f : A → ℝ → B)
    (hf : Measurable (Function.uncurry f)) (hlaw : ∀ a, uniform.map (f a) = η a)
    (μ : Measure A) [SFinite μ] :
    (μ.prod uniform).map (Function.uncurry f) = η ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs), Measure.bind_apply hs η.aemeasurable]
  apply lintegral_congr
  intro a
  have ha := congrArg (fun m : Measure B => m s) (hlaw a)
  have hm : Measurable (f a) :=
    hf.comp (measurable_const.prodMk measurable_id : Measurable (fun u : ℝ => (a, u)))
  change (uniform.map (f a)) s = (η a) s at ha
  rw [Measure.map_apply hm hs] at ha
  exact ha

/-- A finite tape, with a fresh real coordinate appended at each step. -/
def SeedTape : ℕ → Type
  | 0 => Unit
  | n + 1 => SeedTape n × ℝ

instance seedTapeMeasurableSpace : (n : ℕ) → MeasurableSpace (SeedTape n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => by
    letI := seedTapeMeasurableSpace n
    exact inferInstanceAs (MeasurableSpace (SeedTape n × ℝ))

def seedTapeLaw : (n : ℕ) → Measure (SeedTape n)
  | 0 => Measure.dirac ()
  | n + 1 => (seedTapeLaw n).prod uniform

instance seedTapeLaw_probability (n : ℕ) : IsProbabilityMeasure (seedTapeLaw n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ n ih => change IsProbabilityMeasure ((seedTapeLaw n).prod uniform); infer_instance

/-- A time-inhomogeneous adaptive state recursion driven by the tape. -/
def tapeRun (f : ℕ → A → ℝ → A) (a₀ : A) : (n : ℕ) → SeedTape n → A
  | 0, _ => a₀
  | n + 1, w => f n (tapeRun f a₀ n w.1) w.2

theorem tapeRun_measurable (f : ℕ → A → ℝ → A)
    (hf : ∀ n, Measurable (Function.uncurry (f n))) (a₀ : A) (n : ℕ) :
    Measurable (tapeRun f a₀ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hf n).comp ((ih.comp measurable_fst).prodMk measurable_snd)

/-- The law prescribed by the transition kernels. The state may retain full history. -/
def kernelRunLaw (η : ℕ → Kernel A A) (a₀ : A) : ℕ → Measure A
  | 0 => Measure.dirac a₀
  | n + 1 => η n ∘ₘ kernelRunLaw η a₀ n

theorem tapeRun_law (η : ℕ → Kernel A A) [∀ n, IsMarkovKernel (η n)]
    (f : ℕ → A → ℝ → A) (hf : ∀ n, Measurable (Function.uncurry (f n)))
    (hlaw : ∀ n a, uniform.map (f n a) = η n a) (a₀ : A) (n : ℕ) :
    (seedTapeLaw n).map (tapeRun f a₀ n) = kernelRunLaw η a₀ n := by
  induction n with
  | zero => simp [seedTapeLaw, tapeRun, kernelRunLaw]
  | succ n ih =>
    have hr := tapeRun_measurable f hf a₀ n
    have hp : Measurable (Prod.map (tapeRun f a₀ n) (id : ℝ → ℝ)) := hr.prodMap measurable_id
    change ((seedTapeLaw n).prod uniform).map
      (Function.uncurry (f n) ∘ Prod.map (tapeRun f a₀ n) id) =
      η n ∘ₘ kernelRunLaw η a₀ n
    rw [← Measure.map_map (hf n) hp, ← Measure.map_prod_map _ _ hr measurable_id,
      Measure.map_id]
    rw [independent_seed_step (η n) (f n) (hf n) (hlaw n), ih]

/-- All finite execution laws of a standard-Borel transition system are realized
by deterministic measurable recursions using independent uniform tape coordinates. -/
theorem finite_tape_representation [StandardBorelSpace A] [Nonempty A]
    (η : ℕ → Kernel A A) [∀ n, IsMarkovKernel (η n)] :
    ∃ f : ℕ → A → ℝ → A,
      (∀ n, Measurable (Function.uncurry (f n))) ∧
      (∀ n a, uniform.map (f n a) = η n a) ∧
      ∀ a₀ n, (seedTapeLaw n).map (tapeRun f a₀ n) = kernelRunLaw η a₀ n := by
  choose f hf hlaw using fun n => standardBorel_kernel_randomization (η n)
  exact ⟨f, hf, hlaw, tapeRun_law η f hf hlaw⟩

end NCSCPureStochasticLB.PaperExact.KernelRandomization
