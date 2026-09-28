import ManuscriptGuardPreservation
import ManuscriptCommonEvent

noncomputable section
open MeasureTheory
open Classical
open scoped ENNReal
namespace NCSCPureStochasticLB.PaperExact.GeneralProgress

variable {Seed : Type} [MeasurableSpace Seed] {R : ℕ}

def eventCount (E : Set Seed) (w : Fin R → Seed) : ℕ := by
  classical
  exact ∑ t, if w t ∈ E then 1 else 0

theorem eventCount_measurable (E : Set Seed) (hE : MeasurableSet E) :
    Measurable (@eventCount Seed R E) := by
  classical
  unfold eventCount
  apply Finset.measurable_sum
  intro t _
  exact Measurable.ite (hE.preimage (measurable_pi_apply t)) measurable_const measurable_const

theorem eval_event_measure (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (E : Set Seed) (t : Fin R) :
    (Measure.pi (fun _ : Fin R => ρ)) {w | w t ∈ E} = ρ E := by
  classical
  change (Measure.pi (fun _ : Fin R => ρ)) (Function.eval t ⁻¹' E) = _
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  simp [Function.update_apply, apply_ite]

theorem eventCount_integral (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (E : Set Seed) (hE : MeasurableSet E) :
    (∫⁻ w, (eventCount E w : ℝ≥0∞) ∂Measure.pi (fun _ : Fin R => ρ)) = (R : ℝ≥0∞) * ρ E := by
  classical
  have he : (fun w : Fin R → Seed => (eventCount E w : ℝ≥0∞)) =
      fun w => ∑ t : Fin R, ({w : Fin R → Seed | w t ∈ E}).indicator (fun _ => (1 : ℝ≥0∞)) w := by
    funext w
    simp [eventCount, Set.indicator_apply]
  rw [he, lintegral_finset_sum]
  · have hi (t : Fin R) :
        (∫⁻ w : Fin R → Seed, {w : Fin R → Seed | w t ∈ E}.indicator
          (fun _ => (1 : ℝ≥0∞)) w ∂Measure.pi (fun _ : Fin R => ρ)) = ρ E := by
      have hs : MeasurableSet {w : Fin R → Seed | w t ∈ E} :=
        hE.preimage (measurable_pi_apply t)
      exact (lintegral_indicator_one hs).trans (eval_event_measure ρ E t)
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro t _
    exact measurable_const.indicator (hE.preimage (measurable_pi_apply t))

/-- Markov's bound for occurrences of a common seed event, for arbitrary seed spaces. -/
theorem eventCount_bad_le (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (E : Set Seed) (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : ρ E ≤ p)
    (T : ℕ) (hT : 0 < T) :
    (Measure.pi (fun _ : Fin R => ρ)) {w | T ≤ eventCount E w} ≤ (R : ℝ≥0∞) * p / T := by
  have hm : Measurable (fun w : Fin R → Seed => (eventCount E w : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (eventCount_measurable E hE)
  have h := meas_ge_le_lintegral_div (μ := Measure.pi (fun _ : Fin R => ρ)) hm.aemeasurable
    (show (T : ℝ≥0∞) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hT)) (by simp : (T : ℝ≥0∞) ≠ ⊤)
  simp only [Nat.cast_le] at h
  rw [eventCount_integral ρ E hE] at h
  apply h.trans
  exact mul_le_mul_right' (mul_le_mul_left' hp (R : ℝ≥0∞)) (T : ℝ≥0∞)⁻¹

theorem eventCount_good_ge (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (E : Set Seed) (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : ρ E ≤ p)
    (T : ℕ) (hT : 0 < T) :
    1 - (R : ℝ≥0∞) * p / T ≤
      (Measure.pi (fun _ : Fin R => ρ)) {w | eventCount E w < T} := by
  have hb : MeasurableSet {w : Fin R → Seed | T ≤ eventCount E w} :=
    measurableSet_le measurable_const (eventCount_measurable E hE)
  have hc : {w : Fin R → Seed | eventCount E w < T} = {w | T ≤ eventCount E w}ᶜ := by
    ext w
    simp
  rw [hc, measure_compl hb (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left (eventCount_bad_le ρ E hE p hp T hT) 1

/-- Measurable envelope of the paper's common existential reveal event. -/
def revealEvent {T : ℕ} (ρ : Measure Seed) (g : Vec T → Seed → Vec T) : Set Seed :=
  toMeasurable ρ {ξ | ∃ u, prog 0 (g u ξ) = prog (1 / 4) u + 1}

theorem revealEvent_measurable {T : ℕ} (ρ : Measure Seed) (g : Vec T → Seed → Vec T) :
    MeasurableSet (revealEvent ρ g) := measurableSet_toMeasurable _ _

theorem revealEvent_measure_le {T : ℕ} (ρ : Measure Seed) (g : Vec T → Seed → Vec T)
    (p : ℝ) (h : CommonEventPZC ρ g p) : ρ (revealEvent ρ g) ≤ ENNReal.ofReal p := by
  rw [revealEvent, measure_toMeasurable]
  exact h.1

/-- Outside the common null skip-event, a seed advances every possible query by
at most its common event indicator. This remains simultaneous for adaptive batches. -/
theorem commonEvent_step {T : ℕ} (ρ : Measure Seed) (g : Vec T → Seed → Vec T)
    (p : ℝ) (h : CommonEventPZC ρ g p) :
    ∀ᵐ ξ ∂ρ, ∀ u, prog 0 (g u ξ) ≤ prog 0 u + if ξ ∈ revealEvent ρ g then 1 else 0 := by
  classical
  filter_upwards [h.simultaneous_no_skip] with ξ hξ
  intro u
  have hu := prog_threshold_le_zero (1 / 4) (by norm_num) u
  by_cases he : ξ ∈ revealEvent ρ g
  · simp only [if_pos he]
    have := hξ u
    omega
  · simp only [if_neg he, Nat.add_zero]
    have hn : prog 0 (g u ξ) ≠ prog (1 / 4) u + 1 := by
      intro hh
      exact he ((subset_toMeasurable ρ _) ⟨u, hh⟩)
    have := hξ u
    omega

def eventTape (E : Set Seed) (w : Fin R → Seed) : RoundWorld R :=
  fun t => decide (w t ∈ E)

omit [MeasurableSpace Seed] in
theorem eventTape_count (E : Set Seed) (w : Fin R → Seed) :
    (∑ t : Fin R, seedSuccessIncrement t (eventTape E w)) = eventCount E w := by
  simp [seedSuccessIncrement, eventTape, eventCount]

omit [MeasurableSpace Seed] in
/-- The deterministic support induction uses actual same-seed responses and
zero-respecting queries. No conditional reveal-probability witness is assumed. -/
theorem response_progress {T K : ℕ} (O : StochasticOracle T Seed)
    (tr : InteractionTrace T R K) (w : Fin R → Seed) (b : RoundWorld R)
    (hc : OracleConsistentTrace O w tr) (hz : PairZeroRespectingTrace tr)
    (hstep : ∀ t x y, pairProg (O.Gx x y (w t)) (O.Gy x y (w t)) ≤
      pairProg x y + seedSuccessIncrement t b) :
    ∀ n : ℕ, n ≤ R → ∀ s : Fin R, s.val < n → ∀ k r,
      tr.response s k = some r → pairProg r.1 r.2 ≤ roundSuccessPrefixR b n := by
  intro n
  induction n with
  | zero => intro hn s hs; omega
  | succ n ih =>
    intro hn s hs k r hr
    have hnr : n < R := by omega
    have hpref := roundSuccessPrefixR_succ b n hnr
    by_cases hsn : s.val < n
    · have hh := ih (by omega) s hsn k r hr
      omega
    · have he : s = (⟨n, hnr⟩ : Fin R) := by
        apply Fin.ext
        change s.val = n
        omega
      subst s
      let t : Fin R := ⟨n, hnr⟩
      cases hq : tr.query t k with
      | none =>
        have hh := hc t k
        rw [hq, hr] at hh
        simp at hh
      | some q =>
        have hqp := zeroRespecting_query_pairProg_le tr hz t (roundSuccessPrefixR b n)
          (fun s hs k r hr => ih (by omega) s hs k r hr) k q hq
        have hh := hc t k
        rw [hq, hr] at hh
        have he : r = (O.Gx q.1 q.2 (w t), O.Gy q.1 q.2 (w t)) := Option.some.inj hh
        rw [he]
        have hresp := hstep t q.1 q.2
        dsimp only [Prod.fst, Prod.snd]
        change pairProg (O.Gx q.1 q.2 (w t)) (O.Gy q.1 q.2 (w t)) ≤ _
        change roundSuccessPrefixR b (n + 1) =
          roundSuccessPrefixR b n + seedSuccessIncrement t b at hpref
        omega

omit [MeasurableSpace Seed] in
theorem output_progress {T K : ℕ} (O : StochasticOracle T Seed)
    (tr : InteractionTrace T R K) (w : Fin R → Seed) (b : RoundWorld R)
    (hc : OracleConsistentTrace O w tr) (hz : PairZeroRespectingTrace tr)
    (hstep : ∀ t x y, pairProg (O.Gx x y (w t)) (O.Gy x y (w t)) ≤
      pairProg x y + seedSuccessIncrement t b) :
    prog 0 tr.output ≤ ∑ t : Fin R, seedSuccessIncrement t b := by
  apply prog_zero_le_of_zero_above
  intro i hi
  by_contra hne
  obtain ⟨s, k, r, hr, hir⟩ := hz.2 hne
  have hidx := index_succ_le_pairProg_of_mem_psupp hir
  have hresp := response_progress O tr w b hc hz hstep R le_rfl s s.isLt k r hr
  rw [roundSuccessPrefixR_total] at hresp
  omega

/-- Generic quadratic lift of an arbitrary-seed base estimator. -/
def liftedOracle {T : ℕ} (g : Vec T → Seed → Vec T) (P : LiftParameters) :
    StochasticOracle T Seed where
  Gx x y _ := liftedGx P x y false
  Gy x y ξ := P.q • g (P.β • y) ξ - P.ν • (y - P.γ • x)

theorem lifted_commonEvent_step {T : ℕ} (ρ : Measure Seed) (g : Vec T → Seed → Vec T)
    (p : ℝ) (h : CommonEventPZC ρ g p) (P : LiftParameters) :
    ∀ᵐ ξ ∂ρ, ∀ x y,
      pairProg ((liftedOracle g P).Gx x y ξ) ((liftedOracle g P).Gy x y ξ) ≤
        pairProg x y + if ξ ∈ revealEvent ρ g then 1 else 0 := by
  filter_upwards [commonEvent_step ρ g p h] with ξ hξ
  intro x y
  have hx := liftedGx_prog_le_pairProg P x y false
  have hbase := hξ (P.β • y)
  have hscale := prog_zero_smul_le P.β y
  have hscale' := prog_zero_smul_le P.q (g (P.β • y) ξ)
  have hcouple := lift_dual_coupling_prog_le_pairProg P x y
  have hy := prog_zero_sub_le_max (P.q • g (P.β • y) ξ) (P.ν • (y - P.γ • x))
  have hypair : prog 0 y ≤ pairProg x y := Nat.le_max_right _ _
  change max (prog 0 (liftedGx P x y false))
    (prog 0 (P.q • g (P.β • y) ξ - P.ν • (y - P.γ • x))) ≤ _
  omega

theorem seed_steps_ae {T : ℕ} (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    (O : StochasticOracle T Seed) (E : Set Seed)
    (hstep : ∀ᵐ ξ ∂ρ, ∀ x y, pairProg (O.Gx x y ξ) (O.Gy x y ξ) ≤
      pairProg x y + if ξ ∈ E then 1 else 0) :
    ∀ᵐ w ∂Measure.pi (fun _ : Fin R => ρ), ∀ t x y,
      pairProg (O.Gx x y (w t)) (O.Gy x y (w t)) ≤
        pairProg x y + seedSuccessIncrement t (eventTape E w) := by
  apply ae_all_iff.mpr
  intro t
  have ht := (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin R => ρ) (i := t)).eventually hstep
  simpa only [Function.eval, seedSuccessIncrement, eventTape, decide_eq_true_eq] using ht

/-- Arbitrary internal randomness and arbitrary independent oracle seeds. The
trace may be adaptively generated; its actual consistency/support suffice. -/
theorem trace_progress_probability {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (O : StochasticOracle T Seed) (E : Set Seed) (hE : MeasurableSet E)
    (p : ℝ≥0∞) (hp : ρ E ≤ p) (hT : 0 < T)
    (hstep : ∀ᵐ ξ ∂ρ, ∀ x y, pairProg (O.Gx x y ξ) (O.Gy x y ξ) ≤
      pairProg x y + if ξ ∈ E then 1 else 0)
    (tr : Ω × (Fin R → Seed) → InteractionTrace T R K)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      OracleConsistentTrace O z.2 (tr z) ∧ PairZeroRespectingTrace (tr z)) :
    1 - (R : ℝ≥0∞) * p / T ≤
      (η.prod (Measure.pi (fun _ : Fin R => ρ))) {z | prog 0 (tr z).output < T} := by
  have hsteps := (Measure.quasiMeasurePreserving_snd
    (μ := η) (ν := Measure.pi (fun _ : Fin R => ρ))).tendsto_ae.eventually
      (seed_steps_ae ρ O E hstep)
  have hbound : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      prog 0 (tr z).output ≤ eventCount E z.2 := by
    filter_upwards [hlegal, hsteps] with z hz hsz
    have hh := output_progress O (tr z) z.2 (eventTape E z.2) hz.1 hz.2 hsz
    simpa only [eventTape_count] using hh
  have hmeasure : (η.prod (Measure.pi (fun _ : Fin R => ρ)))
      {z : Ω × (Fin R → Seed) | eventCount E z.2 < T} =
      (Measure.pi (fun _ : Fin R => ρ)) {w | eventCount E w < T} := by
    rw [show {z : Ω × (Fin R → Seed) | eventCount E z.2 < T} =
      Set.univ ×ˢ {w | eventCount E w < T} by ext z; simp]
    rw [Measure.prod_prod, measure_univ, one_mul]
  apply (eventCount_good_ge ρ E hE p hp T hT).trans
  rw [← hmeasure]
  apply measure_mono_ae
  filter_upwards [hbound] with z hz
  exact fun hh => lt_of_le_of_lt hz hh

/-- Common-event Definition 3.4 now yields the exact bound for the generic lift,
without a Bernoulli restriction or an assumed progress witness. -/
theorem lifted_progress_probability {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (g : Vec T → Seed → Vec T) (p : ℝ) (h : CommonEventPZC ρ g p)
    (P : LiftParameters) (hT : 0 < T)
    (tr : Ω × (Fin R → Seed) → InteractionTrace T R K)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      OracleConsistentTrace (liftedOracle g P) z.2 (tr z) ∧ PairZeroRespectingTrace (tr z)) :
    1 - (R : ℝ≥0∞) * ENNReal.ofReal p / T ≤
      (η.prod (Measure.pi (fun _ : Fin R => ρ))) {z | prog 0 (tr z).output < T} :=
  trace_progress_probability η ρ (liftedOracle g P) (revealEvent ρ g)
    (revealEvent_measurable ρ g) (ENNReal.ofReal p) (revealEvent_measure_le ρ g p h) hT
    (lifted_commonEvent_step ρ g p h P) tr hlegal

omit [MeasurableSpace Seed] in
/-- Native successful execution has the actual oracle responses, including halt padding. -/
theorem native_response_consistent {Ω : Type*} [MeasurableSpace Ω] {T K : ℕ}
    (P : Rectangular.Policy Ω T T K) (O : Rectangular.Oracle T T Seed) :
    ∀ H n (s : Rectangular.History Ω T T K n) (w : Fin H → Seed)
      (tr : Rectangular.Trace T T H K), P.run? O H n s w = some tr →
      OracleConsistentTrace O.toSquare w tr.toSquare := by
  classical
  intro H
  induction H with
  | zero => intro n s w tr hr t; exact Fin.elim0 t
  | succ H ih =>
    intro n s w tr hr
    by_cases hd : s ∈ P.domain n
    · by_cases hs : P.stop n ⟨s, hd⟩ = true
      · simp [Rectangular.Policy.run?, hd, hs] at hr
        subst tr
        intro t k
        rfl
      · let q := (P.batch n ⟨⟨s, hd⟩, hs⟩).points
        let r := Rectangular.answer O q (w 0)
        simp only [Rectangular.Policy.run?, dif_pos hd, dif_neg hs] at hr
        change (P.run? O H (n + 1) (Rectangular.append s
          (Rectangular.encode q, Rectangular.encode r)) (fun t => w t.succ)).map
          (Rectangular.prepend q r) = some tr at hr
        cases ht : P.run? O H (n + 1) (Rectangular.append s
            (Rectangular.encode q, Rectangular.encode r)) (fun t => w t.succ) with
        | none => simp [ht] at hr
        | some tail =>
          rw [ht] at hr
          change some (Rectangular.prepend q r tail) = some tr at hr
          have hr := Option.some.inj hr
          subst tr
          intro t k
          refine Fin.cases ?_ (fun j => ?_) t
          · change Rectangular.answer O q (w 0) k = _
            simp only [Rectangular.answer, Rectangular.prepend, Rectangular.Trace.toSquare,
              Fin.cases_zero, Rectangular.Oracle.toSquare]
            cases q k <;> rfl
          · exact ih (n + 1) _ (fun t => w t.succ) tail ht j k
    · simp [Rectangular.Policy.run?, hd] at hr

/-- Operational form: the trace assumptions are derived from `Policy.run?`
and its a.e. legality event, not supplied as a separate progress witness. -/
theorem native_progress_probability {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (P : Rectangular.Policy Ω T T K) (O : Rectangular.Oracle T T Seed)
    (E : Set Seed) (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : ρ E ≤ p) (hT : 0 < T)
    (hstep : ∀ᵐ ξ ∂ρ, ∀ x y, pairProg (O.Gx x y ξ) (O.Gy x y ξ) ≤
      pairProg x y + if ξ ∈ E then 1 else 0)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)), P.LegalEvent O R R z) :
    1 - (R : ℝ≥0∞) * p / T ≤ (η.prod (Measure.pi (fun _ : Fin R => ρ)))
      {z | prog 0 (MeasuredOracle.trace P O R z).output < T} := by
  apply trace_progress_probability η ρ O.toSquare E hE p hp hT hstep
    (fun z => (MeasuredOracle.trace P O R z).toSquare)
  filter_upwards [hlegal] with z hz
  obtain ⟨tr, ht, hs, _⟩ := (Rectangular.Policy.legalEvent_iff_native _ _ _ _ _).mp hz
  have hc := native_response_consistent P O R 0 (z.1, Fin.elim0) z.2 tr ht
  have hp := standardZeroRespecting_implies_pair tr.toSquare
    ((Rectangular.support_toSquare tr).mpr hs)
  simpa only [MeasuredOracle.trace, ht, Option.getD_some] using And.intro hc hp

def liftedRectOracle {T : ℕ} (g : Vec T → Seed → Vec T) (L : LiftParameters) :
    Rectangular.Oracle T T Seed := ⟨(liftedOracle g L).Gx, (liftedOracle g L).Gy⟩

theorem native_lifted_progress_probability {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (P : Rectangular.Policy Ω T T K) (g : Vec T → Seed → Vec T)
    (p : ℝ) (h : CommonEventPZC ρ g p) (L : LiftParameters) (hT : 0 < T)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      P.LegalEvent (liftedRectOracle g L) R R z) :
    1 - (R : ℝ≥0∞) * ENNReal.ofReal p / T ≤ (η.prod (Measure.pi (fun _ : Fin R => ρ)))
      {z | prog 0 (MeasuredOracle.trace P (liftedRectOracle g L) R z).output < T} :=
  native_progress_probability η ρ P (liftedRectOracle g L) (revealEvent ρ g)
    (revealEvent_measurable ρ g) (ENNReal.ofReal p) (revealEvent_measure_le ρ g p h) hT
    (lifted_commonEvent_step ρ g p h L) hlegal

theorem probability_real_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : Set X) (p : ℝ) (hp : 0 ≤ p)
    (R T : ℕ) (hT : 0 < T)
    (h : 1 - (R : ℝ≥0∞) * ENNReal.ofReal p / T ≤ μ E) :
    1 - p * R / T ≤ μ.real E := by
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mp
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  simpa [ENNReal.ofReal_sub _ (show 0 ≤ p * R / T by positivity),
    ENNReal.ofReal_div_of_pos hTr, ENNReal.ofReal_mul hp, mul_comm] using h

theorem native_lifted_progress_real {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (P : Rectangular.Policy Ω T T K) (g : Vec T → Seed → Vec T)
    (p : ℝ) (hp : 0 ≤ p) (h : CommonEventPZC ρ g p) (L : LiftParameters) (hT : 0 < T)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      P.LegalEvent (liftedRectOracle g L) R R z) :
    1 - p * R / T ≤ (η.prod (Measure.pi (fun _ : Fin R => ρ))).real
      {z | prog 0 (MeasuredOracle.trace P (liftedRectOracle g L) R z).output < T} :=
  probability_real_bound _ _ p hp R T hT
    (native_lifted_progress_probability η ρ P g p h L hT hlegal)

/-- A probability event with a pointwise loss barrier gives a risk lower bound. -/
theorem event_risk_lower {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : Set X) (hE : MeasurableSet E) (q a : ℝ≥0∞) (hq : q ≤ μ E)
    (loss : X → ℝ≥0∞) (hL : ∀ᵐ z ∂μ, z ∈ E → a ≤ loss z) :
    a * q ≤ ∫⁻ z, loss z ∂μ := by
  calc
    a * q ≤ a * μ E := mul_le_mul_left' hq a
    _ = ∫⁻ z, E.indicator (fun _ => a) z ∂μ := by
      rw [lintegral_indicator hE, setLIntegral_const]
    _ ≤ ∫⁻ z, loss z ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with z hz
      by_cases he : z ∈ E
      · simpa [Set.indicator_of_mem he] using hz he
      · simp [Set.indicator_of_not_mem he]

theorem trace_risk_lower {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (O : StochasticOracle T Seed) (E : Set Seed) (hE : MeasurableSet E)
    (p : ℝ≥0∞) (hp : ρ E ≤ p) (hT : 0 < T)
    (hstep : ∀ᵐ ξ ∂ρ, ∀ x y, pairProg (O.Gx x y ξ) (O.Gy x y ξ) ≤
      pairProg x y + if ξ ∈ E then 1 else 0)
    (tr : Ω × (Fin R → Seed) → InteractionTrace T R K)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      OracleConsistentTrace O z.2 (tr z) ∧ PairZeroRespectingTrace (tr z))
    (loss : Ω × (Fin R → Seed) → ℝ≥0∞) (a : ℝ≥0∞)
    (hL : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      prog 0 (tr z).output < T → a ≤ loss z) :
    a * (1 - (R : ℝ≥0∞) * p / T) ≤
      ∫⁻ z, loss z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)) := by
  have hsteps := (Measure.quasiMeasurePreserving_snd
    (μ := η) (ν := Measure.pi (fun _ : Fin R => ρ))).tendsto_ae.eventually
      (seed_steps_ae ρ O E hstep)
  let A : Set (Ω × (Fin R → Seed)) := {z | eventCount E z.2 < T}
  have hA : MeasurableSet A := measurableSet_lt
    ((eventCount_measurable E hE).comp measurable_snd) measurable_const
  have hprob : 1 - (R : ℝ≥0∞) * p / T ≤
      (η.prod (Measure.pi (fun _ : Fin R => ρ))) A := by
    have he : A = Set.univ ×ˢ {w | eventCount E w < T} := by ext z; simp [A]
    rw [he, Measure.prod_prod, measure_univ, one_mul]
    exact eventCount_good_ge ρ E hE p hp T hT
  apply event_risk_lower _ A hA _ a hprob loss
  filter_upwards [hlegal, hsteps, hL] with z hz hsz hLz
  intro hAz
  have hb := output_progress O (tr z) z.2 (eventTape E z.2) hz.1 hz.2 hsz
  rw [eventTape_count] at hb
  exact hLz (lt_of_le_of_lt hb hAz)

/-- Risk bound for the actual native execution, with response consistency derived internally. -/
theorem native_lifted_risk_lower {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (P : Rectangular.Policy Ω T T K) (g : Vec T → Seed → Vec T)
    (p : ℝ) (h : CommonEventPZC ρ g p) (L : LiftParameters) (hT : 0 < T)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      P.LegalEvent (liftedRectOracle g L) R R z)
    (loss : Ω × (Fin R → Seed) → ℝ≥0∞) (a : ℝ≥0∞)
    (hL : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      prog 0 (MeasuredOracle.trace P (liftedRectOracle g L) R z).output < T → a ≤ loss z) :
    a * (1 - (R : ℝ≥0∞) * ENNReal.ofReal p / T) ≤
      ∫⁻ z, loss z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)) := by
  apply trace_risk_lower η ρ (liftedOracle g L) (revealEvent ρ g)
    (revealEvent_measurable ρ g) (ENNReal.ofReal p) (revealEvent_measure_le ρ g p h) hT
    (lifted_commonEvent_step ρ g p h L)
    (fun z => (MeasuredOracle.trace P (liftedRectOracle g L) R z).toSquare) ?_ loss a hL
  filter_upwards [hlegal] with z hz
  obtain ⟨tr, ht, hs, _⟩ := (Rectangular.Policy.legalEvent_iff_native _ _ _ _ _).mp hz
  have hc := native_response_consistent P (liftedRectOracle g L) R 0
    (z.1, Fin.elim0) z.2 tr ht
  have hp := standardZeroRespecting_implies_pair tr.toSquare
    ((Rectangular.support_toSquare tr).mpr hs)
  simpa only [MeasuredOracle.trace, ht, Option.getD_some] using And.intro hc hp

/-- The analytic terminal-gradient barrier integrated against an arbitrary seed law.
The lift certificate is constructed from the chain, not assumed as an extra field. -/
theorem native_primal_moments {Ω : Type*} [MeasurableSpace Ω]
    (η : Measure Ω) [IsProbabilityMeasure η] (ρ : Measure Seed) [IsProbabilityMeasure ρ]
    {T K : ℕ} (P : Rectangular.Policy Ω T T K) (g : Vec T → Seed → Vec T)
    (p : ℝ) (h : CommonEventPZC ρ g p) (L : LiftParameters)
    (C : ExplicitZeroChainCertificate T) (B : BaseOracle T)
    (ε : ℝ) (hε : 0 < ε) (hγq : L.γ * L.q = 2 * ε)
    (hratio : ℓ₀ * L.h / L.ν ≤ 1 / 5)
    (hlegal : ∀ᵐ z ∂η.prod (Measure.pi (fun _ : Fin R => ρ)),
      P.LegalEvent (liftedRectOracle g L) R R z) :
    ENNReal.ofReal ((5 / 3 : ℝ) * ε) * (1 - (R : ℝ≥0∞) * ENNReal.ofReal p / T) ≤
      ∫⁻ z, ENNReal.ofReal ‖canonicalLiftGradPhi C L
        (MeasuredOracle.trace P (liftedRectOracle g L) R z).output‖
        ∂η.prod (Measure.pi (fun _ : Fin R => ρ)) ∧
    ENNReal.ofReal ((25 / 9 : ℝ) * ε ^ 2) * (1 - (R : ℝ≥0∞) * ENNReal.ofReal p / T) ≤
      ∫⁻ z, ENNReal.ofReal (‖canonicalLiftGradPhi C L
        (MeasuredOracle.trace P (liftedRectOracle g L) R z).output‖ ^ 2)
        ∂η.prod (Measure.pi (fun _ : Fin R => ρ)) := by
  have hb : ∀ x : Vec T, prog 0 x < T → prog 1 ((L.β * L.γ) • x) < T := by
    intro x hx
    exact lt_of_le_of_lt ((prog_threshold_le_zero 1 (by norm_num) _).trans
      (prog_zero_smul_le _ x)) hx
  constructor
  · apply native_lifted_risk_lower η ρ P g p h L C.dim_pos hlegal
    exact Filter.Eventually.of_forall fun z hz => ENNReal.ofReal_le_ofReal
      (le_of_lt (proposition24_pathwise_stationarity C B L
        (canonicalLiftPropertiesCertificate C B L) ε hε hγq hratio _ (hb _ hz)))
  · apply native_lifted_risk_lower η ρ P g p h L C.dim_pos hlegal
    exact Filter.Eventually.of_forall fun z hz => ENNReal.ofReal_le_ofReal
      (le_of_lt (proposition24_pathwise_stationarity_sq C B L
        (canonicalLiftPropertiesCertificate C B L) ε hε hγq hratio _ (hb _ hz)))

end NCSCPureStochasticLB.PaperExact.GeneralProgress
