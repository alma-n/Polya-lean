module

public import Polya.WalkRegularizedOccupation

public section

open MeasureTheory Topology Filter ENNReal BigOperators

variable {d : ℕ} {Ω : Type*}

/-- A rewrite lemma for the regularized occupation `L_λ` of a random walk. -/
lemma regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x = fun ω ↦ ∑' t, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ r ^ t) ω :=
  rfl

lemma summable_regularizedOccupation (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) :
    Summable (regularizedOccupation X r) := by
  rw [Pi.summable]
  intro ω
  exact ENNReal.summable

/-- Regularized occupation of a random walk at any point is increasing
(more precisely nondecreasing) in the regularization parameter `r`. -/
lemma regularizedOccupation_apply_mono (X : (t : ℕ) → Ω → Grid d) (x : Grid d) :
    Monotone (fun r ↦ regularizedOccupation X r x) := by
  intro _ _ h ω
  exact walkRegularizedOccupation_apply_mono _ _ h

/-- Regularized occupation of a random walk is increasing (more precisely nondecreasing) in the
regularization parameter `r`. -/
lemma regularizedOccupation_mono (X : (t : ℕ) → Ω → Grid d) :
    Monotone (fun r ↦ regularizedOccupation X r) := by
  intro a b h
  rw [Pi.le_def]
  intro x
  exact regularizedOccupation_apply_mono _ _ h


/-- Regularized occupation of a random walk at any point is left continuous in the regularization
parameter `r`. -/
lemma regularizedOccupation_apply_tendsto_of_monotone {rs : ℕ → ℝ≥0∞} {r : ℝ≥0∞}
    (X : (t : ℕ) → Ω → Grid d) (rs_incr : Monotone rs) (rs_lim : Tendsto rs atTop (𝓝[<] r))
    (x : Grid d) (ω : Ω) :
    Tendsto (fun n ↦ regularizedOccupation X (rs n) x ω) atTop
      (𝓝 (regularizedOccupation X r x ω)) := by
  simp_rw [regularizedOccupation_eq, ← lintegral_count]
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact AEMeasurable.of_discrete
  · apply Eventually.of_forall
    intro n a b h
    apply Set.indicator_le_indicator
    exact ENNReal.pow_le_pow_left (rs_incr h)
  · apply Eventually.of_forall
    intro n s h
    simp_rw [Set.indicator] at *
    split_ifs
    next ho =>
      rw [tendsto_nhdsWithin_iff] at rs_lim
      have := (Continuous.tendsto (ENNReal.continuous_pow n) r).comp rs_lim.1
      simp only [ho, ite_true] at h
      exact this h
    next ho =>
      simp only [ho, mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage, ite_false] at h ⊢
      use 0
      intro b hb
      exact mem_of_mem_nhds h

/-- Regularized occupation of any random walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma regularizedOccupation_le (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x ≤ fun _ ↦ (1 - r)⁻¹ := by
  rw [← tsum_geometric, Pi.le_def]
  intro ω
  apply ENNReal.tsum_le_tsum
  intro n
  apply indicator_le

-- A random walk is always somewhere, so it is easy to calculate the sum over positions
-- of the regularized occupations at those positions.
lemma tsum_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) :
    ∑' x, regularizedOccupation X r x = fun _ ↦ (∑' (t : ℕ), r ^ t):= by
  ext ω
  rw [← tsum_walkRegularizedOccupation_eq_geom_series (X · ω)]
  apply tsum_apply
  exact summable_regularizedOccupation _ _

open NNReal

lemma tsum_toReal_regularizedOccupation_eq_geom_series {r : ℝ≥0}
    (X : (t : ℕ) → Ω → Grid d) (r_lt_one : r < 1) (ω : Ω) :
    ∑' x, (regularizedOccupation X r x ω).toReal = ∑' (t : ℕ), r.toReal ^ t := by
  rw [← tsum_toReal_walkRegularizedOccupation_eq_geom_series (X · ω) r_lt_one]
  rfl

lemma tsum_toReal_regularizedOccupation_eq {r : ℝ≥0}
    (X : (t : ℕ) → Ω → Grid d) (r_lt_one : r < 1) (ω : Ω) :
    ∑' x, (regularizedOccupation X r x ω).toReal = (1 - r)⁻¹ := by
  rw [← NNReal.tsum_geometric r_lt_one, tsum_toReal_regularizedOccupation_eq_geom_series _ r_lt_one]
  norm_cast

lemma regularizedOccupation_lt {r : ℝ≥0∞}
    (X : (t : ℕ) → Ω → Grid d) (r_lt_one : r < 1) (x : Grid d) (ω : Ω) :
    regularizedOccupation X r x ω < ⊤ := by
  have := regularizedOccupation_le X r x
  rw [Pi.le_def] at this
  grw [this]
  simp [r_lt_one]

lemma regularizedOccupation_toReal_eq {x : Grid d} {r : ℝ≥0∞}
    (X : (t : ℕ) → Ω → Grid d) (r_lt_one : r < 1) :
    ∀ ω, regularizedOccupation X r x ω = ENNReal.ofReal (regularizedOccupation X r x ω).toReal := by
  intro ω
  have := regularizedOccupation_lt X r_lt_one x ω
  exact (toReal_eq_toReal_iff' (ne_of_lt this) (by simp)).mp (by simp)

variable [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The regularized occupation of a random walk is a random variable (measurable). -/
lemma regularizedOccupation.measurable {X : (t : ℕ) → Ω → Grid d}
    (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) (x : Grid d) :
    Measurable (regularizedOccupation X r x) := by
  apply Measurable.tsum
  intro i
  apply Measurable.ite _ measurable_const measurable_const
  · exact measurableSet_eq_fun (X_mble i) measurable_const

/-- The regularized occupation of a random walk is integrable. -/
lemma regularizedOccupation_integrable {r : ℝ≥0∞} {X : (t : ℕ) → Ω → Grid d}
    (X_mble : ∀ t, Measurable (X t)) (r_lt_one : r < 1) (x : Grid d) :
    Integrable (fun ω => (regularizedOccupation X r x ω).toReal) P := by
  have : Integrable (fun (ω : Ω) ↦ ENNReal.toReal ((1 - r)⁻¹)) P := by
    rw [integrable_const_iff]
    right
    infer_instance
  apply MeasureTheory.Integrable.mono' this
  · apply Measurable.aestronglyMeasurable
    exact Measurable.ennreal_toReal (regularizedOccupation.measurable X_mble r x)
  · apply Eventually.of_forall
    intro ω
    rw [regularizedOccupation]
    simp only [Real.norm_eq_abs, abs_toReal, toReal_inv]
    suffices (∑' (t : ℕ), (X t ⁻¹' {x}).indicator (fun x ↦ r ^ t) ω).toReal ≤ ((1 - r)⁻¹).toReal by
      apply le_trans this
      simp
    rw [← ENNReal.tsum_geometric r, ENNReal.toReal_le_toReal]
    · apply ENNReal.tsum_le_tsum
      intro a
      apply indicator_le
    · suffices ∑' (t : ℕ), (X t ⁻¹' {x}).indicator (fun x ↦ r ^ t) ω ≤ (1 - r)⁻¹ by
        rw [← ENNReal.tsum_geometric] at this
        apply ne_of_lt
        apply lt_of_le_of_lt this
        simp only [ENNReal.tsum_geometric, inv_lt_top, tsub_pos_iff_lt]
        exact r_lt_one
      rw [← ENNReal.tsum_geometric]
      apply ENNReal.tsum_le_tsum
      intro a
      apply indicator_le
    · rw [ENNReal.tsum_geometric, ne_eq, inv_eq_top, ← ne_eq]
      exact ne_of_gt (tsub_pos_iff_lt.mpr r_lt_one)

/-- The sum over points of the expected value of the regularized occupation is a geometric series
with the ratio given by the regularization. -/
lemma tsum_lintegral_norm_regularizedOccupation_eq_geom_series {X : (t : ℕ) → Ω → Grid d}
    (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (∑' (t : ℕ), r ^ t):= by
  rw [← lintegral_tsum]
  · have (ω : Ω) := ENNReal.tsum_apply ▸ congrFun (tsum_regularizedOccupation_eq_geom_series X r) ω
    simp [this]
  · intro n
    apply Measurable.aemeasurable
    exact regularizedOccupation.measurable X_mble r n

/-- The sum over points of the expected value of the regularized occupation is just `(1-r)⁻¹`. -/
lemma tsum_lintegral_regularizedOccupation_eq {X : (t : ℕ) → Ω → Grid d}
    (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (1 - r)⁻¹ := by
  rw [tsum_lintegral_norm_regularizedOccupation_eq_geom_series _ X_mble, ENNReal.tsum_geometric]

lemma abs_toReal_coe_eq {x : ℝ≥0∞} (hx : x < ⊤) : (‖x.toReal‖.toNNReal : ℝ≥0∞) = x := by
  simp_rw [ENNReal.ofNNReal_toNNReal, Real.norm_eq_abs]
  rw [abs_of_nonneg toReal_nonneg]
  apply ne_of_lt at hx
  exact ofReal_toReal_eq_iff.mpr hx

/-- The sum over points of the expected norms of the regularized occupation is at most `(1-r)⁻¹`. -/
lemma tsum_lintegral_norm_regularizedOccupation_le {X : (t : ℕ) → Ω → Grid d}
    (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, ‖(regularizedOccupation X r x ω).toReal‖.toNNReal ∂P ≤ (1 - r)⁻¹ := by
  by_cases hr : r < 1
  · have (x) (ω) := abs_toReal_coe_eq (regularizedOccupation_lt X hr x ω)
    simp_rw [this]
    rw [tsum_lintegral_regularizedOccupation_eq _ X_mble]
  · have : (1-r)⁻¹ = ⊤ := by
      apply inv_eq_top.mpr
      rw [tsub_eq_zero_of_le]
      exact not_lt.mp hr
    rw [this]
    exact le_top
