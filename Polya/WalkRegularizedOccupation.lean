module

public import Polya.Defs

public section

open MeasureTheory ENNReal

variable {d : ℕ} {Ω : Type*}

lemma walkRegularizedOccupation_eq (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    walkRegularizedOccupation walk r x = ∑' t, Set.indicator {x} (fun _ ↦ r ^ t) (walk t) :=
  rfl

/-- Regularized occupation of a walk at any point is an increasing (more precisely nondecreasing) function of the regularization parameter `r`. -/
lemma walkRegularizedOccupation_apply_mono (walk : (t : ℕ) → Grid d) (x : Grid d) :
    Monotone (fun r ↦ walkRegularizedOccupation walk r x) := by
  intro a b h
  apply Summable.tsum_mono ENNReal.summable ENNReal.summable
  · rw [Pi.le_def]
    intro i
    exact Set.indicator_le_indicator (ENNReal.pow_le_pow_left (n := i) h)

/-- Regularized occupation of a walk is an increasing (more precisely nondecreasing) function of the regularization parameter `r`. -/
lemma walkRegularizedOccupation_mono (walk : (t : ℕ) → Grid d) :
    Monotone (fun r ↦ walkRegularizedOccupation walk r) := by
  intro a b h
  rw [Pi.le_def]
  intro i
  apply walkRegularizedOccupation_apply_mono _ _ h

lemma indicator_le {x : Grid d} {f : ℝ≥0∞ → ℕ → ℝ≥0∞} {r : ℝ≥0∞} {a : ℕ}
    (walk : (t : ℕ) → Grid d) :
    Set.indicator {x} (fun _ ↦ f r a) (walk a) ≤ f r a := by
  apply Set.indicator_apply_le'
  · intro h
    rfl
  · intro h
    exact zero_le

/-- Regularized occupation of any walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma walkRegularizedOccupation_le {walk : (t : ℕ) → Grid d} {r : ℝ≥0∞} {x : Grid d} :
    walkRegularizedOccupation walk r x ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric]
  apply ENNReal.tsum_le_tsum
  intro a
  apply indicator_le

/-- Regularized occupation of any walk with regularization `r` is less than `∞`. -/
lemma walkRegularizedOccupation_lt_top {r : ℝ≥0∞}
    (walk : (t : ℕ) → Grid d) (r_lt_one : r < 1) (x : Grid d) :
    walkRegularizedOccupation walk r x < ∞ := by
  apply lt_of_le_of_lt (walkRegularizedOccupation_le)
  simp only [inv_lt_top, tsub_pos_iff_lt, r_lt_one]

lemma tsum_indicator_singleton_eq {S : Type*} {R : Type*} [AddCommMonoid R] [TopologicalSpace R]
    (y : S) (c : R) :
    ∑' i, Set.indicator {i} (fun _ ↦ c) y = c := by
  classical
  rw [tsum_eq_single y]
  · simp
  · intro b hb
    simp [hb]

lemma tsum_indicator_value_eq {ω : Ω} {S : Type*} {R : Type*} [AddCommMonoid R] [TopologicalSpace R]
    (Y : Ω → S) (c : R) :
    ∑' i, Set.indicator (Y ⁻¹' {i}) (fun _ ↦ c) ω = c := by
  exact tsum_indicator_singleton_eq _ _

lemma tsum_indicator_walk_position_eq {R : Type*} [AddCommMonoid R] [TopologicalSpace R]
    (X : (t : ℕ) → Ω → Grid d) (c : R) :
    ∑' x, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ c) ω = c := by
  exact tsum_indicator_value_eq _ _

lemma tsum_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) :
    ∑' x, walkRegularizedOccupation walk r x = ∑' (t : ℕ), r ^ t := by
  simp_rw [walkRegularizedOccupation_eq]
  rw [ENNReal.tsum_comm]
  simp_rw [tsum_indicator_singleton_eq]

open NNReal

lemma tsum_toReal_walkRegularizedOccupation_eq_geom_series {r : ℝ≥0}
    (walk : (t : ℕ) → Grid d) (r_lt_one : r < 1) :
    ∑' x, (walkRegularizedOccupation walk r x).toReal = (∑' (t : ℕ), r.toReal ^ t):= by
  rw [← ENNReal.tsum_toReal_eq, tsum_walkRegularizedOccupation_eq_geom_series]
  · apply ENNReal.tsum_toReal_eq
    simp
  · intro a
    apply ne_of_lt
    apply walkRegularizedOccupation_lt_top
    simp [r_lt_one]
