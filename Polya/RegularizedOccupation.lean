module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
import Polya.TendstoOfSMSTendsto

set_option linter.style.longLine false

@[expose]
public section

open MeasureTheory Topology Filter ENNReal BigOperators

section Grid

-- The integer grid in `d` dimensions. -/
abbrev Grid d := Fin d → ℤ
-- Should be def deriving MeasurableSpace, AddCommMonoid, ...

-- The integer grid in `d` dimensions is countable. -/
lemma Grid.countable (d : ℕ) : Countable (Grid d) := by
  exact instCountableForallOfFinite

end Grid

section WalkOfSteps

variable {d : ℕ}

-- Walk on the grid with a given step sequence `steps`. -/
def walkOfSteps (steps : (t : ℕ) → Grid d) (t : ℕ) : Grid d :=
  ∑ s ∈ Finset.range t, steps s

end WalkOfSteps

section RandomWalkOfSteps

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

-- Random walk with a given random step sequence `ξ`. -/
-- At time `t`, the random walk `RW ξ t` is a random variable (`Ω →`) of `Grid d`.
-- TODO: Ask Kalle: By exchanging t and ω we see that `RW ξ` is a random variable of `ℕ → Grid d`, why is the definition the other way around?
def RW (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) : Grid d :=
  walkOfSteps (fun s ↦ ξ s ω) t

-- Another equivalent definition with non-fixed `ξ`, `t` and `ω` -/
def RW_def : RW = fun (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) ↦ walkOfSteps (fun s ↦ ξ s ω) t := by rfl

-- The position of a random walk is a random variable (measurable) if the steps are random
-- variables (measurable).

lemma RW.measurable {ξ : (t : ℕ) → Ω → Grid d} (ξ_mble : ∀ t, Measurable (ξ t)) (t : ℕ) :
    Measurable (RW ξ t) := by
-- Doable with `measurable_const` and `Finset.sum_range_succ` and `Measurable.add`.
-- Note: `measurable_add` is not so convenient here! (It is more general, though.)
  have ξ_mble_t := ξ_mble t
  induction t with
  | zero => exact measurable_const
  | succ n ih =>
    specialize ih (ξ_mble n)
    simp_rw [RW_def, walkOfSteps, Finset.sum_range_succ]
    simp_rw [RW_def, walkOfSteps] at ih
    exact Measurable.add ih (ξ_mble n)

def RW2 (ξ : (t : ℕ) → Ω → Grid d) (ω : Ω) (t : ℕ) : Grid d :=
  walkOfSteps (fun s ↦ ξ s ω) t

lemma RW2.measurable {ξ : (t : ℕ) → Ω → Grid d} (ξ_mble : ∀ t, Measurable (ξ t)) :
    Measurable (RW2 ξ) := by
  unfold RW2
  rw [measurable_pi_iff]
  intro t
  rw [measurable_pi_iff]
  intro x
  have ξ_mble_t := ξ_mble t
  induction t with
  | zero => exact measurable_const
  | succ n ih =>
    specialize ih (ξ_mble n)
    simp_rw [walkOfSteps, Finset.sum_range_succ]
    simp_rw [walkOfSteps] at ih
    apply Measurable.add ih
    · specialize ξ_mble n
      rw [measurable_pi_iff] at ξ_mble
      apply ξ_mble

end RandomWalkOfSteps

noncomputable section RegularizedOccupation

variable {Ω : Type*}
variable {d : ℕ}

-- Regularized occupation of a given walk.
def walkRegularizedOccupation (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) := ∑' t, Set.indicator {x} (fun _ ↦ r ^ t) (walk t)

lemma walkRegularizedOccupation_eq (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) : walkRegularizedOccupation walk r x = ∑' t, Set.indicator {x} (fun _ ↦ r ^ t) (walk t) := rfl

-- Regularized occupation of a walk at any point is an increasing (more precisely nondecreasing)
-- function of the regularization parameter `r`.
lemma walkRegularizedOccupation_apply_mono (walk : (t : ℕ) → Grid d) (x : Grid d) : Monotone (fun r ↦ walkRegularizedOccupation walk r x) := by
  intro a b h
  apply Summable.tsum_mono ENNReal.summable ENNReal.summable
  · rw [Pi.le_def]
    intro i
    apply Set.indicator_le_indicator
    exact ENNReal.pow_le_pow_left h

-- Regularized occupation of a walk is an increasing (more precisely nondecreasing) function
-- of the regularization parameter `r`.
lemma walkRegularizedOccupation_mono (walk : (t : ℕ) → Grid d) : Monotone (fun r ↦ walkRegularizedOccupation walk r) := by
  intro a b h
  rw [Pi.le_def]
  intro i
  apply walkRegularizedOccupation_apply_mono _ _ h

-- Regularized occupation of any walk with regularization `r` is at most `(1-r)⁻¹`.
lemma indicator_le {x : Grid d} {f : ℝ≥0∞ → ℕ → ℝ≥0∞} {r : ℝ≥0∞} {a : ℕ} (walk : (t : ℕ) → Grid d) : Set.indicator {x} (fun _ ↦ f r a) (walk a) ≤ f r a := by
  apply Set.indicator_apply_le'
  · intro h
    rfl
  · intro h
    exact zero_le

lemma walkRegularizedOccupation_le {walk : (t : ℕ) → Grid d} {r : ℝ≥0∞} {x : Grid d} : walkRegularizedOccupation walk r x ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric]
  apply ENNReal.tsum_le_tsum
  intro a
  apply indicator_le

-- Remark by Kalle: It is "funny" (and convenient) that here we do not need to assume `r<1`,
-- which is usually needed for the convergence of the geometric series. That is because in `ℝ≥0∞`
-- we have `1/∞ = 0` according to Lean's (or rather Mathlib's) definition.

-- Regularized occupation `L_λ` of a random walk. -/
def regularizedOccupation (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) (ω : Ω) := walkRegularizedOccupation (fun t ↦ X t ω) r x

-- A rewrite lemma for the regularized occupation `L_λ` of a random walk. -/
lemma regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) : regularizedOccupation X r x = fun ω ↦ ∑' t, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ r ^ t) ω := rfl

lemma summable_regularizedOccupation (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) : Summable (regularizedOccupation X r) := by
  rw [Pi.summable]
  intro ω
  exact ENNReal.summable

-- Regularized occupation of a random walk at any point is increasing (more precisely nondecreasing)
-- in the regularization parameter `r`.
lemma regularizedOccupation_apply_mono (X : (t : ℕ) → Ω → Grid d) (x : Grid d) :
  Monotone (fun r ↦ regularizedOccupation X r x) := by
  intro _ _ h ω
  exact walkRegularizedOccupation_apply_mono _ _ h

-- Regularized occupation of a random walk is increasing (more precisely nondecreasing) in the
-- regularization parameter `r`.
lemma regularizedOccupation_mono (X : (t : ℕ) → Ω → Grid d) :
  Monotone (fun r ↦ regularizedOccupation X r) := by
  intro a b h
  rw [Pi.le_def]
  intro x
  exact regularizedOccupation_apply_mono _ _ h

-- Regularized occupation of a random walk at any point is left continuous in the
-- regularization parameter `r`.

lemma regularizedOccupation_apply_tendsto_of_monotone (X : (t : ℕ) → Ω → Grid d)
    {rs : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (rs_incr : Monotone rs) (rs_lim : Tendsto rs atTop (𝓝[<] r)) (x : Grid d) (ω : Ω) :
  Tendsto (fun n ↦ regularizedOccupation X (rs n) x ω) atTop (𝓝 (regularizedOccupation X r x ω)) := by
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

-- This can almost be proven with the Monotone Convergence Theorem
-- `lintegral_tendsto_of_tendsto_of_monotone`, once one writes the infinite sum as an integral
-- with respect to counting measure using `lintegral_count`.
-- One also needs `tendsto_pi_nhds` (characterization of pointwise convergence).
-- Later we might want to generalize this, since the monotonicity hypothesis is
-- in fact unnecessary (but getting rid of it requires some filter stuff).

-- Regularized occupation of any random walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma regularizedOccupation_le (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x ≤ fun _ ↦ (1 - r)⁻¹ := by
  rw [← tsum_geometric, Pi.le_def]
  intro ω
  apply ENNReal.tsum_le_tsum
  intro n
  apply indicator_le

lemma walkRegularizedOccupation_lt_top (walk : (t : ℕ) → Grid d)
    {r : ℝ≥0∞} (r_lt_one : r < 1) (x : Grid d) :
    walkRegularizedOccupation walk r x < ∞ := by
  apply lt_of_le_of_lt (walkRegularizedOccupation_le)
  simp only [inv_lt_top, tsub_pos_iff_lt, r_lt_one]

lemma tsum_indicator_singleton_eq {S : Type*}
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (y : S) (c : R) :
    ∑' i, Set.indicator {i} (fun _ ↦ c) y = c := by
  classical
  rw [tsum_eq_single y]
  · simp
  · intro b hb
    simp [hb]

-- A random variable always has some value, so it is easy to calculate the sum over possible values of the indicators of having that value. -/
lemma tsum_indicator_value_eq {S : Type*}
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (Y : Ω → S) (c : R) :
    ∑' i, Set.indicator (Y ⁻¹' {i}) (fun _ ↦ c) ω = c := by
  exact tsum_indicator_singleton_eq _ _

lemma tsum_indicator_walk_position_eq (X : (t : ℕ) → Ω → Grid d)
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (c : R) :
    ∑' x, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ c) ω = c := by
  exact tsum_indicator_value_eq _ _

-- A walk is always somewhere, so it is easy to calculate the sum over positions
-- of the regularized occupations at those positions.
lemma tsum_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) :
    ∑' x, walkRegularizedOccupation walk r x = ∑' (t : ℕ), r ^ t := by
  simp_rw [walkRegularizedOccupation_eq]
  rw [ENNReal.tsum_comm]
  simp_rw [tsum_indicator_singleton_eq]

-- A random walk is always somewhere, so it is easy to calculate the sum over positions
-- of the regularized occupations at those positions.
lemma tsum_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) :
    ∑' x, regularizedOccupation X r x = fun _ ↦ (∑' (t : ℕ), r ^ t):= by
  ext ω
  rw [← tsum_walkRegularizedOccupation_eq_geom_series (X · ω)]
  apply tsum_apply
  exact summable_regularizedOccupation _ _

section

open NNReal
-- A walk is always somewhere, so it is easy to calculate the sum over positions
-- of the regularized occupations at those positions.
lemma tsum_toReal_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) :
    ∑' x, (walkRegularizedOccupation walk r x).toReal = (∑' (t : ℕ), r.toReal ^ t):= by
  rw [← ENNReal.tsum_toReal_eq, tsum_walkRegularizedOccupation_eq_geom_series]
  · apply ENNReal.tsum_toReal_eq
    simp
  · intro a
    apply ne_of_lt
    apply walkRegularizedOccupation_lt_top
    simp [r_lt_one]

-- A random walk is always somewhere, so it is easy to calculate the sum over positions of the regularized occupations at those positions.
lemma tsum_toReal_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d) {r : ℝ≥0} (r_lt_one : r < 1) (ω : Ω) : ∑' x, (regularizedOccupation X r x ω).toReal = ∑' (t : ℕ), r.toReal ^ t := by
  rw [← tsum_toReal_walkRegularizedOccupation_eq_geom_series (X · ω) r_lt_one]
  rfl

-- A random walk is always somewhere, so it is easy to calculate the sum over positions
-- of the regularized occupations at those positions. When `r < 1`, the infinite sums are
-- convergent and the calculation yields an equality in `ℝ`.
lemma tsum_toReal_regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d) {r : ℝ≥0} (r_lt_one : r < 1) (ω : Ω) : ∑' x, (regularizedOccupation X r x ω).toReal = (1 - r)⁻¹ := by
  rw [← NNReal.tsum_geometric r_lt_one, tsum_toReal_regularizedOccupation_eq_geom_series _ r_lt_one]
  norm_cast

lemma regularizedOccupation_lt (X : (t : ℕ) → Ω → Grid d) {r : ℝ≥0∞} (r_lt_one : r < 1) (x : Grid d) (ω : Ω) : regularizedOccupation X r x ω < ⊤ := by
  have := regularizedOccupation_le X r x
  rw [Pi.le_def] at this
  grw [this]
  simp [r_lt_one]

lemma regularizedOccupation_toReal_eq
    (X : (t : ℕ) → Ω → Grid d) {x : Grid d} {r : ℝ≥0∞} (r_lt_one : r < 1) :
      ∀ ω, regularizedOccupation X r x ω = ENNReal.ofReal (regularizedOccupation X r x ω).toReal := by
  intro ω
  have := regularizedOccupation_lt X r_lt_one x ω
  exact (toReal_eq_toReal_iff' (ne_of_lt this) (by simp)).mp (by simp)

section

section

variable [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

-- The regularized occupation of a random walk is a random variable (measurable).
lemma regularizedOccupation.measurable
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) (x : Grid d) :
    Measurable (regularizedOccupation X r x) := by
  apply Measurable.tsum
  intro i
  apply Measurable.ite _ measurable_const measurable_const
  · exact measurableSet_eq_fun (X_mble i) measurable_const

lemma regularizedOccupation_integrable
  {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r_lt_one : r < 1) (x : Grid d) :
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

end

variable [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

-- The sum over points of the expected value of the regularized occupation is a
-- geometric series with the ratio given by the regularization.
lemma tsum_lintegral_norm_regularizedOccupation_eq_geom_series
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (∑' (t : ℕ), r ^ t):= by
  rw [← lintegral_tsum]
  · have (ω : Ω) := ENNReal.tsum_apply ▸ congrFun (tsum_regularizedOccupation_eq_geom_series X r) ω
    simp [this]
  · intro n
    apply Measurable.aemeasurable
    exact regularizedOccupation.measurable X_mble r n

-- The sum over points of the expected value of the regularized occupation is just `(1-r)⁻¹`. -/
lemma tsum_lintegral_regularizedOccupation_eq
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (1 - r)⁻¹ := by
  rw [tsum_lintegral_norm_regularizedOccupation_eq_geom_series _ X_mble, ENNReal.tsum_geometric]

lemma abs_toReal_coe_eq (hx : x < ⊤) : (‖x.toReal‖.toNNReal : ℝ≥0∞) = x := by
  simp_rw [ENNReal.ofNNReal_toNNReal, Real.norm_eq_abs]
  rw [abs_of_nonneg toReal_nonneg]
  apply ne_of_lt at hx
  exact ofReal_toReal_eq_iff.mpr hx

-- The sum over points of the expected norms of the regularized occupation is at most `(1-r)⁻¹`. -/
lemma tsum_lintegral_norm_regularizedOccupation_le
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
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

end

end

end RegularizedOccupation

noncomputable section RegularizedGreensFunction

open NNReal

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
variable {d : ℕ}

-- The regularized Green's function `G_λ(x)` of a random walk. -/
def regularizedG (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) : ℝ :=
  ∫ ω, ENNReal.toReal (regularizedOccupation X r x ω) ∂P

lemma regularizedG_eq : regularizedG P X r x = ∫ ω, ENNReal.toReal (regularizedOccupation X r x ω) ∂P := rfl

variable [IsProbabilityMeasure P]

lemma enorm_toReal_eq_coe_norm_toNNReal {a : ℝ≥0∞} :
    ‖(a).toReal‖ₑ = ‖(a).toReal‖.toNNReal := by
  rw [Real.enorm_of_nonneg]
  · simp only [Real.norm_eq_abs, abs_toReal, toNNReal_toReal_eq]
    apply ENNReal.ofReal_eq_coe_nnreal
  · simp

lemma tsum_regularizedG_eq_lintegral_tsum {X : (t : ℕ) → Ω → Grid d}
    {r : ℝ≥0}
    (r_lt_one : r < 1)
    (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x
      = (∫ ω, ∑' x, ∑' t,
    Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ (r : ℝ) ^ t) ω ∂P) := by
  simp_rw [regularizedG_eq]
  rw [← integral_tsum]
  · congr
    ext ω
    congr
    ext x
    rw [regularizedOccupation_eq]
    simp only
    rw [ENNReal.tsum_toReal_eq]
    · congr
      ext n
      norm_cast
    · intro n
      norm_cast
      exact coe_ne_top
  · intro i
    apply Measurable.aestronglyMeasurable
    apply Measurable.ennreal_toReal
    apply regularizedOccupation.measurable X_mble
  · simp_rw [enorm_toReal_eq_coe_norm_toNNReal]
    apply ne_of_lt
    apply lt_of_le_of_lt (tsum_lintegral_norm_regularizedOccupation_le P X_mble r)
    simp [r_lt_one]

section

open SummationFilter

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
theorem hasProd_ite_eq' (b : β) [DecidablePred (b = ·)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' ↦ if b = b' then a else 1) a L := by
  convert hasProd_single b (hf := fun b' hb' ↦ if_neg hb'.symm) (L := L)
  exact (if_pos rfl).symm

@[to_additive (attr := simp)]
theorem tprod_ite_eq' (b : β) [DecidablePred (b = ·)] (a : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b = b' then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

end

-- A summability criterion for a slightly generalized version of walk occupations. -/
lemma summable_weighted_occupation {walk : (t : ℕ) → Grid d}
    {g : ℕ → ℝ} (g_abssummable : ∑' t, ENNReal.ofReal |g t| ≠ ∞) :
    Summable (Function.uncurry fun (t : ℕ) (x : Grid d) ↦ Set.indicator {x} (fun _↦ g t) (walk t)) := by
  classical
  apply ENNReal.tsum_coe_ne_top_iff_summable.mp at g_abssummable
  apply Summable.of_abs
  rw [summable_prod_of_nonneg]
  · simp only [Function.uncurry_apply_pair]
    · constructor
      · intro t
        simp_rw [Set.indicator_apply, Set.mem_singleton_iff, abs_ite, abs_zero]
        use |g t|
        apply hasSum_ite_eq'
      · have (x : ℕ) : ∑' (y : Grid d), |Set.indicator {y} (fun x_1 ↦ g x) (walk x)| = |g x| := by
          unfold Set.indicator
          simp_rw [abs_ite, abs_zero, Set.mem_singleton_iff, tsum_ite_eq']
        simp_rw [this]
        apply NNReal.summable_coe.mpr at g_abssummable
        simp only [Real.toNNReal_abs, Real.coe_nnabs] at g_abssummable
        exact g_abssummable
  · intro ⟨t, x⟩
    simp only [Function.uncurry_apply_pair, Pi.zero_apply, Set.indicator_singleton, abs_nonneg]

-- Kalle says: Probably the cleanest way to do this would be to generalize this further.
-- But for now, this seems ok. If you like, thinking about the right generalization can
-- nevertheless be very useful!
-- At least the general helper lemma `summable_of_abs_le_of_tsum_ne_top` can be used here.
-- The earlier tricks (Fubini variants and juggling between sums and integrals w.r.t
-- counting measures) can also come in handy.

-- A summability criterion for (basically) regularized walk occupations. -/
lemma summable_regularized_occupation {walk : (t : ℕ) → Grid d} {r : ℝ≥0} (r_lt_one : r < 1) :
    Summable (Function.uncurry fun (t : ℕ) (x : Grid d) ↦ Set.indicator {x} (fun _ ↦ (r : ℝ) ^ t) (walk t)) := by
-- The idea is to get this from the slightly generalized version `summable_weighted_occupation`.
  apply summable_weighted_occupation
  simp only [abs_pow, NNReal.abs_eq, zero_le_coe, ofReal_pow, ofReal_coe_nnreal, ENNReal.tsum_geometric, ne_eq, inv_eq_top]
  exact_mod_cast by simpa [NNReal.sub_def]

lemma tsum_regularizedG_eq {X : (t : ℕ) → Ω → Grid d}
    {r : ℝ≥0} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x = (1 - r)⁻¹ := by
-- Tada! The first line of equalities of the main proof will be completed here!
  simp_rw [regularizedG_eq]
  rw [← integral_tsum]
  · have := tsum_toReal_regularizedOccupation_eq X r_lt_one
    simp_rw [this]
    simp
  · intro x
    apply Measurable.aestronglyMeasurable
    exact (regularizedOccupation.measurable X_mble r x).ennreal_toReal
  · simp_rw [enorm_toReal_eq_coe_norm_toNNReal]
    apply ne_of_lt
    apply lt_of_le_of_lt (tsum_lintegral_norm_regularizedOccupation_le P X_mble _)
    simp [r_lt_one]

#check lintegral_tendsto_of_tendsto_of_monotone

lemma lt_of_strict_mono_tendsto
    {xs : ℕ → ℝ≥0∞} (hx : 0 < x) (hx1 : StrictMono xs) (hx2 : Tendsto xs atTop (𝓝 x)) :
  ∀ n, xs n < x := by
    intro n
    by_contra hf
    have strm := hx1
    unfold StrictMono at hx1
    rw [tendsto_atTop'] at hx2
    have := lt_of_le_of_lt (not_lt.mp hf) (hx1 (a := n) (b := n + 1) (by norm_num))
    have ⟨a, ha⟩ := hx2 (Set.Ico 0 (xs (n + 1))) (?_)
    by_cases h : a ≤ (n + 1)
    · specialize ha (n + 1) h
      simp at ha
    · specialize ha a (by norm_num)
      have := hx1 (a := n + 1) (b := a) (by grind)
      simp at ha
      exact (lt_self_iff_false _).mp (lt_trans this ha)
    · rw [mem_nhds_iff]
      refine ⟨Set.Ioo 0 (xs (n + 1)), Set.Ioo_subset_Ico_self, isOpen_Ioo, ⟨hx, this⟩
⟩

lemma regularizedG_tendsto (X_mble : ∀ t, Measurable (X t)) :
    Tendsto (fun r ↦ ENNReal.ofReal (regularizedG P X r 0)) (𝓝[<] 1) (𝓝 (∫⁻ ω,(regularizedOccupation (d := d) X 1 0 ω) ∂P)) := by
  apply tendsto_of_strictMono_seq_tendsto
  intro rs hr1 hr2
  simp_rw [regularizedG_eq]
  have (r : ℝ≥0∞) (hr : r < 1) : ENNReal.ofReal (∫ (ω : Ω), (regularizedOccupation X r 0 ω).toReal ∂P) = (∫⁻ (ω : Ω), (regularizedOccupation X r 0 ω) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · congr
      ext ω
      exact ofReal_toReal_eq_iff.mpr (ne_of_lt (regularizedOccupation_lt _ hr _ _))
    · exact regularizedOccupation_integrable P X_mble hr _
    · apply Eventually.of_forall
      simp
  have rs_lt_one := lt_of_strict_mono_tendsto (x := 1) (xs := rs) (by norm_num) hr1 hr2
  change Tendsto (fun n ↦ ENNReal.ofReal (∫ (ω : Ω), (regularizedOccupation X (rs n) 0 ω).toReal ∂P)) _ _
  simp_rw [this _ (rs_lt_one _)]
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact Measurable.aemeasurable (regularizedOccupation.measurable X_mble (rs n) 0)
  · apply Eventually.of_forall
    intro x a b hab
    apply regularizedOccupation_apply_mono
    exact StrictMono.monotone hr1 hab
  · apply Eventually.of_forall
    intro ω
    have rs_tendsto_lt : Tendsto rs atTop (𝓝[<] 1) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · exact hr2
      · apply Eventually.of_forall
        intro n
        exact Set.mem_Iio.mpr (rs_lt_one n)
    apply regularizedOccupation_apply_tendsto_of_monotone X (StrictMono.monotone hr1) rs_tendsto_lt 0


-- TODO make this less ugly (these should probably be in the GreenFourier file)
lemma regularizedG_summable (X : (t : ℕ) → Ω → Grid d) {r : ℝ≥0} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) : Summable (regularizedG P X r) := by
  have := tsum_regularizedG_eq P r_lt_one X_mble
  by_contra hf
  rw [tsum_def] at this
  simp_all
  have gona : 0 < 1 - r := by
    simp [r_lt_one]
  apply ne_of_lt at gona
  apply gona
  exact_mod_cast this

open scoped lp

lemma regularizedG_square_summable {r : ℝ≥0} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) : regularizedG P X r ∈ ℓ²(Grid d, ℝ) := by
  apply lp.monotone one_le_two
  apply memℓp_gen
  simp only [Real.norm_eq_abs, toReal_one, Real.rpow_one]
  exact Summable.abs (regularizedG_summable P X r_lt_one X_mble)

end RegularizedGreensFunction
