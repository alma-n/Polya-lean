import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib
import Polya.MiscLemmas

open MeasureTheory Topology Filter ENNReal NNReal BigOperators

section Grid

/-- The integer grid in `d` dimensions. -/
abbrev Grid d := Fin d → ℤ

/-- The integer grid in `d` dimensions is countable. -/
lemma Grid.countable (d : ℕ) : Countable (Grid d) := instCountableForallOfFinite

end Grid

section WalkOfSteps

variable {d : ℕ}

/-- Walk on the grid with a given step sequence `steps`. -/
def walkOfSteps (steps : (t : ℕ) → Grid d) (t : ℕ) : Grid d :=
  ∑ s in Finset.range t, steps s

end WalkOfSteps

#eval walkOfSteps (fun _t => fun (d : Fin 2) => (if d = 0 then 1 else 0)) 4
#check ![0, 4]

section RandomWalkOfSteps

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ}

/-- Random walk with a given random step sequence `ξ`. -/
def RW (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) : Grid d :=
  walkOfSteps (fun s ↦ ξ s ω) t

/-- Another equivalent definition with non-fixed `ω : Ω` -/
def RW_def : RW = fun (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) ↦ walkOfSteps (fun s ↦ ξ s ω) t := by rfl

-- h : Eq (A -> B)
-- ∀ A, h : Eq (B)

-- example (f g : A → B) : (h : f = g) ↔
-- #check Function.funext_iff.mp RW_def'

/-- The position of a random walk is a random variable (measurable) if the steps are random
variables (measurable). -/
lemma RW.measurable {ξ : (t : ℕ) → Ω → Grid d} (ξ_mble : ∀ t, Measurable (ξ t)) (t : ℕ) :
    Measurable (RW ξ t) := by
-- Doable with `measurable_const` and `Finset.sum_range_succ` and `Measurable.add`.
-- Note: `measurable_add` is not so convenient here! (It is more general, though.)
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp_rw [RW_def, walkOfSteps, Finset.sum_range_succ]
    exact ih.add (ξ_mble t)

end RandomWalkOfSteps

noncomputable section RegularizedOccupation

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ}

/-- Regularized occupation of a given walk. -/
def walkRegularizedOccupation (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) :=
  ∑' t, Set.indicator {x} (fun _ ↦ r ^ t) (walk t)

lemma ENNReal.pow_le_pow_left : ∀ {a b : ℝ≥0∞}, a ≤ b → ∀ {n : ℕ}, a ^ n ≤  b ^ n :=
  fun h n ↦ pow_le_pow_left' h n

/-- Regularized occupation of a walk at any point is an increasing (more precisely nondecreasing)
function of the regularization parameter `r`. -/
lemma walkRegularizedOccupation_apply_mono (walk : (t : ℕ) → Grid d) (x : Grid d) :
    Monotone (fun r ↦ walkRegularizedOccupation walk r x) := by
  intro r1 r2 hr
  -- rw [MeasureTheory.Measure.tsum_indicator_apply_singleton (s := {x})]
  apply tsum_mono
  repeat exact ENNReal.summable
  rw [Pi.le_def]
  intro n
  by_cases h : walk n = x
  · rw [← Set.mem_singleton_iff] at h
    rw [h]
    simp only [Set.mem_singleton_iff, Set.indicator_of_mem]
    exact ENNReal.pow_le_pow_left hr
  · simp [h]

/-- Regularized occupation of a walk is an increasing (more precisely nondecreasing) function
of the regularization parameter `r`. -/
lemma walkRegularizedOccupation_mono (walk : (t : ℕ) → Grid d) :
    Monotone (fun r ↦ walkRegularizedOccupation walk r) := by
  intro r1 r2 hr
  rw [Pi.le_def]
  exact fun _ ↦ walkRegularizedOccupation_apply_mono _ _ hr

/-- Regularized occupation of any walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma walkRegularizedOccupation_le (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    walkRegularizedOccupation walk r x ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric]
  apply tsum_le_tsum
  · intro t
    by_cases h : walk t = x <;>
      simp [h]
  · exact ENNReal.summable
  · exact ENNReal.summable

-- Remark by Kalle: It is "funny" (and convenient) that here we do not need to assume `r<1`,
-- which is usually needed for the convergence of the geometric series. That is because in `ℝ≥0∞`
-- we have `1/∞ = 0` according to Lean's (or rather Mathlib's) definition.

/-- Regularized occupation `L_λ` of a random walk. -/
def regularizedOccupation (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) (ω : Ω) :=
  walkRegularizedOccupation (fun t ↦ X t ω) r x

/-- A rewrite lemma for the regularized occupation `L_λ` of a random walk. -/
lemma regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x = fun ω ↦ ∑' t, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ r ^ t) ω :=
  rfl

/-- Regularized occupation of a random walk at any point is increasing (more precisely nondecreasing)
in the regularization parameter `r`. -/
lemma regularizedOccupation_apply_mono (X : (t : ℕ) → Ω → Grid d) (x : Grid d) :
    Monotone (fun r ↦ regularizedOccupation X r x) := by
  intro r1 r2 hr
  rw [Pi.le_def]
  exact fun _ ↦ walkRegularizedOccupation_mono _ hr _

/-- Regularized occupation of a random walk is increasing (more precisely nondecreasing) in the
regularization parameter `r`. -/
lemma regularizedOccupation_mono (X : (t : ℕ) → Ω → Grid d) :
    Monotone (fun r ↦ regularizedOccupation X r) := by
  intro r1 r2 hr
  rw [Pi.le_def]
  exact fun _ _ ↦ regularizedOccupation_apply_mono _ _ hr _

/-- Regularized occupation of a random walk at any point is left continuous in the
regularization parameter `r`. -/
lemma regularizedOccupation_apply_tendsto_of_monotone (X : (t : ℕ) → Ω → Grid d)
    {rs : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (rs_incr : Monotone rs) (rs_lim : Tendsto rs atTop (𝓝[<] r)) (x : Grid d) :
    Tendsto (fun n ↦ regularizedOccupation X (rs n) x) atTop (𝓝 (regularizedOccupation X r x)) := by
  simp_rw [regularizedOccupation_eq, ← lintegral_count]

  rw [tendsto_pi_nhds]
  intro ω
  apply lintegral_tendsto_of_tendsto_of_monotone
  · exact fun _ ↦ Measurable.aemeasurable fun ⦃t⦄ _a ↦ trivial
  · rw [Monotone] at rs_incr
    apply Filter.eventually_of_forall
    intro n a b hab
    apply Set.indicator_le_indicator
    exact ENNReal.pow_le_pow_left (rs_incr hab)
  · apply Filter.eventually_of_forall
    intro n
    by_cases h : ω ∈ X n ⁻¹' {x}
    · simp [h]
      -- There should be a more general solution than ENNReal.Tendsto.pow
      apply ENNReal.Tendsto.pow
      intro S h
      rw [Tendsto, Filter.le_def] at rs_lim
      exact rs_lim _ (mem_nhdsWithin_of_mem_nhds h)
    · simp [h]

-- This can almost be proven with the Monotone Convergence Theorem
-- `lintegral_tendsto_of_tendsto_of_monotone`, once one writes the infinite sum as an integral
-- with respect to counting measure using `lintegral_count`.
-- One also needs `tendsto_pi_nhds` (characterization of pointwise convergence).
-- Later we might want to generalize this, since the monotonicity hypothesis is
-- in fact unnecessary (but getting rid of it requires some filter stuff).

/-- The regularized occupation of a random walk is a random variable (measurable). -/
lemma regularizedOccupation.measurable
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) (x : Grid d) :
    Measurable (regularizedOccupation X r x) :=
  Measurable.ennreal_tsum (fun t ↦ Measurable.ite
    (measurableSet_eq_fun (X_mble t) measurable_const) measurable_const measurable_const)

/-- Regularized occupation of any random walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma regularizedOccupation_le (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x ≤ fun _ ↦ (1 - r)⁻¹ := by
  rw [← tsum_geometric, Pi.le_def]
  intro ω
  apply tsum_le_tsum
  intro n
  by_cases h : X n ω = x <;> simp [h]
  · exact ENNReal.summable
  · exact ENNReal.summable

lemma walkRegularizedOccupation_lt_top (X : (t : ℕ) → Grid d)
    {r : ℝ≥0∞} (r_lt_one : r < 1) (x : Grid d) :
    walkRegularizedOccupation X r x < ∞ := by
  rw [walkRegularizedOccupation]
  have gona :  ∑' (t : ℕ), (Set.singleton x).indicator (fun _x ↦ r ^ t) (X t) ≤  ∑' (t : ℕ), (fun _x ↦ r ^ t) (X t) := by
    apply tsum_le_tsum
    intro n
    rw [Set.indicator]
    by_cases h : X n ∈ Set.singleton x
    simp [h]
    simp [h]
    simp
    simp
  have : ∑' (t : ℕ), (fun _x ↦ r ^ t) (X t) < ⊤ := by
    rw [tsum_geometric]
    norm_num
    exact r_lt_one
  exact lt_of_le_of_lt gona this
/-- Regularized occupation of a random walk is finite if the regularization satisfies `r<1`. -/

-- TODO : use walkRegularizedOccupation_lt_top for regularizedOccupation_lt_top

lemma regularizedOccupation_lt_top (X : (t : ℕ) → Ω → Grid d)
    {r : ℝ≥0∞} (r_lt_one : r < 1) (x : Grid d) (ω : Ω) :
    regularizedOccupation X r x ω < ∞ := by
  rw [regularizedOccupation, walkRegularizedOccupation]
  have gona :  ∑' (t : ℕ), (Set.singleton x).indicator (fun _x ↦ r ^ t) (X t ω) ≤  ∑' (t : ℕ), (fun _x ↦ r ^ t) (X t ω) := by
    apply tsum_le_tsum
    · intro n
      rw [Set.indicator]
      by_cases h : X n ω ∈ Set.singleton x
      · simp [h]
      · simp [h]
    · exact ENNReal.summable
    · exact ENNReal.summable
  have : ∑' (t : ℕ), (fun _x ↦ r ^ t) (X t ω) < ⊤ := by
    rw [tsum_geometric]
    norm_num
    exact r_lt_one
  exact lt_of_le_of_lt gona this

/-- The sum over possible values of constant indicators of singletons is the constant. -/
lemma tsum_indicator_singleton_eq {S : Type*} [DecidableEq S]
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (y : S) (c : R) :
    ∑' i, Set.indicator {i} (fun _ ↦ c) y = c := by
  rw [tsum_eq_single]
  · exact if_pos rfl
  · exact fun b' a ↦ if_neg (id (Ne.symm a))

  -- Kalle says: Maybe this belongs to a "misc lemmas" file rather than here.

/-- A random variable always has some value, so it is easy to calculate the sum over possible values of
the indicators of having that value. -/
lemma tsum_indicator_value_eq {S : Type*} [DecidableEq S]
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (Y : Ω → S) (c : R) :
  ∑' i, Set.indicator (Y ⁻¹' {i}) (fun _ ↦ c) ω = c := tsum_indicator_singleton_eq _ _

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the indicators of being there. -/
lemma tsum_indicator_walk_position_eq (X : (t : ℕ) → Ω → Grid d)
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (c : R) :
  ∑' x, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ c) ω = c := tsum_indicator_singleton_eq _ _

/-- A walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) :
    ∑' x, walkRegularizedOccupation walk r x = ∑' (t : ℕ), r ^ t := by
  simp_rw [walkRegularizedOccupation]
  rw [ENNReal.tsum_comm]
  have le1 : ∑' (b : ℕ) (a : Grid d), (Set.singleton a).indicator (fun _x ↦ r ^ b) (walk b) ≤ ∑' (t : ℕ), r ^ t := by
    apply tsum_le_tsum
    intro i
    simp_rw [Set.indicator]
    rw [tsum_eq_single]
    case hf => exact ENNReal.summable
    case b => exact walk i
    case _ => simp [Set.singleton, Set.mem_setOf]
    case _ => exact fun b' a ↦ if_neg (id (Ne.symm a))
    case _ => exact ENNReal.summable
  have le2 : ∑' (t : ℕ), r ^ t ≤ ∑' (b : ℕ) (a : Grid d), (Set.singleton a).indicator (fun _x ↦ r ^ b) (walk b) := by
    apply tsum_le_tsum
    intro i
    simp [Set.indicator]
    rw [tsum_eq_single]
    case b => exact walk i
    case hf => exact ENNReal.summable
    case _ => simp [Set.singleton, Set.mem_setOf]
    case _ => exact fun b' a ↦ if_neg (id (Ne.symm a))
    case _ => exact ENNReal.summable
  exact le_antisymm le1 le2

-- Instead of literal Fubini's theorem (for counting measures), here it is better to use
-- the version `ENNReal.tsum_comm`.

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) :
    ∑' x, regularizedOccupation X r x = fun _ ↦ (∑' (t : ℕ), r ^ t):= by
  ext ω
  rw [tsum_apply]
  apply tsum_walkRegularizedOccupation_eq_geom_series
  rw [Pi.summable]
  exact fun _ ↦ ENNReal.summable

/-- A walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_toReal_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) :
    ∑' x, (walkRegularizedOccupation walk r x).toReal = (∑' (t : ℕ), r.toReal ^ t):= by
  rw [← ENNReal.tsum_toReal_eq, tsum_walkRegularizedOccupation_eq_geom_series]
  · exact ENNReal.tsum_toReal_eq (fun _ ↦ pow_ne_top coe_ne_top)
  · exact fun _ ↦ LT.lt.ne (walkRegularizedOccupation_lt_top _ (coe_lt_one_iff.mpr r_lt_one) _)

-- To get to use the standard Fubini's theorem `lintegral_lintegral_swap`, one can first
-- rewrite the sums as integrals (w.r.t. counting measures) with `lintegral_count`.

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_toReal_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) (ω : Ω) :
    ∑' x, (regularizedOccupation X r x ω).toReal = ∑' (t : ℕ), r.toReal ^ t :=
  tsum_toReal_walkRegularizedOccupation_eq_geom_series (fun t ↦ X t ω) r_lt_one
-- This is easy with the previous one!

lemma summable_regularizedOccupation : Summable (regularizedOccupation X r) := by
  rw [Pi.summable]
  exact fun _ ↦ ENNReal.summable

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. When `r < 1`, the infinite sums are
convergent and the calculation yields an equality in `ℝ`. -/
lemma tsum_toReal_regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) (ω : Ω) :
    ∑' x, (regularizedOccupation X r x ω).toReal = (1 - r)⁻¹ := by
  rw [← tsum_toReal_eq]
  · rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series]
    · rw [tsum_geometric, toReal_inv]; rfl
    · exact summable_regularizedOccupation
  · exact fun _ ↦ LT.lt.ne (regularizedOccupation_lt_top _ (coe_lt_one_iff.mpr r_lt_one) _ _)
-- This is the previous one conbined with a convergent geometric series.

/-- The sum over points of the expected value of the regularized occupation is a
geometric series with the ratio given by the regularization. -/
lemma tsum_lintegral_norm_regularizedOccupation_eq_geom_series
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (∑' (t : ℕ), r ^ t):= by
  rw [← lintegral_tsum]
  conv =>
    enter [1, 2, ω] -- short for arg 1; arg 2; intro ω
    -- rw [← tsum_apply (hf := summable_regularizedOccupation)]
    rw [← tsum_apply] -- generates a subgoal for hf
    · rw [tsum_regularizedOccupation_eq_geom_series]
    · exact summable_regularizedOccupation
  · simp
  · exact fun _ ↦ Measurable.aemeasurable (regularizedOccupation.measurable X_mble r _)

-- Here the most appropriate version of "Fubini's theorem" is probably `lintegral_tsum`.
/-- The sum over points of the expected value of the regularized occupation is just `(1-r)⁻¹`. -/
lemma tsum_lintegral_regularizedOccupation_eq
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (1 - r)⁻¹ := by
  rw [← tsum_geometric]
  exact tsum_lintegral_norm_regularizedOccupation_eq_geom_series _ X_mble _

-- Remark by Kalle: Again it is "funny" (and convenient) that here we do not need to assume `r<1`,
-- which is usually needed for the convergence of the geometric series. That is because in `ℝ≥0∞`
-- we have `1/∞ = 0` according to Lean's (or rather Mathlib's) definition.

/-- The sum over points of the expected norms of the regularized occupation is at most `(1-r)⁻¹`. -/
lemma tsum_lintegral_norm_regularizedOccupation_le
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, ‖(regularizedOccupation X r x ω).toReal‖.toNNReal ∂P ≤ (1 - r)⁻¹ := by
  by_cases rge1 : r ≥ 1
  · simp only [rge1, tsub_eq_zero_of_le, ENNReal.inv_zero]
    exact le_top
  simp at rge1
  rw [← lintegral_tsum]
  · have norm_le_lemma : ∀ ω x, ‖(regularizedOccupation X r x ω).toReal‖.toNNReal ≤ (regularizedOccupation X r x ω).toReal.toNNReal := by
      intros ω x
      rw [Real.toNNReal_le_toNNReal_iff toReal_nonneg]
      rw [Real.norm_eq_abs]
      rw [abs_eq_self.mpr toReal_nonneg]
    -- have summable : ∀ ω, Summable (fun x ↦ (regularizedOccupation X r x ω).toReal) := by
    --   intro ω
    --   apply ENNReal.summable_toReal
    --   rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series, tsum_geometric]
    --   apply LT.lt.ne
    --   simp

    have : ∫⁻ (ω : Ω), ∑' (i : Grid d), (regularizedOccupation X r i ω).toReal.toNNReal ∂P ≤ (1 - r)⁻¹ := by
      have summable_toReal_toNNReal (ω : Ω) : Summable (fun i ↦ (regularizedOccupation X r i ω).toReal.toNNReal) := by
        rw [← tsum_coe_ne_top_iff_summable]
        rw [← ENNReal.coe_tsum (by
          -- TODO refactor this proof (used multiple times)
          apply Summable.toNNReal
          apply ENNReal.summable_toReal
          apply LT.lt.ne
          rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series, tsum_geometric]
          simp
          exact rge1
          · rw [Pi.summable]
            intro o
            exact ENNReal.summable
          )]
        simp only [toNNReal_toReal_eq, ne_eq, coe_ne_top, not_false_eq_true]
      conv in tsum _ =>
        rw [← ENNReal.coe_tsum (summable_toReal_toNNReal ω)]
      -- simp_rw [Real.toNNReal_coe]
      conv in tsum _ =>
        enter [1, a]
        -- rw [Real.toNNReal]
        simp
      have regularizedOccupation_lt_top' (ω : Ω) : ∀ (a : Grid d), regularizedOccupation X r a ω ≠ ⊤ := by
        intro x
        apply LT.lt.ne
        apply regularizedOccupation_lt_top
        exact rge1
      conv in tsum _ =>
        rw [← ENNReal.tsum_toNNReal_eq (regularizedOccupation_lt_top' ω)]
        rw [← tsum_apply summable_regularizedOccupation]
      simp_rw [tsum_regularizedOccupation_eq_geom_series]
      rw [tsum_geometric, lintegral_const, measure_univ, mul_one]
      exact coe_toNNReal_le_self

    apply le_trans _ this
    have lemma2 ω : ∑' x, ‖(regularizedOccupation X r x ω).toReal‖.toNNReal ≤ ∑' x,(regularizedOccupation X r x ω).toReal.toNNReal := by
      apply tsum_le_tsum (norm_le_lemma ω)
      · apply Summable.toNNReal
        simp_rw [Real.norm_eq_abs, abs_toReal]
        apply ENNReal.summable_toReal
        apply LT.lt.ne
        rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series, tsum_geometric]
        simp
        exact rge1
        · rw [Pi.summable]
          intro o
          exact ENNReal.summable
      · apply Summable.toNNReal
        apply ENNReal.summable_toReal
        apply LT.lt.ne
        rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series, tsum_geometric]
        simp
        exact rge1
        · rw [Pi.summable]
          intro o
          exact ENNReal.summable

    -- simp_rw [← ENNReal.coe_tsum (by
    --   sorry
    -- )]

    conv =>
      arg 1
      arg 2
      intro ω
      rw [← ENNReal.coe_tsum (by
      apply Summable.toNNReal
      simp_rw [Real.norm_eq_abs, abs_toReal]
      apply ENNReal.summable_toReal
      apply LT.lt.ne
      rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series, tsum_geometric]
      simp only [inv_lt_top, tsub_pos_iff_lt]
      · exact rge1
      · rw [Pi.summable]; exact fun _ ↦ ENNReal.summable
      )]

    conv =>
      arg 2
      arg 2
      intro ω
      rw [← ENNReal.coe_tsum (by
      apply Summable.toNNReal
      apply ENNReal.summable_toReal
      apply LT.lt.ne
      rw [← tsum_apply, tsum_regularizedOccupation_eq_geom_series, tsum_geometric,
        inv_lt_top, tsub_pos_iff_lt]
      · exact rge1
      · rw [Pi.summable]; exact fun _ ↦ ENNReal.summable
      )]

    apply lintegral_mono
    rw [Pi.le_def]
    intro ω
    rw [ENNReal.coe_le_coe]
    exact lemma2 ω
  · refine fun _ ↦  Measurable.aemeasurable ?_
    simp only [Real.norm_eq_abs, abs_toReal, toNNReal_toReal_eq, measurable_coe_nnreal_ennreal_iff]
    exact Measurable.ennreal_toNNReal (regularizedOccupation.measurable X_mble r _)

-- Some of the earlier tricks apply again.

end RegularizedOccupation

noncomputable section RegularizedGreensFunction

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ}

/-- The regularized Green's function of a random walk. -/
def regularizedG (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) : ℝ :=
  ∫ ω, ENNReal.toReal (regularizedOccupation X r x ω) ∂P

/-- An auxiliary step: one can interchange a sum and expected value for `regularizedG` summed over
all grid points. -/
lemma tsum_regularizedG_eq_lintegral_tsum {X : (t : ℕ) → Ω → Grid d}
    {r : ℝ≥0}
    (r_lt_one : r < 1)
    (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x
      = (∫ ω, ∑' x, ∑' t,
    Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ (r : ℝ) ^ t) ω ∂P) := by

  simp_rw [regularizedG, Set.indicator, regularizedOccupation, walkRegularizedOccupation, Set.indicator]
  rw [integral_tsum]
  -- simp_rw [Set.mem_singleton_iff]
  -- have (x) (ω) : ∀ (a : ℕ), (if X a ω = x then (↑r : ℝ≥0∞) ^ a else 0) ≠ ∞ := by
  conv =>
    enter [1, 1, x, 2, ω]
    rw [ENNReal.tsum_toReal_eq (by
      intro a
      by_cases h : X a ω = x
      · simp [h]
      · simp [h]
    )]
    simp [apply_ite]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  · intro x
    apply Measurable.aestronglyMeasurable

    have : Measurable $ fun (ω : Ω) ↦ ∑' (t : ℕ), Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ (r : ℝ≥0∞) ^ t) ω := by
      apply regularizedOccupation.measurable X_mble

    have := Measurable.coe_nnreal_real (Measurable.ennreal_toNNReal this)
    convert this
    rename_i ω

    rw [ENNReal.tsum_toNNReal_eq (by
      intro n
      rw [Set.indicator]
      by_cases h : ω ∈ X n ⁻¹' {x}
      · simp [h]
      · simp [h]
    )]
    simp_rw [NNReal.coe_tsum]
    simp_rw [Set.indicator]
    simp_rw [apply_ite]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, toNNReal_pow, toNNReal_coe, NNReal.coe_pow,
      zero_toNNReal, NNReal.coe_zero]
  · rw [← lintegral_tsum]
    sorry
    sorry

-- Kalle says: I changed the phrasing slightly for convenience.
-- Instead of literal Fubini's theorem (for counting measure and expected value), here it is
-- better to use the version `integral_tsum`.

-- Lemma 4.14
lemma tsum_regularizedG_eq_lintegral_tsum' {X : (t : ℕ) → Ω → Grid d}
    {r : ℝ≥0} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x
      = (∫ ω, ∑' x, (regularizedOccupation X r x ω).toReal ∂P) := by
  conv =>
    arg 1
    arg 1
    intro x
    rw [regularizedG]
  rw [integral_tsum]
  intro x
  apply Measurable.aestronglyMeasurable
  apply Measurable.ennreal_toReal
  exact regularizedOccupation.measurable X_mble (↑r) x
  -- apply LT.lt.ne
  -- apply ENNReal.lt_top_of_tsum_ne_top
-- tsum_lintegral_norm_regularizedOccupation_le
  sorry

/-- A summability criterion for a slightly generalized version of walk occupations. -/
lemma summable_weighted_occupation {walk : (t : ℕ) → Grid d}
    {g : ℕ → ℝ} (g_abssummable : ∑' t, ENNReal.ofReal |g t| ≠ ∞) :
    Summable
      (Function.uncurry fun (t : ℕ) (x : Grid d) ↦ Set.indicator {x} (fun _↦ g t) (walk t)) := by
-- Kalle says: Probably the cleanest way to do this would be to generalize this further.
-- But for now, this seems ok. If you like, thinking about the right generalization can
-- nevertheless be very useful!
-- At least the general helper lemma `summable_of_abs_le_of_tsum_ne_top` can be used here.
-- The earlier tricks (Fubini variants and juggling between sums and integrals w.r.t
-- counting measures) can also come in handy.
  sorry

/-- A summability criterion for (basically) regularized walk occupations. -/
lemma summable_regularized_occupation {walk : (t : ℕ) → Grid d} {r : ℝ≥0} (r_lt_one : r < 1) :
    Summable (Function.uncurry fun (t : ℕ) (x : Grid d) ↦ Set.indicator {x} (fun _ ↦ (r : ℝ) ^ t) (walk t)) := by
-- The idea is to get this from the slightly generalized version `summable_weighted_occupation`.
  sorry

lemma tsum_regularizedG_eq {X : (t : ℕ) → Ω → Grid d}
    {r : ℝ≥0} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x = (1 - r)⁻¹ := by
-- Tada! The first line of equalities of the main proof will be completed here!
  sorry

end RegularizedGreensFunction
