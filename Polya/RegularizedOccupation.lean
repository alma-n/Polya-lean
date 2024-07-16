import Polya.MiscLemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

open MeasureTheory Topology Filter ENNReal NNReal BigOperators

section Grid

/-- The integer grid in `d` dimensions. -/
abbrev Grid d := Fin d → ℤ

/-- The integer grid in `d` dimensions is countable. -/
lemma Grid.countable (d : ℕ) : Countable (Grid d) := by
  sorry

end Grid

section WalkOfSteps

variable {d : ℕ}

/-- Walk on the grid with a given step sequence `steps`. -/
def walkOfSteps (steps : (t : ℕ) → Grid d) (t : ℕ) : Grid d :=
  ∑ s in Finset.range t, steps s

end WalkOfSteps

section RandomWalkOfSteps

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ}

/-- Random walk with a given random step sequence `ξ`. -/
def RW (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) : Grid d :=
  walkOfSteps (fun s ↦ ξ s ω) t

/-- The position of a random walk is a random variable (measurable) if the steps are random
variables (measurable). -/
lemma RW.measurable {ξ : (t : ℕ) → Ω → Grid d} (ξ_mble : ∀ t, Measurable (ξ t)) (t : ℕ) :
    Measurable (RW ξ t) := by
-- Doable with `measurable_const` and `Finset.sum_range_succ` and `Measurable.add`.
-- Note: `measurable_add` is not so convenient here! (It is more general, though.)
  sorry

end RandomWalkOfSteps

noncomputable section RegularizedOccupation

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ}

/-- Regularized occupation of a given walk. -/
def walkRegularizedOccupation (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) :=
  ∑' t, Set.indicator {x} (fun _ ↦ r ^ t) (walk t)

/-- Regularized occupation of a walk at any point is an increasing (more precisely nondecreasing)
function of the regularization parameter `r`. -/
lemma walkRegularizedOccupation_apply_mono (walk : (t : ℕ) → Grid d) (x : Grid d) :
    Monotone (fun r ↦ walkRegularizedOccupation walk r x) := by
  sorry

/-- Regularized occupation of a walk is an increasing (more precisely nondecreasing) function
of the regularization parameter `r`. -/
lemma walkRegularizedOccupation_mono (walk : (t : ℕ) → Grid d) :
    Monotone (fun r ↦ walkRegularizedOccupation walk r) := by
  sorry

/-- Regularized occupation of any walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma walkRegularizedOccupation_le (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    walkRegularizedOccupation walk r x ≤ (1 - r)⁻¹ := by
-- Remark by Kalle: It is "funny" (and convenient) that here we do not need to assume `r<1`,
-- which is usually needed for the convergence of the geometric series. That is because in `ℝ≥0∞`
-- we have `1/∞ = 0` according to Lean's (or rather Mathlib's) definition.
  sorry

/-- Regularized occupation `L_λ` of a random walk. -/
def regularizedOccupation (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) (ω : Ω) :=
  walkRegularizedOccupation (fun t ↦ X t ω) r x

/-- A rewrite lemma for the regularized occupation `L_λ` of a random walk. -/
lemma regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x
      = fun ω ↦ ∑' t, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ r ^ t) ω := rfl

/-- Regularized occupation of a random walk at any point is increasing (more precisely nondecreasing)
in the regularization parameter `r`. -/
lemma regularizedOccupation_apply_mono (X : (t : ℕ) → Ω → Grid d) (x : Grid d) :
    Monotone (fun r ↦ regularizedOccupation X r x) := by
  sorry

/-- Regularized occupation of a random walk is increasing (more precisely nondecreasing) in the
regularization parameter `r`. -/
lemma regularizedOccupation_mono (X : (t : ℕ) → Ω → Grid d) :
    Monotone (fun r ↦ regularizedOccupation X r) := by
  sorry

/-- Regularized occupation of a random walk at any point is left continuous in the
regularization parameter `r`. -/
lemma regularizedOccupation_apply_tendsto_of_monotone (X : (t : ℕ) → Ω → Grid d)
    {rs : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (rs_incr : Monotone rs) (rs_lim : Tendsto rs atTop (𝓝[<] r)) (x : Grid d) :
    Tendsto (fun n ↦ regularizedOccupation X (rs n) x) atTop (𝓝 (regularizedOccupation X r x)) := by
-- This can almost be proven with the Monotone Convergence Theorem
-- `lintegral_tendsto_of_tendsto_of_monotone`, once one writes the infinite sum as an integral
-- with respect to counting measure using `lintegral_count`.
-- One also needs `tendsto_pi_nhds` (characterization of pointwise convergence).
-- Later we might want to generalize this, since the monotonicity hypothesis is
-- in fact unnecessary (but getting rid of it requires some filter stuff).
  sorry

/-- The regularized occupation of a random walk is a random variable (measurable). -/
lemma regularizedOccupation.measurable
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) (x : Grid d) :
    Measurable (regularizedOccupation X r x) := by
  sorry

/-- Regularized occupation of any random walk with regularization `r` is at most `(1-r)⁻¹`. -/
lemma regularizedOccupation_le (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) :
    regularizedOccupation X r x ≤ fun _ ↦ (1 - r)⁻¹ := by
  sorry

/-- Regularized occupation of a random walk is finite if the regularization satisfies `r<1`. -/
lemma regularizedOccupation_lt_top (X : (t : ℕ) → Ω → Grid d)
    {r : ℝ≥0∞} (r_lt_one : r < 1) (x : Grid d) (ω : Ω) :
    regularizedOccupation X r x ω < ∞ := by
  sorry

/-- The sum over possible values of constant indicators of singletons is the constant. -/
lemma tsum_indicator_singleton_eq {S : Type*} [DecidableEq S]
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (y : S) (c : R) :
    ∑' i, Set.indicator {i} (fun _ ↦ c) y = c := by
  sorry
  -- Kalle says: Maybe this belongs to a "misc lemmas" file rather than here.

/-- A random variable always has some value, so it is easy to calculate the sum over possible values of
the indicators of having that value. -/
lemma tsum_indicator_value_eq {S : Type*} [DecidableEq S]
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (Y : Ω → S) (c : R) :
    ∑' i, Set.indicator (Y ⁻¹' {i}) (fun _ ↦ c) ω = c := by
  apply tsum_indicator_singleton_eq

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the indicators of being there. -/
lemma tsum_indicator_walk_position_eq (X : (t : ℕ) → Ω → Grid d)
    {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (c : R) :
    ∑' x, Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ c) ω = c := by
  apply tsum_indicator_singleton_eq

/-- A walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) :
    ∑' x, walkRegularizedOccupation walk r x = ∑' (t : ℕ), r ^ t := by
-- Instead of literal Fubini's theorem (for counting measures), here it is better to use
-- the version `ENNReal.tsum_comm`.
  sorry

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) :
    ∑' x, regularizedOccupation X r x = fun _ ↦ (∑' (t : ℕ), r ^ t):= by
  sorry

/-- A walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_toReal_walkRegularizedOccupation_eq_geom_series (walk : (t : ℕ) → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) :
    ∑' x, (walkRegularizedOccupation walk r x).toReal = (∑' (t : ℕ), r.toReal ^ t):= by
-- To get to use the standard Fubini's theorem `lintegral_lintegral_swap`, one can first
-- rewrite the sums as integrals (w.r.t. counting measures) with `lintegral_count`.
  sorry

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. -/
lemma tsum_toReal_regularizedOccupation_eq_geom_series (X : (t : ℕ) → Ω → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) (ω : Ω) :
    ∑' x, (regularizedOccupation X r x ω).toReal = ∑' (t : ℕ), r.toReal ^ t := by
-- This is easy with the previous one!
  sorry

/-- A random walk is always somewhere, so it is easy to calculate the sum over positions
of the regularized occupations at those positions. When `r < 1`, the infinite sums are
convergent and the calculation yields an equality in `ℝ`. -/
lemma tsum_toReal_regularizedOccupation_eq (X : (t : ℕ) → Ω → Grid d)
    {r : ℝ≥0} (r_lt_one : r < 1) (ω : Ω) :
    ∑' x, (regularizedOccupation X r x ω).toReal = (1 - r)⁻¹ := by
-- This is the previous one conbined with a convergent geometric series.
  sorry

/-- The sum over points of the expected value of the regularized occupation is a
geometric series with the ratio given by the regularization. -/
lemma tsum_lintegral_norm_regularizedOccupation_eq_geom_series
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (∑' (t : ℕ), r ^ t):= by
-- Here the most appropriate version of "Fubini's theorem" is probably `lintegral_tsum`.
  sorry

/-- The sum over points of the expected value of the regularized occupation is just `(1-r)⁻¹`. -/
lemma tsum_lintegral_regularizedOccupation_eq
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, regularizedOccupation X r x ω ∂P = (1 - r)⁻¹ := by
-- Remark by Kalle: Again it is "funny" (and convenient) that here we do not need to assume `r<1`,
-- which is usually needed for the convergence of the geometric series. That is because in `ℝ≥0∞`
-- we have `1/∞ = 0` according to Lean's (or rather Mathlib's) definition.
  sorry

/-- The sum over points of the expected norms of the regularized occupation is at most `(1-r)⁻¹`. -/
lemma tsum_lintegral_norm_regularizedOccupation_le
    {X : (t : ℕ) → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) (r : ℝ≥0∞) :
    ∑' x, ∫⁻ ω, ‖(regularizedOccupation X r x ω).toReal‖.toNNReal ∂P ≤ (1 - r)⁻¹ := by
-- Some of the earlier tricks apply again.
  sorry

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
    {r : ℝ≥0} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x
      = (∫ ω, ∑' x, ∑' t,
        Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ (r : ℝ) ^ t) ω ∂P) := by
-- Kalle says: I changed the phrasing slightly for convenience.
-- Instead of literal Fubini's theorem (for counting measure and expected value), here it is
-- better to use the version `integral_tsum`.
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
