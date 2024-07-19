import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic

open ENNReal NNReal



section Auxiliary

-- This `@[simp]`lemma should be soon added to Mathlib (there is a PR including this already).
@[simp] lemma ENNReal.toNNReal_toReal_eq (z : ℝ≥0∞) : z.toReal.toNNReal = z.toNNReal := by
  ext; simp only [Real.coe_toNNReal', ge_iff_le, toReal_nonneg, max_eq_left]; rfl

/-- The (topological) sum of `ℝ≥0∞` valued functions evaluated at a point is the (topological)
sum of the evaluations of those functions.  -/
lemma tsum_pi_ennreal_apply {ι α : Type*} (fs : ι → α → ℝ≥0∞) (a : α) :
    (∑' i, fs i) a = ∑' i, fs i a := by
-- Remark by Kalle: It is mildly annoying that one sometimes needs to invoke this triviality
-- explicitly. Maybe we could make it a local `@[simp]` lemma (include in our own `simp` set).
-- I forgot how to do that exactly. Temporarily just marking this lemma with a `@[simp]` tag
-- might (or might not) reduce pain below... Feel free to do that or try to make this more
-- automatic in other ways!
-- The proof needs `tendsto_pi_nhds`, which is the convenient characterization of convergence
-- in the topology of pointwise convergence (product topology, hence the "pi").
  exact ENNReal.tsum_apply

-- Kalle says: This should definitely be in Mathlib...
instance MeasureTheory.sigmaFinite_count
    {α : Type*} [Countable α] {m : MeasurableSpace α} [MeasurableSingletonClass α] :
    SigmaFinite (@Measure.count α m) := by
-- Kalle says: This is a bit measure-theoretic, but in principle easy.
  sorry

-- Kalle says: This should be added to Mathlib if it is actually not there already...
lemma MeasureTheory.count_prod_count
    {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    (hX : SigmaFinite (Measure.count (α := X))) (hY : SigmaFinite (Measure.count (α := Y))) :
    (Measure.count (α := X)).prod (Measure.count (α := Y)) = (Measure.count (α := X × Y)) := by
-- Kalle says: I did not yet prove this, but it should be a true statement
-- and thus safe to build on... The (math) proof is a bit measure-theoretic (uses
-- sigma-finiteness and pi-systems etc.), so maybe feel free to skip it for now.
  sorry

-- Kalle says: I would have expected to find this in Mathlib...
-- But maybe `NNReal.summable_coe` is considered sufficient.
lemma summable_of_summable_toNNReal {ι : Type*} {f : ι → ℝ}
    (f_nn : ∀ i, 0 ≤ f i) (hf : Summable (fun i ↦ (f i).toNNReal)) :
    Summable f := by
  rw [Summable] at *
  cases' hf with r hr
  sorry

-- Kalle says: I would have expected to find (a generalized version of) this in Mathlib...
lemma summable_of_summable_nnnorm {ι : Type*} {f : ι → ℝ} (hf : Summable (fun i ↦ ‖f i‖₊)) :
    Summable f := by
-- Using `summable_of_summable_toNNReal` is one way (after noticing that absolute
-- summability suffices).
  sorry

-- Kalle says: I would have expected to find (a generalized version of) this in Mathlib...
lemma summable_of_tsum_nnnorm_ne_top {ι : Type*} {f : ι → ℝ} (hf : ∑' i, (‖f i‖₊ : ℝ≥0∞) ≠ ∞) :
    Summable f := by
-- Using `summable_of_summable_nnnorm` is one way.
  sorry

-- Kalle says: I would have expected to find (a generalized version of) this in Mathlib...
lemma summable_of_abs_le_of_tsum_ne_top {ι : Type*} {f : ι → ℝ} {g : ι → ℝ≥0}
    (hf : ∀ i, |f i| ≤ g i) (hg : ∑' i, (g i : ℝ≥0∞) ≠ ∞) :
    Summable f := by
-- Using `summable_of_tsum_nnnorm_ne_top` is one way.
  sorry

end Auxiliary
