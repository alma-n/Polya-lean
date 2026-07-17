module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Polya.RegularizedG
@[expose] public section

open MeasureTheory Topology Filter
open VectorFourier
open ENNReal NNReal
open BigOperators

/-
Note that compared to Mathlib conventions and usual Fourier series conventions, our
"Fourier transform" is backwards. The reason is that our "physical space" for the random
walk is the discrete lattice `ℤᵈ` and our "momentum space" is the compact torus `ℝᵈ/ℤᵈ`.
(The standard conventions correspond to the more common case when the "physical space" is
compact and "momentum" is quantized on the discrete lattice.)
Explicitly in the 1-dimensional case, this means that:
 * Usually one starts with a square-integrable periodic function `f : ℝ → ℂ`
   (a complex-valued L²-function on `AddCircle`) and defines its Fourier coefficients
   indexed by `ℤ`.
 * We start from a regularized Green's function function `G : ℤ → ℂ` and to define its
   (backwards) Fourier transform we view `G` as a collection of Fourier coefficients of a
   certain periodic function `Ghat : ℝ → ℂ`. Thus for us, performing the Fourier transform
   is like inverting a Fourier transform in the ordinary conventions, and inverting a
   Fourier transform is like performing a Fourier transform in the ordinary sense.
 * (The periodicity of Ghat is taken such that the circumference of the circle is `T := 2π`.)
-/

notation "π" => Real.pi

instance : Fact (2*π > 0) where
  out := by simp [Real.pi_pos]

#check AddCircle
#check fourier

#check HilbertBasis
#check fourierBasis

#check fourierCoeff
#check fourierCoeff_eq_intervalIntegral

#check HilbertBasis.repr
#check fourierBasis_repr



section Mock_regularized_Green_function_and_its_Fourier_transform
/- This section is for playing around with a mock version of the actual regularized
Green's function. -/

-- Mock regularized Green's function (in dimension 1), to be replaced by the real deal.
-- In `G r x`, `r ≥ 0` is the regularization parameter and `x : ℤ` is the position.
variable (G : ℝ≥0 → ℤ → ℝ)

/-- Regularized Green's function (mock + in dimension 1) seen as an element of `l¹(ℤ)`. -/
def Gl1 : ℝ≥0 → lp (fun (_ : ℤ) ↦ ℂ) 1 := fun r ↦ {
  val := fun x ↦ G r x
  property := by
    -- Need to prove summability of `x ↦ |G r x|`. (Assume `0 ≤ r < 1`, otherwise give junk!)
    -- Of course this cannot be proven for the mock `G` here, but it should be proven for the
    -- actual regularized Green's function.
    sorry
  }

/-- Regularized Green's function (mock + in dimension 1) as an element of `l²(ℤ)`. -/
def Gl2 : ℝ≥0 → lp (fun (_ : ℤ) ↦ ℂ) 2 := fun r ↦
  { val := Gl1 G r
    property := lp.monotone one_le_two (Gl1 G r).property }

/-- The Fourier transform of the (mock + in dimension 1) regularized Green's function. -/
noncomputable def Ghat := fun (r : ℝ≥0) ↦ (fourierBasis (T := 2*π)).repr.symm (Gl2 G r)

/-- The inverse Fourier transform of the Fourier transform of the (mock + in dimension 1)
regularized Green's function is the regularized Green's function. -/
lemma fourierCoeff_Ghat_eq (r : ℝ≥0) (x : ℤ) :
    fourierCoeff (T := 2*π) (Ghat G r) x = G r x := by
  rw [← fourierBasis_repr]
  simp only [Ghat, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The (mock + in dimension 1) regularized Green's function is given by an integral (the explicit
Fourier inverse transform) of its Fourier transform. -/
lemma G_eq_integral_Ghat (r : ℝ≥0) (x : ℤ) :
    G r x = (2*π)⁻¹ * ∫ (θ : ℝ) in (-π)..π, (fourier (T := 2*π) (-x)) θ • (Ghat G r θ) := by
  suffices G r x = (1/(2*π)) • ∫ (θ : ℝ) in (-π)..(-π + 2 * π), (fourier (T := 2*π) (-x)) θ •
  (Ghat G r θ) by
    rw [← smul_eq_mul]
    rw [← inv_eq_one_div] at this
    exact_mod_cast by grind
  rw [← fourierCoeff_eq_intervalIntegral, fourierCoeff_Ghat_eq]
  -- hopefully `fourierCoeff_eq_intervalIntegral` and some simplifications

end Mock_regularized_Green_function_and_its_Fourier_transform

section Actual_regularized_Green_function_and_its_Fourier_transform

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ} {X : ℕ → Ω → Grid d}

/-- Regularized Green's function seen as an element of `l¹(ℤᵈ)`. -/
noncomputable def regularizedG.l1 (X_mble : ∀ t : ℕ, Measurable (X t)) : ℝ≥0 → lp (fun (_ : Grid d) ↦ ℂ) 1 := fun r ↦ {
  val := if r < 1 then fun x ↦ regularizedG P X r x else fun _ ↦ 0 -- junk if `r ≥ 1`.
  property := by
    suffices Summable fun i => ‖(if r < 1 then fun x ↦ (regularizedG P X r x : ℂ) else fun x ↦ 0) i‖ by
      simpa [lp, Memℓp]
    by_cases hr : 1 ≤ r
    · simp [show ¬ r < 1 from not_lt.mpr hr]
    · rw [not_le] at hr
      simp [hr]
      exact Summable.abs (regularizedG_summable P hr X_mble)
  }

/-- Regularized Green's function (mock + in dimension 1) as an element of `l²(ℤ)`. -/
noncomputable def regularizedG.l2 (X_mble : ∀ t : ℕ, Measurable (X t)) : ℝ≥0 → lp (fun (_ : Grid d) ↦ ℂ) 2 := fun r ↦
  { val := regularizedG.l1 P X_mble r
    property := lp.monotone one_le_two (regularizedG.l1 P X_mble r).property }

-- The 1-dimensional case of the actual regularized Green's function.
variable {X₁ : ℕ → Ω → Grid 1}

#synth SeminormedAddCommGroup (Grid 1)

/-- `ℤ¹ ≃ ℤ` -/
def Grid₁.toZ : Grid 1 ≃ ℤ where
  toFun x := x 0
  invFun n := fun _ ↦ n
  left_inv := by intro x; ext i; simp [Fin.fin_one_eq_zero i]
  right_inv := by intro n; simp

#check  LinearEquiv.coe_mk

noncomputable def regularizedG₁.l2 (X_mble : ∀ t : ℕ, Measurable (X₁ t))(r : ℝ≥0)  : lp (fun (_ : ℤ) ↦ ℂ) 2 :=
  { val := fun x ↦ (regularizedG.l1 P X_mble r).val (Grid₁.toZ.symm x)
    property := by
      have := (regularizedG.l1 P X_mble r).property
      apply lp.monotone one_le_two
      simp_rw [lp, Memℓp] at *
      simp_all
      rw [summable_norm_iff] at *
      change Summable ((regularizedG.l1 P X_mble r) ∘ (Grid₁.toZ.symm))
      exact (Equiv.summable_iff (e := Grid₁.toZ.symm)).mpr this
      -- this is morally `(regularizedG.l2 P X₁ r).property`
      }

/-- The Fourier transform of the (in dimension 1) regularized Green's function. -/
noncomputable def regularizedG₁.hat (X_mble : ∀ t : ℕ, Measurable (X₁ t)) :=
  fun (r : ℝ≥0) ↦ (fourierBasis (T := 2*π)).repr.symm (regularizedG₁.l2 P X_mble r)

/-- The inverse Fourier transform of the Fourier transform of the (in dimension 1)
regularized Green's function is the regularized Green's function. -/
lemma fourierCoeff_regularizedG₁hat_eq
    (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (r_lt_one : r < 1) (n : ℤ) :
    (fourierCoeff (T := 2*π) (regularizedG₁.hat P X_mble r)) n
      = regularizedG P X₁ r (Grid₁.toZ.symm n) := by
  rw [regularizedG₁.hat, ← fourierBasis_repr]
  simp_rw [Grid₁.toZ, regularizedG₁.l2, regularizedG.l1]
  simp [r_lt_one]
  rfl

/-- The (in dimension 1) regularized Green's function is given by an integral (the explicit
Fourier inverse transform) of its Fourier transform. -/
lemma regularizedG_eq_integral_regularizedG₁hat (X₁_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (r_lt_one : r < 1) (x : Grid 1) :
    regularizedG P X₁ r x
      = (2*π)⁻¹ * ∫ (θ : ℝ) in (-π)..π,
          (fourier (T := 2*π) (-(Grid₁.toZ x))) θ • (regularizedG₁.hat P X₁_mble r θ) := by
  suffices regularizedG P X₁ r x = (1/(2*π)) • ∫ (θ : ℝ) in (-π)..(-π + 2 * π), (fourier (T := 2*π) (-(Grid₁.toZ x))) θ • (regularizedG₁.hat P X₁_mble r θ) by
    rw [← smul_eq_mul]
    rw [← inv_eq_one_div] at this
    exact_mod_cast by grind
  rw [← fourierCoeff_eq_intervalIntegral (T := 2 * π)]
  rw [fourierCoeff_regularizedG₁hat_eq]
  · simp only [Equiv.symm_apply_apply]
  · exact r_lt_one
  -- hopefully `fourierCoeff_eq_intervalIntegral` and some simplifications
#check Complex.re

#check ContinuousLinearMap.integral_comp_comm

#check Complex.reCLM
#check Complex.reCLM_apply

-- This continuity should be true, but there is a bit of abuse since it relies
-- on a particular representative from the equivalence class of almost everywhere
-- equal functions (equality in `L²(AddCircle)`).
-- If this is a problem, then we should prove that `regularizedG₁.hat P X₁ r` is
-- a.e. equal (`=ᵐ[AddCircle.haarAddCircle]`) to the right continuous function.

#check ContinuousMap.coe_toLp

#check fourierIntegral_continuous

lemma continuous_regularizedG₁hat (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (r_lt_one : r < 1) :
    Continuous (fun θ ↦ regularizedG₁.hat P X_mble r θ) := by
  unfold regularizedG₁.hat
  have := HilbertBasis.hasSum_repr_symm (fourierBasis (T := 2 * π)) (regularizedG₁.l2 P X_mble r)
  -- simp_rw [regularizedG_eq_integral_regularizedG₁hat P X_mble r r_lt_one]
  -- apply continuous_of_dominated
  -- dominant convergence theorem
  -- fourierIntegral_continuous (this is very close)
  sorry

lemma integrable_regularizedG₁hat (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (r_lt_one : r < 1) : Integrable (fun θ ↦ (regularizedG₁.hat P X_mble r θ).re) := by

  -- AEEqFun.integrable_iff_mem_L1
  sorry
  -- Gr₁hat ∈ L² ⊆ L¹ = integrable

/-- The (in dimension 1) regularized Green's function is given by an explicit real integral. -/
lemma regularizedG_eq_real_integral_regularizedG₁hat (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (r_lt_one : r < 1) (x : Grid 1) :
    regularizedG P X₁ r x
      = (2*π)⁻¹ * ∫ (θ : ℝ) in (-π)..π,
          ((fourier (T := 2*π) (-(Grid₁.toZ x))) θ • (regularizedG₁.hat P X_mble r θ)).re := by
  convert congr_arg Complex.re <| regularizedG_eq_integral_regularizedG₁hat P X_mble r r_lt_one x
  rw [Complex.re_ofReal_mul]
  congr
  simp_rw [← Complex.reCLM_apply]
  rw [ContinuousLinearMap.intervalIntegral_comp_comm]
  apply Continuous.intervalIntegrable (Continuous.mul ?_ ?_)
  · continuity
  · apply Continuous.comp (continuous_regularizedG₁hat P X_mble r r_lt_one)
    exact { isOpen_preimage := fun s a ↦ a }

/-- The main integral, which is proportional to the Green's function at the
origin (and whose finiteness in the `r ↑ 1` limit characterizes transience). -/
noncomputable def mainIntegral (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) :=
  ∫ (θ : ℝ) in Set.Ioc (-π) π, (regularizedG₁.hat P X_mble r θ).re

/-- The easy "high frequency" part of the main integral. -/
noncomputable def highFreqIntegral (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (δ : ℝ≥0) :=
  ∫ (θ : ℝ) in (Set.Ioc (-π) π) \ Metric.ball 0 δ, (regularizedG₁.hat P X_mble r θ).re

/-- The interesting "low frequency" part of the main integral. -/
noncomputable def lowFreqIntegral (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r : ℝ≥0) (δ : ℝ≥0) :=
  ∫ (θ : ℝ) in Metric.ball 0 δ, (regularizedG₁.hat P X_mble r θ).re

/-- The decomposition of the main integral to high and low frequency parts. -/
lemma mainIntegral_eq_add {r δ : ℝ≥0} (X_mble : ∀ t : ℕ, Measurable (X₁ t)) (r_lt_one : r < 1) (hδ : δ ≤ π) :
    mainIntegral P X_mble r = highFreqIntegral P X_mble r δ + lowFreqIntegral P X_mble r δ := by
  rw [mainIntegral, lowFreqIntegral, highFreqIntegral]
  rw [← MeasureTheory.setIntegral_union₀]
  have : Set.Ioc (-π) π ∪ Metric.ball 0 δ = Set.Ioc (-π) π := by
    rw [Set.union_eq_left, Real.ball_zero_eq_Ioo]
    grind
  rw [Set.diff_union_self, this]
  · apply Disjoint.aedisjoint
    exact Set.disjoint_sdiff_left
  · apply MeasurableSet.nullMeasurableSet
    exact measurableSet_ball
  · apply Integrable.integrableOn
    have := integrable_regularizedG₁hat P X_mble r r_lt_one

    sorry
  · apply Integrable.integrableOn
    have := integrable_regularizedG₁hat P X_mble r r_lt_one

    sorry


#check MeasureTheory.setIntegral_union₀

end Actual_regularized_Green_function_and_its_Fourier_transform
