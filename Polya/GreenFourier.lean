import Mathlib
import Polya.RegularizedOccupation

open MeasureTheory Topology Filter
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
    simp only [lp, Memℓp, one_ne_zero, ↓reduceIte, one_ne_top, Complex.norm_eq_abs, one_toReal,
               Real.rpow_one, AddSubgroup.mem_mk, Set.mem_setOf_eq, Complex.abs_ofReal]
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
  -- morally `rfl`
  sorry

/-- The (mock + in dimension 1) regularized Green's function is given by an integral (the explicit
Fourier inverse transform) of its Fourier transform. -/
lemma G_eq_integral_Ghat (r : ℝ≥0) (x : ℤ) :
    G r x = (2*π)⁻¹ * ∫ (θ : ℝ) in (-π)..π, (fourier (T := 2*π) (-x)) θ • (Ghat G r θ) := by
  -- hopefully `fourierCoeff_eq_intervalIntegral` and some simplifications
  sorry

end Mock_regularized_Green_function_and_its_Fourier_transform



section Actual_regularized_Green_function_and_its_Fourier_transform

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {d : ℕ} (X : ℕ → Ω → Grid d)

/-- Regularized Green's function seen as an element of `l¹(ℤᵈ)`. -/
noncomputable def regularizedG.l1 : ℝ≥0 → lp (fun (_ : Grid d) ↦ ℂ) 1 := fun r ↦ {
  val := if r < 1 then fun x ↦ regularizedG P X r x else fun _ ↦ 0 -- junk if `r ≥ 1`.
  property := by
    simp only [lp, Memℓp, one_ne_zero, ↓reduceIte, one_ne_top, Complex.norm_eq_abs, one_toReal,
               Real.rpow_one, AddSubgroup.mem_mk, Set.mem_setOf_eq]
    by_cases hr : 1 ≤ r
    · simpa [show ¬ r < 1 from not_lt.mpr hr] using summable_zero
    · -- (Case: "not junk". Math content starts from here.)
      sorry
  }

/-- Regularized Green's function (mock + in dimension 1) as an element of `l²(ℤ)`. -/
noncomputable def regularizedG.l2 : ℝ≥0 → lp (fun (_ : Grid d) ↦ ℂ) 2 := fun r ↦
  { val := regularizedG.l1 P X r
    property := lp.monotone one_le_two (regularizedG.l1 P X r).property }

-- The 1-dimensional case of the actual regularized Green's function.
variable (X₁ : ℕ → Ω → Grid 1)

/-- `ℤ¹ ≃ ℤ` -/
def Grid₁.toZ : Grid 1 ≃ ℤ where
  toFun x := x 0
  invFun n := fun _ ↦ n
  left_inv := by intro x; ext i; simp [Fin.fin_one_eq_zero i]
  right_inv := by intro n; simp

noncomputable def regularizedG₁.l2 : ℝ≥0 → lp (fun (_ : ℤ) ↦ ℂ) 2 := fun r ↦
  { val := fun x ↦ regularizedG.l1 P X₁ r (Grid₁.toZ.symm x)
    property := by
      -- this is morally `(regularizedG.l2 P X₁ r).property`
      sorry }

/-- The Fourier transform of the (in dimension 1) regularized Green's function. -/
noncomputable def regularizedG₁.hat :=
  fun (r : ℝ≥0) ↦ (fourierBasis (T := 2*π)).repr.symm (regularizedG₁.l2 P X₁ r)

/-- The inverse Fourier transform of the Fourier transform of the (in dimension 1)
regularized Green's function is the regularized Green's function. -/
lemma fourierCoeff_regularizedG₁hat_eq (r : ℝ≥0) (n : ℤ) :
    (fourierCoeff (T := 2*π) (regularizedG₁.hat P X₁ r)) n
      = regularizedG P X₁ r (Grid₁.toZ.symm n) := by
  -- morally `rfl`
  sorry

/-- The (in dimension 1) regularized Green's function is given by an integral (the explicit
Fourier inverse transform) of its Fourier transform. -/
lemma regularizedG_eq_integral_regularizedG₁hat (r : ℝ≥0) (x : Grid 1) :
    regularizedG P X₁ r x
      = (2*π)⁻¹ * ∫ (θ : ℝ) in (-π)..π,
          (fourier (T := 2*π) (-(Grid₁.toZ n))) θ • (regularizedG₁.hat P X₁ r θ) := by
  -- hopefully `fourierCoeff_eq_intervalIntegral` and some simplifications
  sorry

end Actual_regularized_Green_function_and_its_Fourier_transform
