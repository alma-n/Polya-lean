import Polya.IntegralInvFourier
import Polya.RegularizedG

open UnitAddTorus MeasureTheory ENNReal NNReal Convolution

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

lemma invFourier_regularizedG_eq {X : ℕ → Ω → Grid d} {r : ℝ≥0∞} {θ : UnitAddTorus (Fin d)} :
    invFourierSeries (fun x => Complex.ofReal (regularizedG P X r x)) θ =
      ∑' (x : Grid d), regularizedG P X r x • (mFourier x) θ := by
  rfl

variable [IsProbabilityMeasure P]

lemma integral_invFourier_regularizedG_eq {X : ℕ → Ω → Grid d} {r : ℝ≥0} {x : Grid d}
  (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    regularizedG P X (ENNReal.ofNNReal r) x = ((2 * π)^d)⁻¹ * ∫ (θ : UnitAddTorus (Fin d)),
      (mFourier (- x)) θ * invFourierSeries (fun x => Complex.ofReal (regularizedG P X r x)) θ := by

  sorry
  -- rw [integral_invFourierSeries_eq (fun x => Complex.ofReal (regularizedG P X (ENNReal.ofNNReal r) x))]
  -- apply memℓp_gen
  -- simp only [Complex.norm_real, Real.norm_eq_abs, toReal_one, Real.rpow_one, summable_abs_iff]
  -- exact regularizedG_summable P r_lt_one X_mble

open UnitAddTorus Fourier MeasureTheory ENNReal

#check MemLp
#check Lp
#check AEEqFun.mk
#check mFourierBasis
#check HilbertBasis

open scoped lp
lemma memLp_invFourierSeries_regularizedG {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0∞}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    MemLp (invFourierSeries (fun x => Complex.ofReal (regularizedG P X r x))) 2 volume := by
  
  -- rw [memLp_pi_iff]
  sorry

noncomputable
def regularizedG_hat_aux (P : Measure Ω) {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0∞} (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) : ((UnitAddTorus (Fin d)) →ₘ[volume] ℂ) :=
  AEEqFun.mk (invFourierSeries (fun x => Complex.ofReal (regularizedG P X r x))) sorry

noncomputable def regularizedG_hat (P : Measure Ω) {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0∞}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    -- (@Lp (UnitAddTorus (Fin d)) ℂ MeasureSpace.pi.toMeasurableSpace Complex.instNormedAddCommGroup 2 (@volume (UnitAddTorus (Fin d)) MeasureSpace.pi : Measure (UnitAddTorus (Fin d))) : AddSubgroup (UnitAddTorus (Fin d) →ₘ[volume] ℂ)) := sorry
    Lp ℂ 2 (@volume (UnitAddTorus (Fin d)) (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun a ↦ UnitAddCircle) fun i ↦ instMeasureSpaceUnitAddCircle)) := sorry
--  ⟨regularizedG_hat_aux P r_lt_one X_mble, sorry⟩ --memLp_invFourierSeries_regularizedG P r_lt_one X_mble⟩
-- ⟨_, memLp_invFourierSeries_regularizedG P r_lt_one X_mble⟩

variable {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0∞}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t))

#check instMeasureSpaceUnitAddCircle
#check instMeasureSpaceUnitAddCircle.volume
#check AddCircle.measureSpace

example : instMeasureSpaceUnitAddCircle = AddCircle.measureSpace 1 := by sorry

#check (mFourierBasis (d := Fin d)).repr
#check (mFourierBasis (d := Fin d)).repr (regularizedG_hat P r_lt_one X_mble)
#check mFourierBasis.repr.symm ((mFourierBasis (d := Fin d)).repr (regularizedG_hat P r_lt_one X_mble))

variable {r' : ℝ≥0} (r'_lt_one : r' < 1)

#check (mFourierBasis (d := Fin d)).repr.symm ⟨_, regularizedG_square_summable' P r'_lt_one X_mble⟩
#check mFourierBasis.repr ((mFourierBasis (d := Fin d)).repr.symm ⟨_, regularizedG_square_summable' P r'_lt_one X_mble⟩)

-- Hyödyllinen asia
lemma gona1 : mFourierBasis.repr ((mFourierBasis (d := Fin d)).repr.symm ⟨_, regularizedG_square_summable' P r'_lt_one X_mble⟩) = ⟨_, regularizedG_square_summable' P r'_lt_one X_mble⟩ := by simp

lemma gona : mFourierBasis.repr.symm ((mFourierBasis (d := Fin d)).repr (regularizedG_hat P r_lt_one X_mble)) = regularizedG_hat P r_lt_one X_mble := by
  simp
