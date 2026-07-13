import Polya.Convolution

open UnitAddTorus MeasureTheory

noncomputable
local instance : MeasureSpace (Grid d) where
  volume := Measure.count

lemma invFourierSeries_single_eq (x : Grid d) :
    invFourierSeries (Pi.single x (M := fun _ => ℂ) 1) = (mFourier x) := by
  classical
  unfold invFourierSeries
  ext θ
  have (y : Grid d) (hy : y ≠ x) : (Pi.single x 1 y (M := fun _ => ℂ)) • (mFourier y) θ = 0 := by
    rw [Pi.single_apply]
    simp [hy]
  sorry

open scoped lp

lemma norm_invFourierSeries_le_norm
    (f : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (θ : UnitAddTorus (Fin d)) :
    ‖invFourierSeries f θ‖ ≤ ‖(⟨_, hf⟩ : ℓ¹(Grid d, ℂ))‖ := by
  sorry

open scoped Convolution

#check Real.fourier_mul_convolution_eq

lemma convolution_fourier_eq
  (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    invFourierSeries (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g)
    = (invFourierSeries f) * (invFourierSeries g) := by

  sorry

lemma invFourierSeries_eq_of_eq_single_add_convolution {r : ℂ}
    (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) + r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p))) (hp : p ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
  invFourierSeries g = 1 + r • ((invFourierSeries g) * (invFourierSeries p)) := by

  sorry

lemma invFourierSeries_eq_inv_of_eq_single_add_convolution {r : ℂ}
    (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) +
      r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p))) (hp : p ∈ ℓ¹(Grid d, ℂ))
    (hg : g ∈ ℓ¹(Grid d, ℂ)) (p_norm : ‖(⟨_, hp⟩ : ℓ¹(Grid d, ℂ))‖ ≤ 1) (r_lt_one : ‖r‖ < 1) :
    invFourierSeries g = (1 - r • (invFourierSeries p))⁻¹ := by
  sorry
