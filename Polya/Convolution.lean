import Mathlib
import Polya.RegularizedOccupation

open MeasureTheory
open UnitAddTorus
open scoped lp
open scoped ENNReal
open scoped Convolution

section convolution

noncomputable
local instance : MeasureSpace (Grid d) where
  volume := Measure.count
-- #synth MeasurableSingletonClass (Grid d)

variable {d : ℕ}

lemma convolution_summable
    (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    f ⋆[ContinuousLinearMap.lsmul ℂ ℂ] g ∈ ℓ¹(Grid d, ℂ) := by
  apply memℓp_gen
  apply (memℓp_gen_iff (by norm_num)).mp at hf
  apply (memℓp_gen_iff (by norm_num)).mp at hg
  simp_rw [ENNReal.toReal_one, Real.rpow_one, ← integrable_count_iff] at *
  apply Integrable.integrable_convolution _ hf hg


lemma convolution_eq_tsum
    (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    f ⋆[ContinuousLinearMap.lsmul ℂ ℂ] g = (fun x => ∑' (z : Grid d), (f z) * (g (x - z))) := by
  apply (memℓp_gen_iff (by norm_num)).mp at hf
  apply (memℓp_gen_iff (by norm_num)).mp at hg
  simp_all
  ext x
  rw [convolution]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [integral_countable]
  · congr
    ext z
    conv =>
      enter [1, 1, 1]
      change Measure.count
    simp
  · conv =>
      enter [2]
      change Measure.count
    rw [integrable_count_iff]


    sorry

#check UnitAddTorus.mFourierCoeff

end convolution

section

variable {d : ℕ}

noncomputable
local instance : MeasureSpace (Grid d) where
  volume := Measure.count

-- TODO yleistä ℂ johonkin vektoriavaruuteen
noncomputable
abbrev invFourierSeries (f : Grid d → ℂ) (θ : UnitAddTorus (Fin d)) : ℂ :=
  ∑' (x : Grid d), f x • (mFourier x) θ

#check Pi.normedRing
-- Väärä normi :(

lemma invFourierSeries_single_eq (x : Grid d) : invFourierSeries (Pi.single x (M := fun _ => ℂ) 1) = (mFourier x) := by
  classical
  unfold invFourierSeries
  ext θ
  have (y : Grid d) (hy : y ≠ x) : (Pi.single x 1 y (M := fun _ => ℂ)) • (mFourier y) θ = 0 := by
    rw [Pi.single_apply]
    simp [hy]

  sorry

#check lp
variable {z : ℝ}
#check abs z

lemma norm_invFourierSeries_le_norm
    (f : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (θ : UnitAddTorus (Fin d)) :
    ‖invFourierSeries f θ‖ ≤ ‖(⟨_, hf⟩ : ℓ¹(Grid d, ℂ))‖ := by

  sorry


-- lemma invFourierSeries_single : invFourierSeries δ₀ = fun θ => 1 := by sorry

#check Real.fourier_mul_convolution_eq

lemma convolution_fourier_eq
  (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    invFourierSeries (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g) = (invFourierSeries f) * (invFourierSeries g) := by
  sorry

lemma invFourierSeries_eq_of_eq_single_add_convolution {r : ℂ}
    (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) + r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p))) (hp : p ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
  invFourierSeries g = 1 + r • ((invFourierSeries g) * (invFourierSeries p)) := by

  sorry

lemma invFourierSeries_eq_inv_of_eq_single_add_convolution {r : ℂ}
    (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) + r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p))) (hp : p ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) (p_norm : ‖(⟨_, hp⟩ : ℓ¹(Grid d, ℂ))‖ ≤ 1) (r_lt_one : ‖r‖ < 1) :
    invFourierSeries g = (1 - r • (invFourierSeries p))⁻¹ := by
  sorry

end

section srw

variable {d : ℕ}

def nnGrid : SimpleGraph (Grid d) where
  Adj x y := ∑ i, |x i - y i| = 1
  symm x y h := by
    grind
  loopless := by
    apply irrefl_def.mpr
    intro x
    simp

local instance : DecidableRel (nnGrid (d := d)).Adj := by sorry

noncomputable
def pSRW (x : Grid d) : ℂ := if nnGrid.Adj 0 x then (2 * d)⁻¹ else 0

variable {θ : UnitAddTorus (Fin 37)}

#check θ 5
#check AddCircle.homeomorphAddCircle
#check AddCircle.homeomorphCircle' (AddCircle.homeomorphAddCircle _ _ (by norm_num) (by norm_num) (θ 5))

/-- θ ↦ cos(2π θ) -/
noncomputable
def UnitAddCircle.cos (θ : UnitAddCircle) :=
  AddCircle.homeomorphCircle' (AddCircle.homeomorphAddCircle _ _ (by norm_num) (by norm_num) θ)

lemma invFourierSeries_pSRW (θ : UnitAddTorus (Fin d)) :
    invFourierSeries pSRW θ = (d : ℂ)⁻¹ * ∑ i, ((θ i).cos : ℂ) := by
  sorry

lemma pSRW_mem_lp_one : pSRW ∈ ℓ¹(Grid d, ℂ) := by sorry

lemma norm_pSRW (d_ne_zero : d ≠ 0) :
    ‖(⟨pSRW, pSRW_mem_lp_one⟩ :ℓ¹(Grid d, ℂ))‖ = 1 := by
  sorry

-- lemma invFourierSeries_regularizedG_pSRW_eq {r : ℂ}
--     (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) + r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p))) (hp : p ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) (p_norm : ‖(⟨_, hp⟩ : ℓ¹(Grid d, ℂ))‖ ≤ 1) (r_lt_one : ‖r‖ < 1) :
--     invFourierSeries g = (1 - r • (invFourierSeries p))⁻¹ := by
--   sorry

end srw
