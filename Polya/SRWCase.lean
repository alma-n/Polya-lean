import Polya.Convolution

open scoped lp

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
def UnitAddCircle.cos (θ : UnitAddCircle) := Complex.cos (AddCircle.homeomorphCircle'
  (AddCircle.homeomorphAddCircle _ _ (by norm_num) (by norm_num) θ))

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
