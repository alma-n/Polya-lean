import Mathlib
import Polya.RegularizedOccupation

open MeasureTheory Topology Filter
open ENNReal NNReal
open BigOperators


#check regularizedG

section Step_Distribution_to_Fourier_Green

variable {d : ℕ} (p : Measure <| Grid d) [IsProbabilityMeasure p] (r : ℝ≥0∞)

section RW_Green_Eq

/--
1 at `0 : Grid d`, 0 otherwise
-/
def δ₀ := Pi.single (0 : Grid d) (M := fun _ => ℝ) 1

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

#check Measure.real
#check ProbabilityTheory.iIndepFun

-- This is the last lemma which works with the whole Ω and P
lemma RW_green_eq
  (ξ : (t : ℕ) → Ω → Grid d) (ξ_meas : ∀ t, Measurable <| ξ t)
  (hξ : ∀ t, P.map (ξ t) = p) -- The probability distribution of each `ξ t` is p
  (hξ2 : ProbabilityTheory.iIndepFun ξ P) -- The steps are independent
  {x : Grid d}
  : regularizedG P (RW ξ) r x = δ₀ x + r.toReal * ∑' z : Grid d, p.real {x - z} * regularizedG P (RW ξ) r z := by
  -- It will be difficult to work with the dependency between `P[X_n = x | X_(n - 1) = z]`
  -- Need Fubini for tsum
  sorry

end RW_Green_Eq

noncomputable section Ghat_eq

open UnitAddTorus

variable {r : ℂ}

#check UnitAddTorus.mFourierCoeff

def Ghat (G : Grid d → ℂ) (θ : UnitAddTorus (Fin d)) : ℂ := ∑' (x : Grid d), G x • mFourier x θ

def phat (p : Grid d → ℂ) (θ : UnitAddTorus (Fin d)) : ℂ := ∑' (x : Grid d), p x • mFourier x θ

-- It's not entirely certain if `FinSupp →₀` is the best design assumption
lemma Ghat_eq (p : Grid d →₀ ℂ) (G : Grid d → ℂ) (h : ∀ x, G x = δ₀ x + r * ∑' z : Grid d, p (x - z) * G z) (θ : UnitAddTorus (Fin d)) :
  Ghat G θ = 1 + r * phat p θ * Ghat G θ := by
  sorry

def p_l1 (p : Grid d →₀ ℂ) : lp (fun (_ : Grid d) ↦ ℂ) 1 := {
  val x := p x
  property := by
    -- Finsupp should give this
    sorry
  }


lemma norm_phat_le_norm (p : lp (fun (_ : Grid d) ↦ ℂ) 1) : eLpNorm (phat p) ∞ ≤ ‖p‖ₑ := by
  sorry


-- Use with `(phat_memLp p).toLp : ↥(Lp E p μ)`
lemma phat_memLp (p : lp (fun (_ : Grid d) ↦ ℂ) 1) : MemLp (phat p) ∞ := by
  constructor
  · sorry
  · -- ‖p‖ₑ must be finite
    sorry

#check Lp
#check MemLp.toLp

-- This specializes with (g = Ghat G)
lemma ghat_eq_2 (hr : ‖r‖ < 1) (p : lp (fun (_ : Grid d) ↦ ℂ) 1) (hp : ‖p‖ ≤ 1)
  (g : UnitAddTorus (Fin d) → ℂ)
  (θ)
  (h : g θ = 1 + r * phat p θ * g θ)
  : g θ = 1 / (1 - r * phat p θ) := by
  sorry

end Ghat_eq

-- Gᵣ(x) = δ x 0 + ∑ (p ⋆ Gᵣ)(x)

end Step_Distribution_to_Fourier_Green

-- Split the integral to low and high frequency

section Fourier_Green_to_LowFreq_Asymptotics



end Fourier_Green_to_LowFreq_Asymptotics


section LowFreq_Asymptotics_to_Divergence



end LowFreq_Asymptotics_to_Divergence


section LowFreq_Asymptotics_to_Convergence



end LowFreq_Asymptotics_to_Convergence
