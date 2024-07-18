import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

open MeasureTheory ENNReal NNReal BigOperators

noncomputable section

-- #check ℝ≥0∞


-- setup
abbrev Grid d := Fin d → ℤ

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

variable {d : ℕ}

variable
  (ξ : (t : ℕ) → Ω → Grid d)
  (ξ_mble : ∀ t, Measurable (ξ t))

/-
## Random walk
-/
def RW (t : ℕ) : Ω → Grid d := ∑ s < t, ξ s

lemma RW.measurable (t : ℕ) : Measurable (RW ξ t) := sorry

-- #check measurable_add

-- #check (RW ξ 4) ⁻¹' {0}

/-
## Regularized occupation `L_λ`
-/
def regularizedOccupation (r : ℝ≥0∞) (x : Grid d) (ω : Ω) :=
  ∑' t, r ^ t * Set.indicator ((RW ξ t) ⁻¹' {x}) (Function.const _ 1) ω

lemma regularizedOccupation.measurable (r : ℝ≥0∞) (x : Grid d) :
  Measurable <| regularizedOccupation ξ r x := sorry

def regularizedG (r : ℝ≥0∞) (x : Grid d) : ℝ :=
  ∫ ω, ENNReal.toReal (regularizedOccupation ξ r x ω) ∂P

-- #check integral_prod

lemma tsum_regularizedG_eq_tsum (r : ℝ≥0) (h : r < 1) :
  ∑' x, regularizedG P ξ r x = ∑' t, r ^ t * (∫ ω, ∑' x, Set.indicator ((RW ξ t) ⁻¹' {x}) (Function.const _ (1 : ℝ)) ω ∂P) :=
  -- convert integral_prod
  sorry
