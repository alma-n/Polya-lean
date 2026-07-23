module

public import Mathlib

@[expose]
public noncomputable section defs

open MeasureTheory ENNReal UnitAddTorus

/-- The integer grid in `d` dimensions. -/
@[implicit_reducible]
def Grid d := Fin d → ℤ
deriving DecidableEq, MeasurableSpace, MeasurableEq, MeasurableAdd₂, SeminormedAddCommGroup

variable {d : ℕ}

/-- Walk on the grid with a given step sequence `steps`. -/
def walkOfSteps (steps : (t : ℕ) → Grid d) (t : ℕ) : Grid d :=
  ∑ s ∈ Finset.range t, steps s

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Random walk with a given random step sequence `ξ`. -/
def RW (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) : Grid d :=
  walkOfSteps (fun s ↦ ξ s ω) t

def RW2 (ξ : (t : ℕ) → Ω → Grid d) (ω : Ω) (t : ℕ) : Grid d :=
  walkOfSteps (fun s ↦ ξ s ω) t

/-- Regularized occupation of a given walk. -/
def walkRegularizedOccupation (walk : (t : ℕ) → Grid d) (r : ℝ≥0∞) (x : Grid d) :=
  ∑' t, Set.indicator {x} (fun _ ↦ r ^ t) (walk t)

/-- Regularized occupation `L_λ` of a random walk. -/
def regularizedOccupation (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) (ω : Ω) :=
  walkRegularizedOccupation (fun t ↦ X t ω) r x

/-- The regularized Green's function `G_λ(x)` of a random walk. -/
def regularizedG (X : (t : ℕ) → Ω → Grid d) (r : ℝ≥0∞) (x : Grid d) : ℝ :=
  ∫ ω, ENNReal.toReal (regularizedOccupation X r x ω) ∂P

-- Does not seem possible to generalize, since mFourier uses ℂ for some reason.
noncomputable
def invFourierSeries (f : Grid d → ℂ) (θ : UnitAddTorus (Fin d)) : ℂ :=
  ∑' (x : Grid d), f x • (mFourier x) θ

def nnGrid : SimpleGraph (Grid d) where
  Adj x y := ∑ i, |x i - y i| = 1
  symm x y h := by
    grind
  loopless := by
    apply irrefl_def.mpr
    intro x
    simp

instance : DecidableRel (nnGrid (d := d)).Adj := by
  intro a b
  unfold SimpleGraph.Adj
  exact (∑ i, |a i - b i|).decEq 1

noncomputable
def pSRW (x : Grid d) : ℂ := if nnGrid.Adj 0 x then (2 * d)⁻¹ else 0

end defs
