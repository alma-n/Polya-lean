module

public import Mathlib.Tactic
public import Polya.Defs

open MeasureTheory

public section

variable {d : ℕ}

-- The integer grid in `d` dimensions is countable. -/
instance : Countable (Grid d) := inferInstanceAs (Countable (Fin d → ℤ)) -- instCountableForallOfFinite

noncomputable
instance : MeasureSpace (Grid d) where
  volume := Measure.count

instance : FunLike (Grid d) (Fin d) ℤ where
  coe := id
  coe_injective' := Function.injective_id

@[ext] lemma Grid.ext (x y : Grid d) (h : (∀ i, x i = y i)) : x = y := funext h

end
