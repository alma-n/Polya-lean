module

public import Mathlib.Tactic
public import Polya.Defs

-- The integer grid in `d` dimensions is countable. -/
lemma Grid.countable {d : ℕ} : Countable (Grid d) := instCountableForallOfFinite

