module

public import Polya.Defs

public section

open MeasureTheory

variable {d : ℕ} {Ω : Type*}

/-- Another equivalent definition with non-fixed `ξ`, `t` and `ω` -/
lemma RW_def :
    RW = fun (ξ : (t : ℕ) → Ω → Grid d) (t : ℕ) (ω : Ω) ↦ walkOfSteps (fun s ↦ ξ s ω) t := by
  rfl

variable [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The position of a random walk is a random variable (measurable)
if the steps are random variables (measurable). -/
lemma RW.measurable {ξ : (t : ℕ) → Ω → Grid d} (ξ_mble : ∀ t, Measurable (ξ t)) (t : ℕ) :
    Measurable (RW ξ t) := by
  have ξ_mble_t := ξ_mble t
  induction t with
  | zero => exact measurable_const
  | succ n ih =>
    specialize ih (ξ_mble n)
    simp_rw [RW_def, walkOfSteps, Finset.sum_range_succ]
    simp_rw [RW_def, walkOfSteps] at ih
    exact Measurable.add ih (ξ_mble n)

lemma RW2.measurable {ξ : (t : ℕ) → Ω → Grid d} (ξ_mble : ∀ t, Measurable (ξ t)) :
    Measurable (RW2 ξ) := by
  unfold RW2
  rw [measurable_pi_iff]
  intro t
  apply measurable_pi_iff.mpr
  intro x
  have ξ_mble_t := ξ_mble t
  induction t with
  | zero => exact measurable_const
  | succ n ih =>
    specialize ih (ξ_mble n)
    simp_rw [walkOfSteps, Finset.sum_range_succ]
    simp_rw [walkOfSteps] at ih
    exact Measurable.add ih (measurable_pi_iff.mp (ξ_mble n) _)
