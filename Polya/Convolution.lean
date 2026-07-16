import Polya.Grid

open MeasureTheory
open scoped lp Convolution

section convolution

variable {d : ℕ}

lemma convolution_summable (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    f ⋆[ContinuousLinearMap.lsmul ℂ ℂ] g ∈ ℓ¹(Grid d, ℂ) := by
  apply memℓp_gen
  apply (memℓp_gen_iff (by norm_num)).mp at hf
  apply (memℓp_gen_iff (by norm_num)).mp at hg
  simp_rw [ENNReal.toReal_one, Real.rpow_one, ← integrable_count_iff] at *
  apply Integrable.integrable_convolution _ hf hg

lemma convolution_eq_tsum (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    f ⋆[ContinuousLinearMap.lsmul ℂ ℂ] g = (fun x => ∑' (z : Grid d), (f z) * (g (x - z))) := by
  ext x
  simp_rw [convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [integral_countable]
  · rw [show volume = Measure.count by rfl]
    simp
  · rw [show volume = Measure.count by rfl, integrable_count_iff]
    simp_rw [norm_mul]
    let h := fun w => g (x - w)
    have hh : h ∈ ℓ¹(Grid d, ℂ) := by
      apply memℓp_gen
      apply (memℓp_gen_iff (by norm_num)).mp at hg
      simp only [ENNReal.toReal_one, Real.rpow_one, summable_norm_iff] at *
      exact Summable.comp_injective hg sub_right_injective
    apply lp.summable_mul (f := ⟨f, (lp.monotone (show 1 ≤ 2 by norm_num) hf)⟩)
      (g := ⟨h, (lp.monotone (show 1 ≤ 2 by norm_num) hh)⟩)
    exact Real.HolderConjugate.two_two
