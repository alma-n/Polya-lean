import Mathlib

open MeasureTheory
open Metric
open Filter
open Topology

variable (d : ℕ)

#check Fin d → ℝ
#check (volume : Measure (Fin d → ℝ))
#check (volume : Measure (EuclideanSpace ℝ (Fin d)))
#check EuclideanSpace

section

variable {δ : ℝ} (δ_pos : 0 < δ)
variable (f : (EuclideanSpace ℝ (Fin d)) → ℝ)
variable (f_cont : Continuous f)(f_bdd : ∀ θ, |f θ| ≤ 1) (f_pos : ∀ θ ∈ ball 0 δ, 0 < f θ) (f_zero : f 0 = 1)
variable {c : ℝ} (c_pos : 0 < c)
variable (hf : ∀ θ ∈ ball 0 δ, f θ ≤ 1 - c * ‖θ‖^2)

#check ∫ θ in ball 0 δ, (1 - f θ)⁻¹
#check 𝓝[<](1 : ℝ)

include c_pos hf
lemma f_ae_ne_one : ∀ᵐ θ, f θ ≠ 1 := by
  sorry

lemma fii (r : ℝ) (r_pos : 0 < r) (r_lt_one : r < 1) (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ ball 0 δ) :
    0 < 1 - r * f θ := by
  sorry

include f_cont
lemma foo :
    Tendsto (fun r ↦ ∫ θ in ball 0 δ, (1 - r * f θ)⁻¹) (𝓝[<] 1)
      (𝓝 (∫ θ in ball 0 δ, (1 - f θ)⁻¹)) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro xs hxs
  rw [tendsto_nhdsWithin_iff] at hxs
  obtain ⟨hx1, hx2⟩ := hxs
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun θ ↦ (1 - f θ)⁻¹)
  · intro n
    apply Measurable.aestronglyMeasurable
    measurability
  ·
    sorry
  · intro n
    simp_rw [Set.mem_Iio, eventually_atTop, ge_iff_le] at hx2
    obtain ⟨N, hx2⟩ := hx2
    filter_upwards with a
    sorry
  ·
    sorry



end

section integrability_of_norm_theta

example :
  MeasureTheory.IntegrableOn (fun (θ : EuclideanSpace ℝ (Fin 2)) => ‖θ‖) (Metric.ball 0 t) MeasureTheory.volume := by
    apply (MeasureTheory.integrableOn_fun_norm_addHaar volume (f := id)).mpr
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.add_one_sub_one, pow_one, id_eq,
      smul_eq_mul]
    have : Set.Ioo 0 t ⊆ Set.Ioc 0 t := by grind
    apply MeasureTheory.IntegrableOn.mono_set _ this
    apply Continuous.integrableOn_Ioc
    continuity

#check Real.ball_eq_Ioo

variable {t : ℝ}

lemma not_integrable_d1 (t_pos : 0 < t) :
  ¬ MeasureTheory.IntegrableOn (fun (θ : EuclideanSpace ℝ (Fin 1)) => 1/‖θ‖^(2 : ℝ)) (Metric.ball 0 t) MeasureTheory.volume := by
    apply (MeasureTheory.integrableOn_fun_norm_addHaar volume (f := fun x => 1/x^2)).mp.mt
    simp only [finrank_euclideanSpace, Fintype.card_unique, tsub_self, pow_zero, Real.rpow_ofNat,
      one_div, smul_eq_mul, one_mul]
    suffices ¬IntegrableOn (fun y ↦ y^(-2 : ℝ)) (Set.Ioo 0 t) volume by
      contrapose this
      apply (integrableOn_congr_fun _ _).mp this
      · intro x hx
        have : 0 < x := by grind
        simp_rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt this)]
        simp
      · simp
    simp_rw [intervalIntegral.integrableOn_Ioo_rpow_iff t_pos]
    simp

lemma not_integrable_d2 (t_pos : 0 < t) :
  ¬ MeasureTheory.IntegrableOn (fun (θ : EuclideanSpace ℝ (Fin 2)) => 1/‖θ‖^(2 : ℝ)) (Metric.ball 0 t) MeasureTheory.volume := by
    apply (MeasureTheory.integrableOn_fun_norm_addHaar volume (f := fun x => 1/x^2)).mp.mt
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.add_one_sub_one, pow_one,
      Real.rpow_ofNat, one_div, smul_eq_mul]
    suffices ¬IntegrableOn (fun y ↦ y^(-1 : ℝ)) (Set.Ioo 0 t) volume by
      simp_rw [Real.rpow_neg_one] at this
      grind
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff]
    · simp
    · exact t_pos

#check EuclideanSpace ℝ (Fin d)

lemma nontrivial_Rd (one_le_d : 1 ≤ d) : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
      have gona1 : Nonempty (Fin d) := by
        use 0
        grind
      apply Infinite.instNontrivial

lemma integrable_dn (t_pos : 0 < t) (three_le_d : 3 ≤ d) :
  MeasureTheory.IntegrableOn (fun (θ : EuclideanSpace ℝ (Fin d)) => 1/‖θ‖^2) (Metric.ball 0 t) MeasureTheory.volume := by
    have : 1 ≤ d := by grind
    have ntRd := nontrivial_Rd d this
    apply (MeasureTheory.integrableOn_fun_norm_addHaar volume (f := fun x => 1/x^2)).mpr
    simp only [finrank_euclideanSpace, Fintype.card_fin, one_div, smul_eq_mul]
    suffices IntegrableOn (fun y ↦ y ^((d - 3) : ℝ)) (Set.Ioo 0 t) volume by
      apply (integrableOn_congr_fun _ _).mp this
      · intro x hx
        simp only
        have : 0 < x := by grind
        rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt this), ← Real.rpow_add this]
        simp only [Nat.cast_ofNat, mul_neg, mul_one]
        congr 1
        exact_mod_cast by omega
      · simp
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff]
    · exact_mod_cast by omega
    · exact t_pos

lemma not_integrable_dn (t_pos : 0 < t) (d_le_two : d ≤ 2) (d_ne_zero : d ≠ 0) :
  ¬ (MeasureTheory.IntegrableOn (fun (θ : EuclideanSpace ℝ (Fin d)) => 1/‖θ‖^(2 : ℝ)) (Metric.ball 0 t) MeasureTheory.volume) := by
    by_cases hd : d = 1
    · rw [hd]
      exact not_integrable_d1 t_pos
    · have : d = 2 := by grind
      rw [this]
      exact not_integrable_d2 t_pos

end integrability_of_norm_theta

section

def UpToConstantBoundsEstimateWithin (S : Set ℝ) (f g : ℝ → ℝ) := ∃ a > 0, ∃ b > 0, ∀ x ∈ S, a * f x ≤ g x ∧ g x ≤ b * f x

example : UpToConstantBoundsEstimateWithin Set.univ (fun _ => 1) (fun _ => 2) := by
  use 1
  constructor
  · linarith
  · use 3
    constructor
    · linarith
    · intro x hx
      constructor
      · simp
      · simp
        grind

lemma UpToConstantBoundsEstimateWithin.antitone {S T : Set ℝ} (hst : S ⊆ T) : UpToConstantBoundsEstimateWithin T f g → UpToConstantBoundsEstimateWithin S f g := by
  intro ⟨a, ha, b, hb, h⟩
  refine ⟨a, ha, b, hb, ?_⟩
  intro x hx
  exact h x (hst hx)

lemma UpToConstantBoundsEstimateWithin_cos : UpToConstantBoundsEstimateWithin (Metric.ball (0 : ℝ) (Real.pi / 4)) (fun x => x^2) (fun y => 1 - Real.cos y) := by
  use (1/(2 * Real.sqrt 2))
  constructor
  · simp
  · use 1/2
    constructor
    · linarith
    · intro x hx
      constructor
      · suffices 1 / (2 * √2) * (Real.pi / 4)^ 2 <= 1 - Real.cos x by
          simp only [ge_iff_le]
          apply le_trans (b := 1 / (2 * √2) * (Real.pi / 4)^ 2) _ this
          · have gona : |x| ≤ Real.pi/4 := by
              simp at hx
              grind
            sorry
        sorry
      · sorry



end
