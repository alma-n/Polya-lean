import Polya.InvFourierSeries
import Polya.RegularizedG

open scoped lp

variable {d : ℕ}

lemma nnGrid.adj_iff {x y : Grid d} : nnGrid.Adj x y ↔ ∑ (i : Fin d), |x i - y i| = 1 := by
  with_unfolding_all rfl

lemma ncard_eq_ncard {n : ℕ} (x : Grid (n + 1)) :
    {w : Grid (n + 1) | |x 0 - w 0| = 0 ∧ ∑ (i : Fin n) , |x i.succ - w i.succ| = 1}.ncard =
      {w : Grid n | ∑ i, |x i.succ - w i| = 1}.ncard := by
  apply Set.ncard_congr'
  exact {
    toFun hw := ⟨fun (i : Fin n) => hw.val i.succ, by
      rw [Set.mem_setOf]
      exact hw.prop.2⟩
    invFun hw := ⟨fun (i : Fin (n + 1)) => if hi : i = 0 then x 0 else hw.val (i.pred hi), by
      rw [Set.mem_setOf]
      simp
      exact hw.prop⟩
    left_inv := by
      intro h
      ext i
      simp only [Set.mem_setOf_eq, Fin.succ_pred, dite_eq_ite, ite_eq_right_iff]
      intro hi
      subst i
      have := h.prop.1
      simp at this
      grind
    right_inv := by
      intro h
      ext i
      simp
  }

lemma ncard_addSet_eq_two {n : ℕ} (x : Grid (n + 1)) :
    {w : Grid (n + 1) | |x 0 - w 0| = 1 ∧ ∑ (i : Fin n), |x i.succ - w i.succ| = 0}.ncard = 2 := by
  have {w : Grid (n + 1)} : |x 0 - w 0| = 1 ∧ ∑ (i : Fin n), |x i.succ - w i.succ| = 0 ↔
      w = (fun (j : Fin (n + 1)) => if j = 0 then x 0 + 1 else x j) ∨
      w = (fun (j : Fin (n + 1)) => if j = 0 then x 0 - 1 else x j) := by
    constructor
    · intro h
      have : w 0 = x 0 + 1 ∨ w 0 = x 0 - 1 := by
        grind
      have h0 : ∀ j : Fin (n + 1), j ≠ 0 → w j = x j := by
        intro j hj
        rw [Finset.sum_eq_zero_iff_of_nonneg] at h
        · have := h.2 (j.pred hj) (by simp)
          simp at this
          grind
        · grind
      cases this with
      | inl h1 =>
          left
          ext j
          grind
      | inr h1 =>
          right
          ext j
          grind
    · intro h
      cases h with | inl h => simp [h] | inr h => simp [h]
  rw [Set.ext_iff.mpr @this]
  change Set.ncard ({w | _} ∪ {w | _}) = _
  have := ncard_eq_ncard x
  rw [Set.ncard_union_eq _ _ _]
  · simp
  · grind
  · simp
  · simp

lemma nnGrid.neighborSet_ncard_eq (x : Grid d) : (nnGrid.neighborSet x).ncard = 2 * d := by
  simp_rw [SimpleGraph.neighborSet, nnGrid.adj_iff]
  induction d with
  | zero =>
      simp
  | succ n ih =>
      simp_rw [Fin.sum_univ_succ]
      specialize @ih (fun i => x i.succ)
      have gona {w : Grid (n + 1)} : |x 0 - w 0| + ∑ (i : Fin n), |x i.succ - w i.succ| = 1 ↔
        (|x 0 - w 0| = 0 ∧ ∑ (i : Fin n), |x i.succ - w i.succ| = 1) ∨ (|x 0 - w 0| = 1 ∧ ∑ (i : Fin n), |x i.succ - w i.succ| = 0) := by
          rw [← Finset.abs_sum_of_nonneg' (by simp)]
          grind
      simp_rw [gona]
      change ({w : Grid (n + 1) | |x 0 - w 0| = 0 ∧ ∑ (i : Fin n), |x i.succ - w i.succ| = 1} ∪ {w : Grid (n + 1) |  |x 0 - w 0| = 1 ∧ ∑ (i : Fin n), |x i.succ - w i.succ| = 0}).ncard = 2 * (n + 1)
      have := ncard_addSet_eq_two x
      rw [Set.ncard_union_eq _ _ _]
      · rw [ncard_eq_ncard x, ih]
        congr
      · grind
      · rw [← ncard_eq_ncard x] at ih
        by_cases hn : n = 0
        · subst n
          simp
        · apply Set.finite_of_ncard_ne_zero
          grind
      · apply Set.finite_of_ncard_ne_zero
        grind

noncomputable
local instance : SimpleGraph.LocallyFinite (nnGrid (d := d)) := by
  intro x
  apply Set.Finite.fintype
  have := nnGrid.neighborSet_ncard_eq x
  by_cases hd : d = 0
  · have : Grid 0 ≃ Fin 1 := by
      unfold Grid
      apply Fintype.equivFinOfCardEq Fintype.card_unique
    have : Finite (Grid 0) := by
      rw [this.finite_iff]
      exact Finite.of_subsingleton
    subst d
    apply (Finite.Set.subset .univ)
    simp
  · apply Set.finite_of_ncard_ne_zero
    grind


lemma zero_of_single_ge_sum_nonneg {i : Fin d} {x : Grid d}
  (h : ∑ (j : Fin d), |x j| = 1) (hf : 1 ≤ |x i|) :
    ∀ j : Fin d, i ≠ j → |x j| = 0 := by
  intro j hj
  by_contra hxj
  have : 0 < |x j| := by grind
  have : |x i| < ∑ k, |x k| := by
    apply Finset.single_lt_sum hj.symm (f := fun k => |x k|)
      (Finset.mem_univ i) (Finset.mem_univ j) this
    intro k hk hkf
    simp
  rw [h] at this
  have := lt_of_le_of_lt hf this
  contradiction



/-- θ ↦ (e^(2π * i * θ) + e^(-2π * i * θ))/2 (=cos(2π θ)) -/
noncomputable
def UnitAddCircle.cos (θ : UnitAddCircle) := 2⁻¹ * ((AddCircle.homeomorphCircle'
  (AddCircle.homeomorphAddCircle _ _ (by norm_num) (by norm_num) θ) : ℂ) +
  (starRingEnd _) ((AddCircle.homeomorphCircle' (AddCircle.homeomorphAddCircle _ _ (by norm_num) (by norm_num) θ)) : ℂ))

-- Original definition with Complex.cos. This does an extra exponentiation, which is wrong.
-- θ ↦ cos(2π θ)
-- noncomputable
-- def UnitAddCircle.cos' (θ : UnitAddCircle) := Complex.cos (AddCircle.equivAddCircle 1 (2 * π) (by simp) (by simp) θ)

lemma neighborSet_zero_eq :
    nnGrid.neighborFinset (0 : Grid d) = Finset.biUnion (Finset.univ : Finset (Fin d))
      (fun i => {Pi.single i (M := fun _ => ℤ) 1, -Pi.single i (M := fun _ => ℤ) 1}) := by
  ext x
  constructor
  · intro h
    simp_all [nnGrid.adj_iff, Pi.zero_apply _, zero_sub, abs_neg]
    have : ∃ i : Fin d, x i ≠ 0 := by
      by_contra hf
      push Not at hf
      have : ∑ (j : Fin d), |x j| = 0 := by simp [hf]
      grind
    obtain ⟨i, hi⟩ := this
    use i
    have gona := zero_of_single_ge_sum_nonneg h (show 1 ≤ |x i| by exact Int.one_le_abs hi)
    by_cases hf : |x i| = 1
    · rw [abs_eq (by norm_num)] at hf
      cases hf with
      | inl hf =>
          left
          ext n
          rw [Pi.single_apply]
          grind
      | inr hf =>
          right
          ext n
          simp [Pi.single_apply]
          grind
    · have two_le_xi : 2 ≤ |x i| := by
        grind
      have : ∑ (j : Fin d), |x j| = |x i| := by
        rw [Finset.sum_eq_single i]
        · exact fun b a c ↦ (fun {a} ↦ Rat.intCast_eq_zero_iff.mp)
            (congrArg Int.cast (gona b (Ne.symm c)))
        · simp
      rw [h] at this
      rw [this] at hf
      contradiction
  · intro h
    simp_all
    obtain ⟨i, hi⟩ := h
    simp_rw [nnGrid.adj_iff, Pi.zero_apply _, zero_sub, abs_neg]
    cases hi with
    | inl h =>
        simp_rw [h]
        suffices ∑ j, Pi.single i (1 : ℤ) j = 1 by
          grind
        rw [Finset.sum_pi_single']
        simp
    | inr h =>
        simp_rw [h]
        suffices ∑ j, Pi.single i (1 : ℤ) j = 1 by
          simp
          grind
        simp [Finset.sum_pi_single']

open UnitAddTorus


lemma two_cos_eq {n : Fin d} {θ : UnitAddTorus (Fin d)} :
    (mFourier (Pi.single n 1)) θ + (mFourier (-Pi.single n 1)) θ = 2 * (θ n).cos := by
  rw [mFourier_neg, mFourier_single, fourier_apply, one_smul]
  induction (θ n) using Quotient.inductionOn with | h θn =>
  rw [AddCircle.toCircle_apply_mk]
  unfold UnitAddCircle.cos
  simp
  congr
  · push_cast
    grind
  · push_cast
    grind

lemma invFourierSeries_pSRW (θ : UnitAddTorus (Fin d)) :
    invFourierSeries pSRW θ = (d : ℂ)⁻¹ * ∑ i, ((θ i).cos : ℂ) := by
  rw [invFourierSeries_eq']
  unfold pSRW
  change ∑' (x : Grid d), (if x ∈ nnGrid.neighborSet 0 then (2 * ↑d : ℂ)⁻¹ else 0) • (UnitAddTorus.mFourier x) θ = _
  rw [tsum_eq_sum (s := nnGrid.neighborFinset 0)]
  · suffices ∑ b ∈ nnGrid.neighborFinset 0, (2 * d : ℂ)⁻¹ • (mFourier b) θ = (d : ℂ)⁻¹*
        ∑ i, (θ i).cos by
      rw [SimpleGraph.neighborFinset_def]
      rw [← this, ← Finset.sum_attach]
      nth_rw 2 [← Finset.sum_attach]
      congr
      ext x
      have := x.prop
      grind
    simp_rw [smul_eq_mul, ← Finset.mul_sum, mul_inv_rev, mul_assoc]
    congr
    apply GroupWithZero.mul_right_injective (two_ne_zero)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel_left₀, Finset.mul_sum]
    rw [neighborSet_zero_eq, Finset.sum_biUnion]
    · congr
      ext n
      rw [Finset.sum_insert, Finset.sum_singleton]
      · exact two_cos_eq
      · intro hf
        rw [Finset.mem_singleton] at hf
        apply congrFun at hf
        specialize hf n
        simp at hf
    · rintro i - j - hf
      simp
      constructor <;> constructor <;>
        · intro h
          apply congrFun at h
          specialize h i
          simp [hf] at h
  · intro x hx
    simp_all

lemma pSRW_mem_lp_one (d_ne_zero : d ≠ 0) : pSRW ∈ ℓ¹(Grid d, ℂ) := by
  apply memℓp_gen
  simp only [ENNReal.toReal_one, Real.rpow_one, summable_norm_iff]
  apply summable_of_hasFiniteSupport
  unfold pSRW Function.HasFiniteSupport Function.support
  simp [d_ne_zero]
  change (nnGrid.neighborSet 0).Finite
  exact Set.toFinite (nnGrid.neighborSet 0)

-- I don't think this is needed
-- lemma norm_pSRW (d_ne_zero : d ≠ 0) :
--     ‖(⟨pSRW, pSRW_mem_lp_one d_ne_zero⟩ : ℓ¹(Grid d, ℂ))‖ = 1 := by
--   sorry

open Convolution MeasureTheory NNReal

variable {Ω : Type*} [MeasureSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/--The Fourier transform of the r-regularized Green function of a simple random walk-/
lemma invFourierSeries_regularizedG_SRW
  {θ : UnitAddTorus (Fin d)} {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0}
  (d_ne_zero : d ≠ 0) (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t))
  (h_simple : ∀ (x : Grid d), Complex.ofReal (regularizedG P X r x) =
    (Pi.single 0 (M := fun _ => ℂ) 1) x + (r •(((fun x => Complex.ofReal (regularizedG P X r x))
      ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] pSRW)) x) ) :
    invFourierSeries (fun x => Complex.ofReal (regularizedG P X r x)) θ =
      (1 - r • ((d : ℂ)⁻¹ * ∑ i,  ((θ i).cos : ℂ)))⁻¹ := by
  rw [invFourierSeries_eq_inv_of_eq_single_add_convolution (r := Complex.ofReal (NNReal.toReal r)) (fun x => Complex.ofReal (regularizedG P X r x)) pSRW, ← invFourierSeries_pSRW]
  · rfl
  · ext x
    rw [h_simple]
    rfl
  · exact pSRW_mem_lp_one d_ne_zero
  · have := regularizedG_summable P r_lt_one X_mble
    apply memℓp_gen
    simp [summable_abs_iff]
    exact this
