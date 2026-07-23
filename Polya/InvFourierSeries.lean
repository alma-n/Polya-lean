import Polya.Convolution

open UnitAddTorus MeasureTheory

variable {d : ℕ}

notation "π" => Real.pi

lemma invFourierSeries_eq {f : Grid d → ℂ} :
    invFourierSeries f = fun θ => ∑' (x : Grid d), f x • (mFourier x) θ :=
  rfl

lemma invFourierSeries_eq' {f : Grid d → ℂ} (θ : UnitAddTorus (Fin d)) :
    invFourierSeries f θ = ∑' (x : Grid d), f x • (mFourier x) θ :=
  rfl

lemma invFourierSeries_single_eq (x : Grid d) :
    invFourierSeries (Pi.single x (M := fun _ => ℂ) 1) = (mFourier x) := by
  rw [invFourierSeries_eq]
  ext θ
  have (y : Grid d) (hy : y ≠ x) : (Pi.single x 1 y (M := fun _ => ℂ)) • (mFourier y) θ = 0 := by
    simp [hy]
  rw [tsum_eq_single x this, Pi.single_eq_same, smul_eq_mul, one_mul]

lemma norm_mFourier_le_one {x : Grid d} {θ : UnitAddTorus (Fin d)} :
    ‖(mFourier x) θ‖ ≤ 1 := by
  unfold mFourier
  simp

open scoped lp

lemma summable_invFourier {θ : UnitAddTorus (Fin d)} {f : Grid d → ℂ} (hf : f ∈ ℓ¹(Grid d, ℂ)) :
    Summable (fun x => ‖f x • (mFourier x) θ‖) := by
  have := (memℓp_gen_iff (by norm_num)).mp hf
  simp_all
  apply Summable.of_nonneg_of_le ?_ ?_ this
  · intro x
    rw [← norm_mul]
    exact norm_nonneg _
  · intro x
    apply mul_le_of_le_one_right (norm_nonneg (f x)) (norm_mFourier_le_one)

lemma summable_invFourier' {θ : UnitAddTorus (Fin d)} {f : Grid d → ℂ} (hf : f ∈ ℓ¹(Grid d, ℂ)) :
    Summable (fun x => f x * (mFourier x) θ) := by
  rw [← summable_norm_iff]
  simp_rw [← smul_eq_mul]
  exact summable_invFourier hf

lemma norm_invFourierSeries_le_norm
    (f : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (θ : UnitAddTorus (Fin d)) :
    ‖invFourierSeries f θ‖ ≤ ‖(⟨_, hf⟩ : ℓ¹(Grid d, ℂ))‖ := by
  have f_summable := (memℓp_gen_iff (by norm_num)).mp hf
  simp at f_summable
  rw [invFourierSeries_eq, lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [smul_eq_mul, ENNReal.toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true,
    div_self]
  suffices ∑' (x : Grid d), ‖f x * (mFourier x) θ‖ ≤ ∑' (i : Grid d), ‖f i‖ by
    exact le_trans' this (norm_tsum_le_tsum_norm (summable_invFourier hf))
  simp
  apply Summable.tsum_le_tsum ?_ ?_ f_summable
  · intro i
    apply mul_le_of_le_one_right (norm_nonneg (f i)) (norm_mFourier_le_one)
  · simp_rw [← norm_mul]
    apply summable_invFourier hf

-- This might belong in a different file
lemma integral_invFourierSeries_eq (f : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (x : Grid d) :
    f x = ((2 * π)^d)⁻¹ * ∫ (θ : UnitAddTorus (Fin d)), (mFourier (-x)) θ * invFourierSeries f θ := by
  rw [invFourierSeries_eq]
  dsimp only
  simp_rw [← tsum_mul_left]
  sorry

open scoped Convolution

#check Real.fourier_mul_convolution_eq

lemma fourier_convolution_eq (f g : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    invFourierSeries (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] g)
    = (invFourierSeries f) * (invFourierSeries g) := by
  ext θ
  simp_rw [invFourierSeries_eq, convolution_eq_tsum _ _ hf hg]
  simp
  simp_rw [← tsum_mul_right]
  -- This should not be neccesary, but rw [mFourierAdd] does not work
  have (x y : Grid d) : mFourier (x + y) θ = mFourier x θ * mFourier y θ := by
    exact @mFourier_add (Fin d) (Fin.fintype d) y θ x
  conv =>
    enter [1, 1, x, 1, z]
    rw [show mFourier x = mFourier (x - z + z) by simp, this (x - z) z]
    tactic =>
      suffices f z * g (x - z) * ((mFourier (x - z)) θ * (mFourier z) θ) = (f z * (mFourier z) θ) *
          (g (x - z) * ((mFourier (x - z)) θ)) by
        exact this
      grind
  rw [Summable.tsum_comm]
  · simp_rw [tsum_mul_left]
    congr
    ext z
    congr 1
    let e : Grid d ≃ Grid d := {
        toFun := fun x => x - z
        invFun := fun x => x + z
        left_inv x := by norm_num
        right_inv x := by norm_num
    }
    exact e.tsum_eq (f := fun x => g x * (mFourier x) θ)
  · change Summable (fun (x : Grid d × Grid d) => ((fun (z : Grid d × Grid d) ↦
      f z.1 *(mFourier z.1) θ * (g z.2 * (mFourier  z.2) θ)) ∘ (fun (x : Grid d × Grid d) =>
        (x.1, x.2 - x.1))) x)
    apply Summable.comp_injective
    · have gonaf : Summable (fun z => ‖f z * (mFourier z) θ‖) := by
        simp_rw [← smul_eq_mul]
        exact summable_invFourier hf
      have gonag : Summable  (fun z => ‖g z * (mFourier z) θ‖) := by
        simp_rw [← smul_eq_mul]
        exact summable_invFourier hg
      have := summable_mul_of_summable_norm gonaf gonag
      exact this
    · intro x y h
      simp at h
      grind

lemma invFourierSeries_eq_of_eq_single_add_convolution {r : ℂ}
    (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) +
      r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p)))
    (hp : p ∈ ℓ¹(Grid d, ℂ)) (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    invFourierSeries g = 1 + r • ((invFourierSeries g) * (invFourierSeries p)) := by
  simp_rw [invFourierSeries_eq]
  ext θ
  nth_rw 1 [h]
  simp only [smul_eq_mul, Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.mul_apply]
  rw [← mul_assoc, ← Summable.tsum_mul_left _ (summable_invFourier' hp)]
  · simp_rw [add_mul]
    have : ∑' (x : Grid d), (Pi.single 0 (M := fun _ => ℂ) 1) x * (mFourier x) θ = (1 : ℂ) := by
      have : ∀ (y : Grid d), y ≠ 0 → (Pi.single 0 (M := fun _ => ℂ) 1) y * (mFourier y) θ = 0 := by
        intro y hy
        simp [hy]
      rw [tsum_eq_single 0 this, show mFourier (0 : Grid d) = 1 by exact mFourier_zero,
        Pi.single_eq_same, ContinuousMap.one_apply, mul_one]
    · nth_rw 2 [← this]
      rw [Summable.tsum_add]
      · congr 1
        simp_rw [mul_assoc]
        rw [Summable.tsum_mul_left, Summable.tsum_mul_left _ (Summable.mul_left _
          (summable_invFourier' hp))]
        · congr 1
          simp_rw [← smul_eq_mul]
          rw [← invFourierSeries_eq', ← invFourierSeries_eq']
          simp_rw [smul_eq_mul]
          rw [Summable.tsum_mul_left _ (summable_invFourier' hp)]
          · simp_rw [← smul_eq_mul, ← invFourierSeries_eq', smul_eq_mul]
            have := fourier_convolution_eq g p hg hp
            simp [this]
        · rw [← summable_norm_iff]
          simp_rw [← smul_eq_mul]
          exact summable_invFourier (convolution_summable _ _ hg hp)
      · apply summable_of_ne_finset_zero (s := {0})
        intro b hb
        rw [Finset.mem_singleton] at hb
        simp [hb]
      · simp_rw [mul_assoc]
        apply Summable.mul_left _ (summable_invFourier' (convolution_summable _ _ hg hp))

lemma invFourierSeries_eq_inv_of_eq_single_add_convolution {r : ℂ}
    (g p : Grid d → ℂ) (h : g = ((Pi.single 0 (M := fun _ => ℂ) 1) +
      r • (g ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] p))) (hp : p ∈ ℓ¹(Grid d, ℂ))
    (hg : g ∈ ℓ¹(Grid d, ℂ)) :
    invFourierSeries g = (1 - r • (invFourierSeries p))⁻¹ := by
  have := invFourierSeries_eq_of_eq_single_add_convolution _ _ h hp hg
  have : invFourierSeries g - r • (invFourierSeries g * invFourierSeries p) = 1 := by
    rw [sub_eq_of_eq_add this]
  simp_rw [← Algebra.smul_mul_assoc] at this
  have : invFourierSeries g * (1 - r • invFourierSeries p) = 1 := by
    rw [mul_sub, mul_one, Algebra.mul_smul_comm, ← Algebra.smul_mul_assoc]
    exact this
  exact (inv_eq_of_mul_eq_one_left this).symm
