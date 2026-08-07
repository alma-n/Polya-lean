import Polya.InvFourierSeries
variable {d : ℕ}

open UnitAddTorus MeasureTheory
open scoped lp

#check HilbertBasis.coe_mk
#check mFourierBasis (d := Fin d)
#check UnitAddTorus (Fin d) →ₘ[volume] ℂ

/-- The equivalence class of functions that are almost everywhere equal to `invFourierSeries f` -/
noncomputable
def invFourierSeriesL2_aux (f : Grid d → ℂ) : ((UnitAddTorus (Fin d)) →ₘ[@volume (UnitAddTorus (Fin d)) (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ ↦ UnitAddCircle) fun _ ↦ instMeasureSpaceUnitAddCircle)] ℂ) := AEEqFun.mk (invFourierSeries f) (Measurable.aestronglyMeasurable (invFourierSeries_measurable f))

-- Very annoying
lemma gooona : instMeasureSpaceUnitAddCircle = AddCircle.measureSpace 1 := by
  unfold instMeasureSpaceUnitAddCircle AddCircle.measureSpace
  simp
  congr

/--
If `f ∈ ℓ¹(Grid d, ℂ)` then any representative from `invFourierSeriesL2_aux f` is in
`L²(UnitAddTorus (Fin d), ℂ)`.
-/
lemma invFourierSeriesL2_aux_mem_L2 {f : Grid d → ℂ} (hf_l1 : f ∈ ℓ¹(Grid d, ℂ)) : MemLp (invFourierSeriesL2_aux f) 2 (μ := @volume (UnitAddTorus (Fin d)) (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ ↦ UnitAddCircle) fun _ ↦ instMeasureSpaceUnitAddCircle)) := by
  rw [MemLp]
  unfold invFourierSeriesL2_aux
  constructor
  · apply AEEqFun.aestronglyMeasurable
  · rw [eLpNorm_aeeqFun, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
      invFourierSeries_eq]
    simp only [smul_eq_mul, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
    have (a : UnitAddTorus (Fin d)) : ‖∑' (x : Grid d), f x * (mFourier x) a‖ₑ^2 =  ENNReal.ofNNReal
        (‖(∑' (x : Grid d), f x * (mFourier x) a)^2‖.toNNReal) := by
      simp only [enorm_eq_nnnorm, norm_pow]
      rw [Real.toNNReal_pow (by simp)]
      simp
    simp_rw [this]
    have hf : Integrable (fun a => NNReal.toReal (‖(∑' (x : Grid d), f x * (mFourier x) a)^2‖.toNNReal)) (@volume (UnitAddTorus (Fin d)) MeasureSpace.pi) := by
      simp only [Real.coe_toNNReal', norm_nonneg, sup_of_le_left]
      have := square_integrable_invFourierSeries_of_l1 f hf_l1
      rw [invFourierSeries_eq, ← integrable_norm_iff] at this
      · convert this
      · measurability
    have gona := lintegral_coe_eq_integral _ hf
    suffices (ENNReal.ofReal (∫ (a : UnitAddTorus (Fin d)), ↑‖(∑' (x : Grid d), f x * (mFourier x) a) ^ 2‖.toNNReal)) < ⊤ by
      apply lt_of_eq_of_lt _ this
      rw [← gona]
      congr
      ext n
      exact gooona
    exact ENNReal.ofReal_lt_top

/-- The element of the `L²` space corresponding to `invFourierSeries f` -/
noncomputable
def invFourierSeriesL2 {f : Grid d → ℂ} (hf_l1 : f ∈ ℓ¹(Grid d, ℂ)) :
    Lp ℂ 2 (@volume (UnitAddTorus (Fin d)) ((@MeasureSpace.pi (Fin d) (Fin.fintype d)
      (fun _ ↦ UnitAddCircle) fun _ ↦ instMeasureSpaceUnitAddCircle))) :=
  ⟨invFourierSeriesL2_aux (f := f), Lp.mem_Lp_iff_memLp.mpr (invFourierSeriesL2_aux_mem_L2 hf_l1)⟩

open ENNReal

lemma aeeq_congr2 {E F : Type*} [MeasureSpace E] {f : F → F → F} {g g' h h' : E → F}
  (hg : g =ᵐ[volume] g') (hh : h =ᵐ[volume] h') :
    (fun x => f (g x) (h x)) =ᵐ[volume] fun x => f (g' x) (h' x) := by
  rw [aeEq_iff] at *
  have : {x | f (g x) (h x) ≠ f (g' x) (h' x)} ⊆ {x | g x ≠ g' x} ∪ {x | h x ≠ h' x} := by
    intro x hx
    rw [Set.mem_setOf] at hx
    rw [Set.mem_union]
    by_cases hgx : g x = g' x
    · by_cases hhx : h x = h' x
      · rw [hgx, hhx] at hx
        contradiction
      · right
        simp [hhx]
    · left
      simp [hgx]
  exact Measure.mono_null this (measure_union_null_iff.mpr ⟨hg, hh⟩)

lemma integral_inner_eq_L2_inner (n i : Grid d) :
    ∫ (x : UnitAddTorus (Fin d)), inner ℂ ((mFourier n) x) ((mFourier i) x) =
  inner ℂ (mFourierLp 2 n) (mFourierLp 2 i) := by
  rw [MeasureTheory.L2.inner_def]
  convert integral_congr_ae ?_ <;> try exact gooona
  symm
  apply aeeq_congr2
  · convert UnitAddTorus.coeFn_mFourierLp 2 n
    exact gooona.symm
  · convert UnitAddTorus.coeFn_mFourierLp 2 i
    exact gooona.symm

lemma mFourierBasis_repr_invFourierSeries_eq (f : Grid d → ℂ) (hf_l1 : f ∈ ℓ¹(Grid d, ℂ)) :
    mFourierBasis.repr (invFourierSeriesL2 hf_l1) = ⟨f, lp.monotone (show 1 ≤ 2 by norm_num) hf_l1⟩ := by
  ext n
  unfold invFourierSeriesL2 invFourierSeriesL2_aux
  simp_rw [mFourierBasis_repr, mFourierCoeff, smul_eq_mul]
  have ifs_mble := Measurable.aestronglyMeasurable (invFourierSeries_measurable f) (μ := volume)
  have : ∫ (t : UnitAddTorus (Fin d)), (mFourier (-n)) t * (AEEqFun.mk (invFourierSeries f)
      (μ := volume) ifs_mble) t = ∫ (t : UnitAddTorus (Fin d)), (mFourier (-n)) t *
        (invFourierSeries f) t := by
    apply integral_congr_ae
    suffices (fun a ↦ (AEEqFun.mk (invFourierSeries f) ifs_mble) a) =ᶠ[ae volume]
        fun a ↦invFourierSeries f a by
      exact Set.EqOn.aeEq (fun ⦃x⦄ ↦ congrArg (HMul.hMul ((mFourier (-n)) x))) this
    apply MeasureTheory.AEEqFun.mk_eq_mk.mp (by simp)
    · exact AEEqFun.aestronglyMeasurable (AEEqFun.mk (invFourierSeries f) ifs_mble)
    · exact AEStronglyMeasurable.mono_ac (fun ⦃s⦄ a ↦ a) ifs_mble
  convert this <;> try exact gooona
  simp_rw [invFourierSeries_eq, ← tsum_mul_left, smul_eq_mul, mul_comm (f _), ← mul_assoc, ← smul_eq_mul]
  rw [integral_tsum]
  simp_rw [integral_smul_const, smul_eq_mul, mul_comm, mFourier_neg, ← RCLike.inner_apply]
  have h := orthonormal_iff_ite.mp (HilbertBasis.orthonormal (mFourierBasis (d := Fin d)))
  specialize this
  rw [UnitAddTorus.coe_mFourierBasis] at h
  · simp_rw [integral_inner_eq_L2_inner n, h]
    have : ∀ i : Grid d, i ≠ n → (f i * (if n = i then 1 else 0) = 0) := by
      intro i hi
      simp [hi.symm]
    rw [tsum_eq_single _ this]
    simp
  · intro x
    measurability
  · simp only [smul_eq_mul]
    apply ne_of_lt
    rw [← lintegral_tsum]
    · simp only [enorm_eq_nnnorm, ← norm_toNNReal, norm_mul]
      have hf : ∫⁻ (a : UnitAddTorus (Fin d)), ∑' (i : Grid d), ↑(‖(mFourier (-n)) a‖ * ‖(mFourier i) a‖ * ‖f i‖).toNNReal ≤ ∫⁻ (a : UnitAddTorus (Fin d)), ∑' (i : Grid d), ↑(‖f i‖).toNNReal := by
        apply lintegral_mono
        rw [Pi.le_def]
        intro θ
        apply Summable.tsum_le_tsum <;> try simp
        intro x
        grw [norm_mFourier_le_one, norm_mFourier_le_one, mul_one, one_mul, norm_toNNReal]
      apply lt_of_le_of_lt hf
      simp_rw [norm_toNNReal, lintegral_const, mul_lt_top_iff]
      left
      constructor
      · apply (memℓp_gen_iff (by norm_num)).mp at hf_l1
        simp_all
        suffices ∑' (i : Grid d), ENNReal.ofReal (NNReal.toReal ‖f i‖₊) < ∞ by
          convert this with x
          rw [coe_nnnorm, ofReal_norm, enorm_eq_nnnorm]
        exact Summable.tsum_ofReal_lt_top hf_l1
      · simp
    · intro i
      measurability

theorem mFourierBasis_repr_symm {f : Grid d → ℂ} (hf_l1 : f ∈ ℓ¹(Grid d, ℂ)) :
    invFourierSeriesL2 hf_l1 = mFourierBasis.repr.symm ⟨f, lp.monotone (show 1 ≤ 2 by norm_num)  hf_l1⟩ := by
  have := mFourierBasis_repr_invFourierSeries_eq f hf_l1
  simp [← this]

#check ContinuousMap.toLp (E := ℂ) 2 volume
