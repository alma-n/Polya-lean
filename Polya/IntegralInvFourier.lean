import Polya.InvFourierSeries
variable {d : ℕ}

open UnitAddTorus MeasureTheory
open scoped lp

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)
variable {f : Grid d → ℂ} (hf : f ∈ ℓ²(Grid d, ℂ))

#check HilbertBasis.coe_mk
#check mFourierBasis (d := Fin d)
#check UnitAddTorus (Fin d) →ₘ[volume] ℂ

noncomputable
abbrev fhat : ((UnitAddTorus (Fin d)) →ₘ[@volume (UnitAddTorus (Fin d)) (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ ↦ UnitAddCircle) fun _ ↦ instMeasureSpaceUnitAddCircle)] ℂ) := AEEqFun.mk (invFourierSeries f) (Measurable.aestronglyMeasurable (invFourierSeries_measurable f))

-- Wrong way to do this
-- include hf in
-- lemma fhat_mem_L2 : MemLp (fhat (f := f)) 2 (μ := @volume (UnitAddTorus (Fin d)) (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ ↦ UnitAddCircle) fun _ ↦ instMeasureSpaceUnitAddCircle)) := by
--   rw [MemLp]
--   unfold fhat
--   constructor
--   · apply AEEqFun.aestronglyMeasurable
--   · rw [eLpNorm_aeeqFun, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
--       invFourierSeries_eq]
--     simp only [smul_eq_mul, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
--     have (a : UnitAddTorus (Fin d)) : ‖∑' (x : Grid d), f x * (mFourier x) a‖ₑ^2 =  ENNReal.ofNNReal
--         (‖(∑' (x : Grid d), f x * (mFourier x) a)^2‖.toNNReal) := by
--       simp only [enorm_eq_nnnorm, norm_pow]
--       rw [Real.toNNReal_pow (by simp)]
--       simp
--     simp_rw [this]
--     have hf : Integrable (fun a => NNReal.toReal (‖(∑' (x : Grid d), f x * (mFourier x) a)^2‖.toNNReal)) (@volume (UnitAddTorus (Fin d)) MeasureSpace.pi) := by
--       simp only [Real.coe_toNNReal', norm_nonneg, sup_of_le_left]
--       -- Neliöintegroituvuus
--       sorry
--     have gona := lintegral_coe_eq_integral _ hf
--     suffices (ENNReal.ofReal (∫ (a : UnitAddTorus (Fin d)), ↑‖(∑' (x : Grid d), f x * (mFourier x) a) ^ 2‖.toNNReal)) < ⊤ by
--       apply lt_of_eq_of_lt _ this
--       rw [← gona]
--       congr
--       ext n
--       unfold instMeasureSpaceUnitAddCircle AddCircle.measureSpace
--       simp
--       rfl
--     exact ENNReal.ofReal_lt_top

lemma gooona : instMeasureSpaceUnitAddCircle = AddCircle.measureSpace 1 := by
  unfold instMeasureSpaceUnitAddCircle AddCircle.measureSpace
  simp
  congr

-- lemma invFourierSeries_eq_mFourierBasis_repr (f : Grid d → ℂ) (hf : f ∈ ℓ²(Grid d, ℂ)) :
--     mFourierBasis.repr ⟨fhat (f := f), Lp.mem_Lp_iff_memLp.mpr (fhat_mem_L2 hf)⟩ = ⟨f, hf⟩ := by
--   ext n
--   unfold fhat
--   simp_rw [mFourierBasis_repr, mFourierCoeff, smul_eq_mul]
--   have ifs_mble := Measurable.aestronglyMeasurable (invFourierSeries_measurable f) (μ := volume)
--   have : ∫ (t : UnitAddTorus (Fin d)), (mFourier (-n)) t * (AEEqFun.mk (invFourierSeries f)
--       (μ := volume) ifs_mble) t = ∫ (t : UnitAddTorus (Fin d)), (mFourier (-n)) t *
--         (invFourierSeries f) t := by
--     apply integral_congr_ae
--     suffices (fun a ↦ (AEEqFun.mk (invFourierSeries f) ifs_mble) a) =ᶠ[ae volume]
--         fun a ↦invFourierSeries f a by
--       exact Set.EqOn.aeEq (fun ⦃x⦄ ↦ congrArg (HMul.hMul ((mFourier (-n)) x))) this
--     apply MeasureTheory.AEEqFun.mk_eq_mk.mp (by simp)
--     · exact AEEqFun.aestronglyMeasurable (AEEqFun.mk (invFourierSeries f) ifs_mble)
--     · exact AEStronglyMeasurable.mono_ac (fun ⦃s⦄ a ↦ a) ifs_mble
--   convert this <;> try exact gooona
--   -- UnitAddTorus.hasSum_mFourier_series_of_summable
--   sorry

-- theorem mFourierBasis_repr_symm (f : Grid d → ℂ) (hf : f ∈ ℓ²(Grid d, ℂ)) :
--     ⟨fhat (f := f), Lp.mem_Lp_iff_memLp.mpr (fhat_mem_L2 hf)⟩ = mFourierBasis.repr.symm ⟨f, hf⟩ := by
--   have := invFourierSeries_eq_mFourierBasis_repr f hf
--   simp [← this]

#check ContinuousMap.toLp (E := ℂ) 2 volume

-- I think this is what I want to proof
theorem invFourier_aeeq_mFourierBasis_repr_symm (f : Grid d → ℂ) (hf : f ∈ ℓ²(Grid d, ℂ)) :
    invFourierSeries f =ᵐ[volume] mFourierBasis.repr.symm ⟨f, hf⟩ := by
  unfold mFourierBasis
  sorry


-- lemma integral_invFourierSeries_eq (f : Grid d → ℂ) (hf : f ∈ ℓ¹(Grid d, ℂ)) (x : Grid d) :
--     f x = ((2 * π)^d)⁻¹ * ∫ (θ : UnitAddTorus (Fin d)),
--       (mFourier (-x)) θ * invFourierSeries f θ := by
--   rw [invFourierSeries_eq]
--   dsimp only
--   simp_rw [← tsum_mul_left, smul_eq_mul]
--   conv =>
--     enter [2, 2, 2, θ, 1, y]
--     rw [mul_comm, mul_assoc, ← mFourier_add]
--   have (θ : UnitAddTorus (Fin d)) : ∑' (y : Grid d), f y * (mFourier (y + -x)) θ =
--       ∑' (z : Grid d), f (z + x) * (mFourier z) θ := by
--     let e : Grid d ≃ Grid d := {
--         toFun := fun y => y + x
--         invFun := fun y => y - x
--         left_inv _ := by norm_num
--         right_inv _ := by norm_num
--     }
--     have := e.tsum_eq (f := fun y => f y * (mFourier (y + -x)) θ)
--     rw [← this]
--     unfold e
--     simp
--   conv =>
--     enter [2, 2, 2, θ]
--     rw [this]
--   rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
--   simp_rw [smul_eq_mul, ← tsum_mul_right]
--   rw [MeasureTheory.integral_tsum]
--   · conv =>
--       enter [2, 1, z, 2, θ]
--       rw [mul_comm, ← mul_assoc, mul_comm, ←smul_eq_mul]
--     simp_rw [integral_smul_const, smul_eq_mul, mul_comm]

--     sorry
--   · intro i
--     apply Measurable.aestronglyMeasurable
--     measurability
--   ·
--     sorry
