import Polya.IntegralInvFourier
import Polya.RegularizedG

open UnitAddTorus MeasureTheory ENNReal NNReal Convolution

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

lemma invFourier_regularizedG_eq {X : ℕ → Ω → Grid d} {r : ℝ≥0∞} {θ : UnitAddTorus (Fin d)} :
    invFourierSeries (fun x => Complex.ofReal (regularizedG P X r x)) θ =
      ∑' (x : Grid d), regularizedG P X r x • (mFourier x) θ := by
  rfl

variable [IsProbabilityMeasure P]

open UnitAddTorus Fourier MeasureTheory ENNReal

variable {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0∞} {x : Grid d}

noncomputable
def regularizedG_hat (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :=
  invFourierSeriesL2 (regularizedG'_mem_l1 P (ENNReal.toNNReal_lt_of_lt_coe r_lt_one) X_mble)

lemma regularizedG_hat_coe_aeeq_invFourierSeries
  (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    regularizedG_hat P r_lt_one X_mble =ᵐ[volume] (invFourierSeries (fun x => regularizedG P X r x))
      := by
  unfold regularizedG_hat invFourierSeriesL2 invFourierSeriesL2_aux
  simp
  have (x : Grid d) : (regularizedG P X (↑r.toNNReal) x) = (regularizedG P X r x) := by
    congr
    apply coe_toNNReal (LT.lt.ne_top r_lt_one)
  have hf : AEStronglyMeasurable (invFourierSeries fun x ↦ (regularizedG P X r x)) := by
    apply Measurable.aestronglyMeasurable (invFourierSeries_measurable _)
  simp_rw [this]
  convert MeasureTheory.AEEqFun.coeFn_mk (f := invFourierSeries fun x ↦ (regularizedG P X r x)) hf
  exact gooona

lemma integrable_regularizedG_hat (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    Integrable (fun θ => regularizedG_hat P r_lt_one X_mble θ) volume := by
  rw [MeasureTheory.integrable_congr (regularizedG_hat_coe_aeeq_invFourierSeries P r_lt_one X_mble)]
  apply integrable_invFourierSeries_of_l1
  convert regularizedG'_mem_l1 (r := r.toNNReal) P (ENNReal.toNNReal_lt_of_lt_coe r_lt_one) X_mble
  apply (coe_toNNReal (LT.lt.ne_top r_lt_one)).symm

lemma repr_regularizedG_hat_eq (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    mFourierBasis.repr (regularizedG_hat P r_lt_one X_mble) x = regularizedG P X r x := by
  unfold regularizedG_hat
  simp_rw [mFourierBasis_repr_invFourierSeries_eq]
  congr
  apply ENNReal.coe_toNNReal
  apply ne_of_lt
  grw [r_lt_one]
  exact one_lt_top

lemma integral_eq_repr (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∫ (t : UnitAddTorus (Fin d)), (mFourier (-x)) t • (regularizedG_hat P r_lt_one X_mble) t =
      mFourierBasis.repr (regularizedG_hat P r_lt_one X_mble) x := by
  rw [mFourierBasis_repr, mFourierCoeff]
  congr
  ext n
  exact gooona.symm

lemma integral_regularizedG_hat_eq (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∫ (t : UnitAddTorus (Fin d)), (mFourier (-x)) t • (regularizedG_hat P r_lt_one X_mble) t =
      regularizedG P X r x := by
  rw [integral_eq_repr, repr_regularizedG_hat_eq]

lemma integral_regularizedG_hat_re_eq (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∫ (t : UnitAddTorus (Fin d)), ((mFourier (-x)) t • (regularizedG_hat P r_lt_one X_mble) t).re =
      regularizedG P X r x := by
  change ∫ (t : UnitAddTorus (Fin d)), RCLike.re ((mFourier (-x)) t • (regularizedG_hat P r_lt_one
      X_mble) t) = (Complex.ofReal (regularizedG P X r x)).re
  rw [integral_re]
  · rw [integral_regularizedG_hat_eq]
    rfl
  · rw [← integrable_norm_iff]
    · simp
      apply Integrable.mono (g := fun a => ‖(regularizedG_hat P r_lt_one X_mble) a‖)
      · rw [integrable_norm_iff]
        · exact integrable_regularizedG_hat P r_lt_one X_mble
        · measurability
      · measurability
      · apply Filter.Eventually.of_forall
        intro θ
        suffices ‖(mFourier (-x)) θ‖ * ‖(regularizedG_hat P r_lt_one X_mble) θ‖ ≤ 1 * ‖(regularizedG_hat P r_lt_one X_mble) θ‖ by
          simp_all
        apply mul_le_mul <;> try simp
        · exact norm_mFourier_le_one
    . measurability

-- #check instMeasureSpaceUnitAddCircle
-- #check instMeasureSpaceUnitAddCircle.volume
-- #check AddCircle.measureSpace

-- variable {r' : ℝ≥0} (r'_lt_one : r' < 1)

-- Hyödyllinen asia
-- lemma gona1 {X_mble : ∀ t, Measurable (X t)} : mFourierBasis.repr ((mFourierBasis (d := Fin d)).repr.symm ⟨_, regularizedG_square_summable' P r'_lt_one X_mble⟩) = ⟨_, regularizedG_square_summable' P r'_lt_one X_mble⟩ := by simp

-- lemma gona : mFourierBasis.repr.symm ((mFourierBasis (d := Fin d)).repr (regularizedG_hat P r_lt_one X_mble)) = regularizedG_hat P r_lt_one X_mble := by
--   simp
