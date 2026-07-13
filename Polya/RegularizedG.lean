module

public import Polya.RegularizedOccupation
public import Polya.TendstoOfSMSTendsto

public section

open MeasureTheory ENNReal Filter Topology

variable {d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

lemma regularizedG_eq {X : ℕ → Ω → Grid d} {r : ℝ≥0∞} {x : Grid d} :
    regularizedG P X r x = ∫ ω, ENNReal.toReal (regularizedOccupation X r x ω) ∂P :=
  rfl

variable [IsProbabilityMeasure P]

open NNReal

lemma enorm_toReal_eq_coe_norm_toNNReal {a : ℝ≥0∞} :
    ‖(a).toReal‖ₑ = ‖(a).toReal‖.toNNReal := by
  rw [Real.enorm_of_nonneg]
  · simp only [Real.norm_eq_abs, abs_toReal, toNNReal_toReal_eq]
    apply ENNReal.ofReal_eq_coe_nnreal
  · simp

lemma tsum_regularizedG_eq_lintegral_tsum {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x = (∫ ω, ∑' x, ∑' t,
    Set.indicator ((X t) ⁻¹' {x}) (fun _ ↦ (r : ℝ) ^ t) ω ∂P) := by
  simp_rw [regularizedG_eq]
  rw [← integral_tsum]
  · congr
    ext ω
    congr
    ext x
    rw [regularizedOccupation_eq]
    simp only
    rw [ENNReal.tsum_toReal_eq]
    · congr
      ext n
      norm_cast
    · intro n
      norm_cast
      exact coe_ne_top
  · intro i
    apply Measurable.aestronglyMeasurable
    apply Measurable.ennreal_toReal
    apply regularizedOccupation.measurable X_mble
  · simp_rw [enorm_toReal_eq_coe_norm_toNNReal]
    apply ne_of_lt
    apply lt_of_le_of_lt (tsum_lintegral_norm_regularizedOccupation_le P X_mble r)
    simp [r_lt_one]

section

open SummationFilter

variable {α β : Type*} [CommMonoid α] [TopologicalSpace α]

@[to_additive]
theorem hasProd_ite_eq' (b : β) [DecidablePred (b = ·)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' ↦ if b = b' then a else 1) a L := by
  convert hasProd_single b (hf := fun b' hb' ↦ if_neg hb'.symm) (L := L)
  exact (if_pos rfl).symm

@[to_additive (attr := simp)]
theorem tprod_ite_eq' (b : β) [DecidablePred (b = ·)] (a : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b = b' then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

end

/-- A summability criterion for a slightly generalized version of walk occupations. -/
lemma summable_weighted_occupation {walk : (t : ℕ) → Grid d} {g : ℕ → ℝ}
    (g_abssummable : ∑' t, ENNReal.ofReal |g t| ≠ ∞) :
    Summable (Function.uncurry
      fun (t : ℕ) (x : Grid d) ↦ Set.indicator {x} (fun _↦ g t) (walk t)) := by
  classical
  apply ENNReal.tsum_coe_ne_top_iff_summable.mp at g_abssummable
  apply Summable.of_abs
  rw [summable_prod_of_nonneg]
  · simp only [Function.uncurry_apply_pair]
    · constructor
      · intro t
        simp_rw [Set.indicator_apply, Set.mem_singleton_iff, abs_ite, abs_zero]
        use |g t|
        apply hasSum_ite_eq'
      · have (x : ℕ) : ∑' (y : Grid d), |Set.indicator {y} (fun x_1 ↦ g x) (walk x)| = |g x| := by
          unfold Set.indicator
          simp_rw [abs_ite, abs_zero, Set.mem_singleton_iff, tsum_ite_eq']
        simp_rw [this]
        apply NNReal.summable_coe.mpr at g_abssummable
        simp only [Real.toNNReal_abs, Real.coe_nnabs] at g_abssummable
        exact g_abssummable
  · intro ⟨t, x⟩
    simp only [Function.uncurry_apply_pair, Pi.zero_apply, Set.indicator_singleton, abs_nonneg]

/-- A summability criterion for (basically) regularized walk occupations. -/
lemma summable_regularized_occupation {walk : (t : ℕ) → Grid d} {r : ℝ≥0} (r_lt_one : r < 1) :
    Summable (Function.uncurry
      fun (t : ℕ) (x : Grid d) ↦ Set.indicator {x} (fun _ ↦ (r : ℝ) ^ t) (walk t)) := by
  apply summable_weighted_occupation
  simp only [abs_pow, NNReal.abs_eq, zero_le_coe, ofReal_pow, ofReal_coe_nnreal,
  ENNReal.tsum_geometric, ne_eq, inv_eq_top]
  exact_mod_cast by simpa [NNReal.sub_def]

lemma tsum_regularizedG_eq {X : (t : ℕ) → Ω → Grid d} {r : ℝ≥0}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    ∑' x, regularizedG P X r x = (1 - r)⁻¹ := by
-- Tada! The first line of equalities of the main proof will be completed here!
  simp_rw [regularizedG_eq]
  rw [← integral_tsum]
  · have := tsum_toReal_regularizedOccupation_eq X r_lt_one
    simp_rw [this]
    simp
  · intro x
    apply Measurable.aestronglyMeasurable
    exact (regularizedOccupation.measurable X_mble r x).ennreal_toReal
  · simp_rw [enorm_toReal_eq_coe_norm_toNNReal]
    apply ne_of_lt
    apply lt_of_le_of_lt (tsum_lintegral_norm_regularizedOccupation_le P X_mble _)
    simp [r_lt_one]


lemma lt_of_strict_mono_tendsto {x : ℝ≥0∞} {xs : ℕ → ℝ≥0∞}
    (hx : 0 < x) (hx1 : StrictMono xs) (hx2 : Tendsto xs atTop (𝓝 x)) :
    ∀ n, xs n < x := by
  intro n
  by_contra hf
  unfold StrictMono at hx1
  rw [tendsto_atTop'] at hx2
  have := lt_of_le_of_lt (not_lt.mp hf) (hx1 (a := n) (b := n + 1) (by norm_num))
  have ⟨a, ha⟩ := hx2 (Set.Ico 0 (xs (n + 1))) (?_)
  by_cases h : a ≤ (n + 1)
  · specialize ha (n + 1) h
    simp at ha
  · specialize ha a (by norm_num)
    have := hx1 (a := n + 1) (b := a) (by grind)
    simp at ha
    exact (lt_self_iff_false _).mp (lt_trans this ha)
  · rw [mem_nhds_iff]
    refine ⟨Set.Ioo 0 (xs (n + 1)), Set.Ioo_subset_Ico_self, isOpen_Ioo, ⟨hx, this⟩⟩

lemma regularizedG_tendsto {X : ℕ → Ω → Grid d} (X_mble : ∀ t, Measurable (X t)) :
    Tendsto (fun r ↦ ENNReal.ofReal (regularizedG P X r 0)) (𝓝[<] 1)
      (𝓝 (∫⁻ ω,(regularizedOccupation (d := d) X 1 0 ω) ∂P)) := by
  apply tendsto_of_strictMono_seq_tendsto
  intro rs hr1 hr2
  simp_rw [regularizedG_eq]
  have (r : ℝ≥0∞) (hr : r < 1) : ENNReal.ofReal (∫ (ω : Ω), (regularizedOccupation X r 0 ω).toReal ∂P) = (∫⁻ (ω : Ω), (regularizedOccupation X r 0 ω) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · congr
      ext ω
      exact ofReal_toReal_eq_iff.mpr (ne_of_lt (regularizedOccupation_lt _ hr _ _))
    · exact regularizedOccupation_integrable P X_mble hr _
    · apply Eventually.of_forall
      simp
  have rs_lt_one := lt_of_strict_mono_tendsto (x := 1) (xs := rs) (by norm_num) hr1 hr2
  change Tendsto (fun n ↦ ENNReal.ofReal (∫ (ω : Ω), (regularizedOccupation X (rs n) 0 ω).toReal ∂P)) _ _
  simp_rw [this _ (rs_lt_one _)]
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact Measurable.aemeasurable (regularizedOccupation.measurable X_mble (rs n) 0)
  · apply Eventually.of_forall
    intro x a b hab
    apply regularizedOccupation_apply_mono
    exact StrictMono.monotone hr1 hab
  · apply Eventually.of_forall
    intro ω
    have rs_tendsto_lt : Tendsto rs atTop (𝓝[<] 1) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · exact hr2
      · apply Eventually.of_forall
        intro n
        exact Set.mem_Iio.mpr (rs_lt_one n)
    apply regularizedOccupation_apply_tendsto_of_monotone X (StrictMono.monotone hr1) rs_tendsto_lt 0

-- TODO make this less ugly (these should probably be in the GreenFourier file)
lemma regularizedG_summable {r : ℝ≥0} {X : (t : ℕ) → Ω → Grid d}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    Summable (regularizedG P X r) := by
  have := tsum_regularizedG_eq P r_lt_one X_mble
  by_contra hf
  rw [tsum_def] at this
  simp_all
  have gona : 0 < 1 - r := by
    simp [r_lt_one]
  apply ne_of_lt at gona
  apply gona
  exact_mod_cast this

open scoped lp

lemma regularizedG_square_summable {r : ℝ≥0} {X : ℕ → Ω → Grid d}
    (r_lt_one : r < 1) (X_mble : ∀ t, Measurable (X t)) :
    regularizedG P X r ∈ ℓ²(Grid d, ℝ) := by
  apply lp.monotone one_le_two
  apply memℓp_gen
  simp only [Real.norm_eq_abs, toReal_one, Real.rpow_one]
  exact Summable.abs (regularizedG_summable P r_lt_one X_mble)
