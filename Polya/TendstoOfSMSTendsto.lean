module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Metrizable.Uniformity

@[expose]
public section

open Topology Filter

variable {α ι : Type*} {f : ι → α} {xs : ℕ → ι} [LinearOrder ι]

noncomputable
def φ {a : ℕ} (h : ∀ n ≥ a, ∃ m > n, xs n < xs m) : ℕ → {n:ℕ // n ≥ a}
  | 0 => ⟨a, by simp⟩
  | n + 1 => ⟨(h (φ h n) (Subtype.prop _)).choose, by
    have := (h (φ h n) (Subtype.prop _)).choose_spec
    grind
  ⟩

lemma φ_spec₁ {a : ℕ} (h : ∀ n ≥ a, ∃ m > n, xs n < xs m) (n : ℕ) : (φ h (n + 1)) > φ h n :=
  (h (φ h n) (Subtype.prop _)).choose_spec.1
lemma φ_spec₂ {a : ℕ} (h : ∀ n ≥ a, ∃ m > n, xs n < xs m) (n : ℕ) : xs (φ h n) < xs (φ h (n + 1)) :=
  (h (φ h n) (Subtype.prop _)).choose_spec.2

lemma φ_strictMono {a : ℕ} (h : ∀ n ≥ a, ∃ m > n, xs n < xs m) : StrictMono (fun n => φ h n) := by
  intro n m hnm
  simp
  induction m with
  | zero => contradiction
  | succ m ih =>
      by_cases hf : n = m
      · rw [hf]
        exact φ_spec₁ h _
      · specialize ih (by grind)
        apply lt_trans ih (φ_spec₁ h _)

lemma xs_φ_strictMono {a : ℕ} (h : ∀ n ≥ a, ∃ m > n, xs n < xs m) :
    StrictMono (xs ∘ (fun n => (φ h n : ℕ))) := by
  intro n m hnm
  simp
  induction m with
  | zero => contradiction
  | succ m ih =>
      by_cases hf : n = m
      · rw [hf]
        exact φ_spec₂ h _
      · specialize ih (by grind)
        apply lt_trans ih (φ_spec₂ h _)

variable {F : Filter α} [TopologicalSpace ι] [ClosedIicTopology ι]

-- This proof is kind of ugly :(
lemma eventually_forall_exists_gt_of_nhdsWithin {x : ι} (hxs : Tendsto xs atTop (𝓝[<] x)) :
  ∃ a, ∀ n ≥ a, ∃ m > n, xs n < xs m := by
    rw [tendsto_nhdsWithin_iff] at hxs
    obtain ⟨hxs, hx⟩ := hxs
    simp only [Set.mem_Iio, eventually_atTop, ge_iff_le] at hx
    obtain ⟨a, ha⟩ := hx
    use a
    intro n hn
    by_contra! hf
    specialize ha n hn
    have := le_of_tendsto hxs (b := xs n)
    simp only [eventually_atTop, ge_iff_le, forall_exists_index] at this
    specialize this n (by grind)
    grind

lemma has_strict_mono_subseq_of_tendsto_nhdsWithin {x : ι} (hxs : Tendsto xs atTop (𝓝[<] x)) :
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (xs ∘ φ) ∧ Tendsto (xs ∘ φ) atTop (𝓝[<] x) := by
    have ⟨a, h⟩ := eventually_forall_exists_gt_of_nhdsWithin hxs
    refine ⟨fun n => φ h n, φ_strictMono h, xs_φ_strictMono h, ?_⟩
    rw [tendsto_iff_seq_tendsto] at hxs
    exact hxs (fun n => φ h n) (StrictMono.tendsto_atTop (φ_strictMono h))

variable [SecondCountableTopology ι]

lemma tendsto_of_strictMono_seq_tendsto {x : ι}
    (hf : ∀ xs : ℕ → ι, StrictMono xs → Tendsto xs atTop (𝓝 x) → (Tendsto (f ∘ xs) atTop F)) :
    Tendsto f (𝓝[<] x) F := by
  apply Filter.tendsto_of_subseq_tendsto
  intro xs hxs
  have ⟨φ, hφ, hp1, hp2⟩ := has_strict_mono_subseq_of_tendsto_nhdsWithin hxs
  specialize hf (xs ∘ φ) hp1 (tendsto_nhds_of_tendsto_nhdsWithin hp2)
  use φ
  exact tendsto_def.mpr hf

end
