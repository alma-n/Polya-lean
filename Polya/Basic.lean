import Mathlib.Topology.Instances.ENNReal
import Mathlib.Tactic.DeriveFintype

open Set
noncomputable section

-- #check ENNReal

-- #check ENNReal.summable

class RandomVariable (α : Type) where
  P (a : α) : ENNReal
  sum_to_one : (∑' a, P a) = 1

inductive Silmaluku where
  | Yksi
  | Kaksi
  | Kolme
  | Nelja
  | Viisi
  | Kuusi
deriving Fintype, DecidableEq

def Silmaluku.todnak (_sl : Silmaluku) : ENNReal := 1/6

def Silmaluku.todnak_ne_zero (sl : Silmaluku) : sl ∈ {x | x.todnak ≠ 0} := by
  rw [mem_setOf]
  cases sl <;> rw [todnak] <;> intro c <;> norm_num at c <;> contradiction

theorem Silmaluku.todnak.finite : (Function.support Silmaluku.todnak).Finite :=
  toFinite (Function.support todnak)

theorem Silmaluku.todnak.summable : Summable (todnak) := by
  rw [Summable]
  use ∑ b : Silmaluku, b.todnak
  intro sx hs
  rw [Filter.atTop]
  apply hasSum_fintype
  convert hs
--   rw [Set.finite_def]
--   constructor
--   constructor
--   case elems =>
--     constructor
--     case val =>
--       rw [Multiset]
--       rw [Function.support]
--       exact Quotient.mk' [
--         {val := Yksi, property := todnak_ne_zero _ },
--         {val := Kaksi, property := todnak_ne_zero _ }
--       ]
--     case nodup =>
--       constructor
--       · intro a
--         intro ha
--         rw [Function.support] at a
--         intro c
--         rename_i gona
--         subst gona
--         contradiction
--       · rw [List.pairwise_iff]
--         right
--         use {val := Yksi, property := todnak_ne_zero _ }
--         use [{val := Kaksi, property := todnak_ne_zero _ }]
--         constructor
--         · intro a ha
--           intro c
--           rw [List.mem_singleton] at ha
--           subst a
--           have := congrArg Subtype.val c
--           contradiction
--         · constructor
--           · constructor
--             intro a ha
--             contradiction
--           · sorry -- gona
--   case complete =>
--     intro x
--     simp
--     sorry

instance : Decidable (Function.support Silmaluku.todnak).Finite :=
  isTrue Silmaluku.todnak.finite

instance Silmaluku.gona : RandomVariable Silmaluku where
  P := Silmaluku.todnak
  sum_to_one := by
    rw [tsum_def, dif_pos]
    case hc => exact Silmaluku.todnak.summable
    rw [if_pos]
    case hc => exact Silmaluku.todnak.finite
    rw [finsum_def]
    rw [dif_pos]
    case hc => exact Silmaluku.todnak.finite
    have :
        Silmaluku.todnak.finite.toFinset = [Yksi, Kaksi, Kolme, Nelja, Viisi, Kuusi].toFinset := by
      ext x
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      cases x <;>
      · exact Finset.insert_eq_self.mp (by rfl)
      cases x <;>
      · simp only [Finite.toFinset_setOf, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [todnak] at *
        norm_num
        exact ne_of_beq_false rfl
    rw [Finset.sum, this]
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, Finset.insert_val,
      Finset.singleton_val, Multiset.mem_singleton, not_false_eq_true, Multiset.ndinsert_of_not_mem,
      Multiset.mem_cons, or_self, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton]
    repeat rw [todnak]
    ring_nf
    norm_num
    rw [ENNReal.inv_mul_cancel]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    exact ne_of_beq_false rfl
