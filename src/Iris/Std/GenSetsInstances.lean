/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Iris.Std.GenSets
import Std.Data.ExtTreeSet
import Iris.Std.CoPset

/-! ## LawfulSet Instances -/

namespace Iris.Std

open Iris.Std.Set

/-! ### ExtTreeSet Instance -/

namespace ExtTreeSet

variable {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp]

instance : Union (Std.ExtTreeSet α cmp) where
  union := Std.ExtTreeSet.union

instance : Inter (Std.ExtTreeSet α cmp) where
  inter := Std.ExtTreeSet.inter

instance : SDiff (Std.ExtTreeSet α cmp) where
  sdiff := Std.ExtTreeSet.diff

instance : Set (Std.ExtTreeSet α cmp) α where

theorem mem_singleton_extTreeSet [Std.LawfulEqCmp cmp] {x y : α} :
    x ∈ ({y} : Std.ExtTreeSet α cmp) ↔ x = y := by
  simp only [Std.ExtTreeSet.singleton_eq_insert, Std.ExtTreeSet.mem_insert,
    Std.LawfulEqCmp.compare_eq_iff_eq, Std.ExtTreeSet.not_mem_empty, or_false]
  apply Iff.intro <;> rintro ⟨⟩ <;> rfl

instance [Std.LawfulEqCmp cmp] :
    LawfulSet (Std.ExtTreeSet α cmp) α where
  ext _ _ h := Std.ExtTreeSet.ext_mem h
  mem_empty := Std.ExtTreeSet.not_mem_empty
  mem_singleton := mem_singleton_extTreeSet
  mem_union := Std.ExtTreeSet.mem_union_iff
  mem_inter := Std.ExtTreeSet.mem_inter_iff
  mem_diff := Std.ExtTreeSet.mem_diff_iff

instance [Std.LawfulEqCmp cmp] : FiniteSet (Std.ExtTreeSet α cmp) α where
  toList s := s.toList

instance [Std.LawfulEqCmp cmp] : LawfulFiniteSet (Std.ExtTreeSet α cmp) α where
  mem_toList := Std.ExtTreeSet.mem_toList
  toList_nodup := by
    intro m
    have e := Std.ExtTreeSet.distinct_toList (t := m)
    simp only [List.Nodup]
    have heq : (fun x1 x2 => x1 ≠ x2) = (fun a b => ¬cmp a b = Ordering.eq) := by
      ext x1 x2; simp
    rw [heq]
    apply e

end ExtTreeSet

/-! ### CoPset Instance -/

namespace CoPset

instance : Set CoPset Pos where

instance : LawfulSet CoPset Pos where
  ext _ _ h := CoPset.ext h
  mem_empty := CoPset.mem_empty
  mem_singleton := CoPset.in_singleton
  mem_union := CoPset.in_union
  mem_inter := CoPset.in_inter
  mem_diff := CoPset.in_diff

end CoPset

end Iris.Std
