/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Iris.Std.FiniteSet
import Std.Data.ExtHashSet
import Std.Data.ExtTreeSet

/-! ## LawfulSet Instances

This file provides `LawfulSet` instances for Lean's standard library set implementations:

* `ExtTreeSet`
* `ExtHashSet`

These instances allow these types to be used with the abstract set interface
defined in `FiniteSet.lean`.
-/

namespace Iris.Std

open Iris.Std.Set

/-! ### ExtHashSet Instance -/

namespace ExtHashSet

variable {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

instance : Union (Std.ExtHashSet α) where
  union := Std.ExtHashSet.union

instance : Inter (Std.ExtHashSet α) where
  inter := Std.ExtHashSet.inter

instance : SDiff (Std.ExtHashSet α) where
  sdiff := Std.ExtHashSet.diff

instance : Filter α (Std.ExtHashSet α) where
  filter s φ := Std.ExtHashSet.filter φ s

instance : Set (Std.ExtHashSet α) α where

instance [LawfulBEq α] :
    LawfulSet (Std.ExtHashSet α) α where
  ext X Y h := Std.ExtHashSet.ext_mem h
  mem_empty := Std.ExtHashSet.not_mem_empty
  singleton_insert := Std.ExtHashSet.singleton_eq_insert.symm
  mem_insert_eq := by
    intro s x y heq
    subst heq
    exact Std.ExtHashSet.mem_insert_self
  mem_insert_ne := by
    intro s x y hne
    simp; grind only
  mem_union := Std.ExtHashSet.mem_union_iff
  mem_inter := Std.ExtHashSet.mem_inter_iff
  mem_diff := Std.ExtHashSet.mem_diff_iff
  mem_filter := by
    intro X φ x
    simp only [Filter.filter, Std.ExtHashSet.mem_filter]
    constructor
    · intro ⟨h1, h2⟩; simp at h2; exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩; simp; exact ⟨h1, h2⟩

-- {1, 2} = {2, 1}, yet hash set doesn't have a canonical ordering. interface should output lists quoted by permutation
-- instance : FiniteSet (Std.ExtHashSet α) α where

end ExtHashSet

/-! ### ExtTreeSet Instance -/

namespace ExtTreeSet

variable {α : Type _} {cmp : α → α → Ordering} [Std.TransCmp cmp]

instance : Union (Std.ExtTreeSet α cmp) where
  union := Std.ExtTreeSet.union

instance : Inter (Std.ExtTreeSet α cmp) where
  inter := Std.ExtTreeSet.inter

instance : SDiff (Std.ExtTreeSet α cmp) where
  sdiff := Std.ExtTreeSet.diff

instance : Filter α (Std.ExtTreeSet α cmp) where
  filter s φ := Std.ExtTreeSet.filter φ s

instance : Set (Std.ExtTreeSet α cmp) α where

instance [Std.LawfulEqCmp cmp] :
    LawfulSet (Std.ExtTreeSet α cmp) α where
  ext X Y h := Std.ExtTreeSet.ext_mem h
  mem_empty := Std.ExtTreeSet.not_mem_empty
  singleton_insert := Std.ExtTreeSet.singleton_eq_insert
  mem_insert_eq := by
    intro s x y heq
    subst heq
    exact Std.ExtTreeSet.mem_insert_self
  mem_insert_ne := by
    intro s x y hne
    simp; grind only
  mem_union := Std.ExtTreeSet.mem_union_iff
  mem_inter := Std.ExtTreeSet.mem_inter_iff
  mem_diff := Std.ExtTreeSet.mem_diff_iff
  mem_filter := by
    intro X φ x
    simp only [Filter.filter, Std.ExtTreeSet.mem_filter]
    constructor
    · intro ⟨h1, h2⟩; simp at h2; exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩; simp; exact ⟨h1, h2⟩

instance : FiniteSet (Std.ExtTreeSet α cmp) α where
  toList s := s.toList

instance [Std.LawfulEqCmp cmp] : LawfulFiniteSet (Std.ExtTreeSet α cmp) α where
  mem_toList := Std.ExtTreeSet.mem_toList
  toList_noDup := by
    intro m
    have e := Std.ExtTreeSet.distinct_toList (t := m)
    simp only [List.Nodup]
    have heq : (fun x1 x2 => x1 ≠ x2) = (fun a b => ¬cmp a b = Ordering.eq) := by
      ext x1 x2; simp
    rw [heq]
    apply e

end ExtTreeSet

end Iris.Std
