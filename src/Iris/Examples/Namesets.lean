/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.ProofMode

public import Iris.Algebra.IProp
public import Iris.Algebra.GenSet

public import Iris.Instances.UPred.Instance
public import Iris.Instances.IProp.Instance

public import Iris.Std.CoPset
public import Iris.Std.GenSets

@[expose] public section

namespace Iris.Examples
open Iris.BI COFE Std LawfulSet

section const_gset

abbrev γ : GType := 1
abbrev gname := Pos

@[simp]
def MySet (S : CoPset) : GenSetDisjO CoPset := GenSetDisj.gen_set_valid S
def SetOwn (S : CoPset) : UPred (GenSetDisjO CoPset) := UPred.ownM (MySet S)

example {x y : gname} : SetOwn {x, y} ⊢ (SetOwn {x} -∗ False) := by
  iintro H1 H2
  istop
  apply (UPred.ownM_op _ _).2.trans
  apply (UPred.ownM_valid _).trans
  apply UPred.ownM_always_invalid_elim
  intro n H
  simp only [MySet, ←CMRA.valid_iff_validN', GenSetDisj.set_disj_valid_op] at H
  apply H x; simp [mem_singleton, mem_insert]

end const_gset

end Iris.Examples
