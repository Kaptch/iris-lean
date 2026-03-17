/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.Algebra.Monoid
import Iris.Std.List
import Iris.Std.PartialMap
import Iris.Std.GenSets

namespace Iris.Algebra

/-! # Big Operators

This file defines big operators (fold operations) at the abstract OFE level.
These are parameterized by a monoid operation and include theorems about their properties.
-/

open OFE
open Iris.Std

def bigOpS {A : Type _} [DecidableEq A] {S : Type _} [OFE M] (op : M → M → M) {unit : M}
  [MonoidOps op unit] (Φ : A → M) [LawfulFiniteSet S A] (m : S) : M :=
  Set.fold (fun acc x => op acc (Φ x)) (by intro S' x y; simp only; rw [<-MonoidOps.op_comm]) unit m

/-- Big op over set without index: `[^ op set] x ∈ l, P` -/
scoped syntax atomic("[^") term " set]" ident " ∈ " term ", " term : term

scoped macro_rules
  | `([^ $o set] $x ∈ $l, $P) => `(bigOpS $o (fun _ $x => $P) $l)

end Iris.Algebra
