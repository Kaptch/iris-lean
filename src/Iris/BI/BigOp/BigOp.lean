/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Sergei Stepanenko
-/
import Iris.Algebra.BigOp
import Iris.BI.DerivedLaws
import Iris.Std.PartialMap
import Iris.Std.GenSets

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open OFE
open BIBase

/-! # BI-Instantiated Big Operators over Lists
- `bigSepL`: Big separating conjunction `[∗list]`
- `bigAndL`: Big conjunction `[∧list]`
- `bigOrL`: Big disjunction `[∨list]`
-/

section List
/-! ## Core Definitions -/

/-- Big separating conjunction over a list with index access.
    `bigSepL Φ l` computes `Φ 0 l[0] ∗ Φ 1 l[1] ∗ ... ∗ Φ (n-1) l[n-1]` -/
abbrev bigSepL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL sep Φ l

/-- Big conjunction over a list with index access.
    `bigAndL Φ l` computes `Φ 0 l[0] ∧ Φ 1 l[1] ∧ ... ∧ Φ (n-1) l[n-1]` -/
abbrev bigAndL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL and Φ l

/-- Big disjunction over a list with index access.
    `bigOrL Φ l` computes `Φ 0 l[0] ∨ Φ 1 l[1] ∨ ... ∨ Φ (n-1) l[n-1]` -/
abbrev bigOrL [BI PROP] {A : Type _} (Φ : Nat → A → PROP) (l : List A) : PROP :=
  bigOpL or Φ l

/-! ## Notation -/

-- Notation for bigSepL without index
syntax atomic("[∗list]") ident " ∈ " term ", " term : term
-- Notation for bigSepL with index
syntax atomic("[∗list]") ident " ↦ " ident " ∈ " term ", " term : term
-- Notation for bigSepL2 without index (two lists)
syntax atomic("[∗list]") ident ";" ident " ∈ " term ";" term ", " term : term
-- Notation for bigSepL2 with index (two lists)
syntax atomic("[∗list]") ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

-- Notation for bigAndL without index
syntax atomic("[∧list]") ident " ∈ " term ", " term : term
-- Notation for bigAndL with index
syntax atomic("[∧list]") ident " ↦ " ident " ∈ " term ", " term : term

-- Notation for bigOrL without index
syntax atomic("[∨list]") ident " ∈ " term ", " term : term
-- Notation for bigOrL with index
syntax atomic("[∨list]") ident " ↦ " ident " ∈ " term ", " term : term

macro_rules
  | `([∗list] $x:ident ∈ $l, $P) => `(bigSepL (fun _ $x => $P) $l)
  | `([∗list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigSepL (fun $k $x => $P) $l)
  | `([∧list] $x:ident ∈ $l, $P) => `(bigAndL (fun _ $x => $P) $l)
  | `([∧list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigAndL (fun $k $x => $P) $l)
  | `([∨list] $x:ident ∈ $l, $P) => `(bigOrL (fun _ $x => $P) $l)
  | `([∨list] $k:ident ↦ $x:ident ∈ $l, $P) => `(bigOrL (fun $k $x => $P) $l)

-- iprop macro rules
macro_rules
  | `(iprop([∗list] $x:ident ∈ $l, $P)) => `(bigSepL (fun _ $x => iprop($P)) $l)
  | `(iprop([∗list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigSepL (fun $k $x => iprop($P)) $l)
  | `(iprop([∧list] $x:ident ∈ $l, $P)) => `(bigAndL (fun _ $x => iprop($P)) $l)
  | `(iprop([∧list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigAndL (fun $k $x => iprop($P)) $l)
  | `(iprop([∨list] $x:ident ∈ $l, $P)) => `(bigOrL (fun _ $x => iprop($P)) $l)
  | `(iprop([∨list] $k:ident ↦ $x:ident ∈ $l, $P)) => `(bigOrL (fun $k $x => iprop($P)) $l)

end List

/-! # BI-Instantiated Big Operators over Sets
- `bigSepS`: Big separating conjunction `[∗set]`
- `bigAndS`: Big conjunction `[∧set]`
- `bigOrS`: Big disjunction `[∨set]`
-/

section Set
/-! ## Core Definitions -/

abbrev bigSepS [BI PROP] {A : Type _} (Φ : A → PROP) [FiniteSet S A] (s : S) : PROP :=
  bigOpS sep Φ s

abbrev bigAndS [BI PROP] {A : Type _} (Φ : A → PROP) [FiniteSet S A] (s : S) : PROP :=
  bigOpS and Φ s

/-- Big disjunction over a list with index access.
    `bigOrL Φ l` computes `Φ 0 l[0] ∨ Φ 1 l[1] ∨ ... ∨ Φ (n-1) l[n-1]` -/
abbrev bigOrS [BI PROP] {A : Type _} (Φ : A → PROP) [FiniteSet S A] (s : S) : PROP :=
  bigOpS or Φ s

/-! ## Notation -/

-- Notation for bigSepS
syntax atomic("[∗set]") ident " ∈ " term ", " term : term

-- Notation for bigAndS
syntax atomic("[∧set]") ident " ∈ " term ", " term : term

-- Notation for bigOrS
syntax atomic("[∨set]") ident " ∈ " term ", " term : term

macro_rules
  | `([∗set] $x:ident ∈ $l, $P) => `(bigSepS (fun $x => $P) $l)
  | `([∧set] $x:ident ∈ $l, $P) => `(bigAndS (fun $x => $P) $l)
  | `([∨set] $x:ident ∈ $l, $P) => `(bigOrS (fun $x => $P) $l)

-- iprop macro rules
macro_rules
  | `(iprop([∗set] $x:ident ∈ $l, $P)) => `(bigSepS (fun $x => iprop($P)) $l)
  | `(iprop([∧set] $x:ident ∈ $l, $P)) => `(bigAndS (fun $x => iprop($P)) $l)
  | `(iprop([∨set] $x:ident ∈ $l, $P)) => `(bigOrS (fun $x => iprop($P)) $l)

end Set
