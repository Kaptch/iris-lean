/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Sergei Stepanenko
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
open Iris.Std.Set

def bigOpL {M : Type u} {A : Type v} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit]
    (Φ : Nat → A → M) (l : List A) : M :=
  match l with
  | [] => unit
  | x :: xs => op (Φ 0 x) (bigOpL op (fun n => Φ (n + 1)) xs)

def bigOpS {A : Type _} {S : Type _} [OFE M] (op : M → M → M) {unit : M}
  [MonoidOps op unit] (Φ : A → M) [FiniteSet S A] (m : S) : M :=
  fold (fun acc x => op (Φ x) acc) unit m

/-- Big op over list with index: `[^ op list] k ↦ x ∈ l, P` -/
scoped syntax atomic("[^") term " list]" ident " ↦ " ident " ∈ " term ", " term : term
/-- Big op over list without index: `[^ op list] x ∈ l, P` -/
scoped syntax atomic("[^") term " list]" ident " ∈ " term ", " term : term

/-- Big op over set without index: `[^ op set] x ∈ l, P` -/
scoped syntax atomic("[^") term " set]" ident " ∈ " term ", " term : term

scoped macro_rules
  | `([^ $o list] $k ↦ $x ∈ $l, $P) => `(bigOpL $o (fun $k $x => $P) $l)
  | `([^ $o list] $x ∈ $l, $P) => `(bigOpL $o (fun _ $x => $P) $l)
  | `([^ $o set] $x ∈ $l, $P) => `(bigOpS $o (fun $x => $P) $l)

namespace BigOpL

variable {M : Type _} {A : Type _} [OFE M] {op : M → M → M} {unit : M} [MonoidOps op unit]

@[simp] theorem nil (Φ : Nat → A → M) :
    ([^ op list] k ↦ x ∈ ([] : List A), Φ k x) = unit := rfl

@[simp] theorem cons (Φ : Nat → A → M) (a : A) (as : List A) :
    ([^ op list] k ↦ x ∈ a :: as, Φ k x) = op (Φ 0 a) ([^ op list] k ↦ x ∈ as, Φ (k + 1) x) := rfl

@[simp] theorem singleton (Φ : Nat → A → M) (a : A) :
    ([^ op list] k ↦ x ∈ [a], Φ k x) ≡ Φ 0 a := by
  simp only [cons, nil]; exact MonoidOps.op_right_id _

theorem congr {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡ Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡ ([^ op list] k ↦ x ∈ l, Ψ k x) := by
  induction l generalizing Φ Ψ with
  | nil => exact Equiv.rfl
  | cons y ys ih =>
    simp only [cons]
    apply MonoidOps.op_proper (h 0 y rfl)
    exact ih fun i x hget => h (i + 1) x hget

theorem congr_dist {Φ Ψ : Nat → A → M} {l : List A} {n : Nat}
    (h : ∀ i x, l[i]? = some x → Φ i x ≡{n}≡ Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡{n}≡ ([^ op list] k ↦ x ∈ l, Ψ k x) := by
  induction l generalizing Φ Ψ with
  | nil => exact Dist.rfl
  | cons y ys ih =>
    simp only [cons]
    apply MonoidOps.op_ne_dist (h 0 y rfl)
    exact ih fun i x hget => h (i + 1) x hget

/-- Congruence when the functions are equivalent on all indices. -/
theorem congr_forall {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, Φ i x ≡ Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡ ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  congr (fun i x _ => h i x)

theorem append (Φ : Nat → A → M) (l₁ l₂ : List A) :
    ([^ op list] k ↦ x ∈ l₁ ++ l₂, Φ k x) ≡
      op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Φ (k + l₁.length) x) := by
  induction l₁ generalizing Φ with
  | nil => simp only [nil]; exact (MonoidOps.op_left_id _).symm
  | cons x xs ih =>
    simp only [List.cons_append, cons, List.length_cons]
    apply (MonoidOps.op_congr_r (ih _)).trans
    simp only [show ∀ n, n + xs.length + 1 = n + (xs.length + 1) from by omega]
    exact (MonoidOps.op_assoc _ _ _).symm

theorem snoc (Φ : Nat → A → M) (l : List A) (a : A) :
    ([^ op list] k ↦ x ∈ l ++ [a], Φ k x) ≡ op ([^ op list] k ↦ x ∈ l, Φ k x) (Φ l.length a) := by
  have := append (op := op) Φ l [a]
  simp only [cons, nil, Nat.zero_add] at this
  refine this.trans ?_
  exact MonoidOps.op_congr_r (MonoidOps.op_right_id _)

theorem const_unit (l : List A) :
    ([^ op list] _x ∈ l, unit) ≡ unit := by
  induction l with
  | nil => exact Equiv.rfl
  | cons _ _ ih =>
    simp only [cons]
    refine (MonoidOps.op_left_id _).trans ?_
    exact ih

theorem op_distrib (Φ Ψ : Nat → A → M) (l : List A) :
    ([^ op list] k ↦ x ∈ l, op (Φ k x) (Ψ k x)) ≡
      op ([^ op list] k ↦ x ∈ l, Φ k x) ([^ op list] k ↦ x ∈ l, Ψ k x) := by
  induction l generalizing Φ Ψ with
  | nil => simp only [nil]; exact Equiv.symm (MonoidOps.op_left_id _)
  | cons x xs ih =>
    simp only [cons]
    refine (MonoidOps.op_congr_r (ih _ _)).trans ?_
    exact MonoidOps.op_op_swap

theorem map {B : Type v} (h : A → B) (Φ : Nat → B → M) (l : List A) :
    ([^ op list] k ↦ x ∈ l.map h, Φ k x) ≡ ([^ op list] k ↦ x ∈ l, Φ k (h x)) := by
  induction l generalizing Φ with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, cons]
    exact MonoidOps.op_proper Equiv.rfl (ih _)

theorem closed (P : M → Prop) (Φ : Nat → A → M) (l : List A)
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ i x, l[i]? = some x → P (Φ i x)) :
    P ([^ op list] k ↦ x ∈ l, Φ k x) := by
  induction l generalizing Φ with
  | nil => exact hunit
  | cons y ys ih =>
    simp only [cons]
    exact hop _ _ (hf 0 y rfl) (ih _ fun i x hget => hf (i + 1) x hget)

theorem perm (Φ : A → M) {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([^ op list] x ∈ l₁, Φ x) ≡ ([^ op list] x ∈ l₂, Φ x) := by
  induction hp with
  | nil => exact Equiv.rfl
  | cons _ _ ih => simp only [cons]; exact MonoidOps.op_congr_r ih
  | swap _ _ _ => simp only [cons]; exact MonoidOps.op_swap_inner (unit := unit)
  | trans _ _ ih1 ih2 => exact Equiv.trans ih1 ih2

theorem take_drop (Φ : Nat → A → M) (l : List A) (n : Nat) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡
      op ([^ op list] k ↦ x ∈ l.take n, Φ k x) ([^ op list] k ↦ x ∈ l.drop n, Φ (n + k) x) := by
  by_cases hn : n ≤ l.length
  · have := append (op := op) Φ (l.take n) (l.drop n)
    simp only [List.take_append_drop, List.length_take_of_le hn, Nat.add_comm] at this
    exact this
  · simp only [Nat.not_le] at hn
    simp only [List.drop_eq_nil_of_le (Nat.le_of_lt hn)
             , List.take_of_length_le (Nat.le_of_lt hn), nil]
    exact Equiv.symm (MonoidOps.op_right_id _)

theorem filter_map {B : Type v} (h : A → Option B) (Φ : B → M) (l : List A) :
    ([^ op list] x ∈ l.filterMap h, Φ x) ≡
      ([^ op list] x ∈ l, (h x).elim unit Φ) := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    cases hx : h x <;> simp only [hx, Option.elim, cons]
    · exact Equiv.trans ih (Equiv.symm (MonoidOps.op_left_id _))
    · exact MonoidOps.op_congr_r ih

theorem bind {B : Type v} (h : A → List B) (Φ : B → M) (l : List A) :
    ([^ op list] x ∈ l.flatMap h, Φ x) ≡
      ([^ op list] x ∈ l, [^ op list] y ∈ h x, Φ y) := by
  induction l with
  | nil => exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, cons]
    refine (append _ _ _).trans ?_
    exact MonoidOps.op_congr_r ih

theorem gen_proper_2 {B : Type v} (R : M → M → Prop)
    (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hunit : R unit unit)
    (hop : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hlen : l₁.length = l₂.length)
    (hf : ∀ i, ∀ x y, l₁[i]? = some x → l₂[i]? = some y → R (Φ i x) (Ψ i y)) :
    R ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [nil]; exact hunit
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [cons]
      exact hop _ _ _ _ (hf 0 x y rfl rfl)
        (ih _ _ _ hlen fun i a b ha hb => hf (i + 1) a b ha hb)

theorem gen_proper (R : M → M → Prop)
    (Φ Ψ : Nat → A → M) (l : List A)
    (hR_refl : ∀ x, R x x)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k y, l[k]? = some y → R (Φ k y) (Ψ k y)) :
    R ([^ op list] k ↦ x ∈ l, Φ k x) ([^ op list] k ↦ x ∈ l, Ψ k x) := by
  apply gen_proper_2 R Φ Ψ l l (hR_refl unit) hR_op rfl
  intro k x y hx hy; rw [hx] at hy; cases hy; exact hf k x hx

theorem ext {Φ Ψ : Nat → A → M} {l : List A}
    (h : ∀ i x, l[i]? = some x → Φ i x = Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) = ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  gen_proper (· = ·) _ _ _ (fun _ => rfl) (fun _ _ _ _ ha hb => ha ▸ hb ▸ rfl) h

theorem proper_2 [OFE A] (Φ Ψ : Nat → A → M) (l₁ l₂ : List A)
    (hlen : l₁.length = l₂.length)
    (hf : ∀ (k : Nat) (y₁ y₂ : A), l₁[k]? = some y₁ → l₂[k]? = some y₂ → Φ k y₁ ≡ Ψ k y₂) :
    ([^ op list] k ↦ x ∈ l₁, Φ k x) ≡ ([^ op list] k ↦ x ∈ l₂, Ψ k x) :=
  gen_proper_2 (· ≡ ·) Φ Ψ l₁ l₂ Equiv.rfl (fun _ _ _ _ => MonoidOps.op_proper) hlen hf

theorem zipIdx (Φ : A × Nat → M) (n : Nat) (l : List A) :
    ([^ op list] x ∈ l.zipIdx n, Φ x) ≡
      ([^ op list] k ↦ x ∈ l, Φ (x, n + k)) := by
  induction l generalizing n with
  | nil => simp only [nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [cons, Nat.add_zero]
    exact MonoidOps.op_proper Equiv.rfl
      ((ih (n + 1)).trans (congr_forall fun i _ => by simp [Nat.add_assoc, Nat.add_comm 1 i]))

theorem zipIdxInt (Φ : A × Int → M) (n : Int) (l : List A) :
    ([^ op list] x ∈ Std.List.zipIdxInt l n, Φ x) ≡
      ([^ op list] k ↦ x ∈ l, Φ (x, n + (k : Int))) := by
  unfold Std.List.zipIdxInt
  suffices ∀ m, bigOpL op (fun _ => Φ) (l.mapIdx (fun i v => (v, (i : Int) + m))) ≡
                bigOpL op (fun i x => Φ (x, m + (i : Int))) l from this n
  intro m
  induction l generalizing m with
  | nil => simp only [List.mapIdx, nil]; exact Equiv.rfl
  | cons x xs ih =>
    simp only [List.mapIdx_cons, cons]
    apply MonoidOps.op_proper
    · show Φ (x, (0 : Int) + m) ≡ Φ (x, m + (0 : Int))
      rw [Int.zero_add, Int.add_zero]
    · rw [show (List.mapIdx (fun i v => (v, ↑(i + 1) + m)) xs) =
              (List.mapIdx (fun i v => (v, ↑i + (m + 1))) xs) from by
        apply List.ext_getElem (by simp only [List.length_mapIdx])
        intro n hn1 hn2
        simp only [List.getElem_mapIdx]; congr 1; omega]
      apply (ih (m + 1)).trans
      apply congr_forall fun i _ => ?_
      rw [show m + 1 + (i : Int) = m + ((i + 1 : Nat) : Int) from by omega]

theorem sep_zipWith {B C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hlen : l₁.length = l₂.length) :
    ([^ op list] k ↦ c ∈ List.zipWith f l₁ l₂, op (Φ k (g1 c)) (Ψ k (g2 c))) ≡
      op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [List.zipWith_nil_left, nil]; exact Equiv.symm (MonoidOps.op_left_id _)
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, cons, hg1, hg2]
      refine (MonoidOps.op_congr_r (ih _ _ _ hlen)).trans ?_
      exact MonoidOps.op_op_swap

/-- Big op over zipped list with separated functions. -/
theorem sep_zip {B : Type v} (Φ : Nat → A → M) (Ψ : Nat → B → M) (l₁ : List A) (l₂ : List B)
    (hlen : l₁.length = l₂.length) :
    ([^ op list] k ↦ xy ∈ l₁.zip l₂, op (Φ k xy.1) (Ψ k xy.2)) ≡
      op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  simp only [List.zip]
  exact sep_zipWith (op := op) _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) hlen

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]
variable {B : Type w}

/-- Monoid homomorphisms distribute over big ops. -/
theorem hom {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : Nat → B → M₁) (l : List B) :
    R (f ([^ op₁ list] k ↦ x ∈ l, Φ k x)) ([^ op₂ list] k ↦ x ∈ l, f (Φ k x)) := by
  induction l generalizing Φ with
  | nil => simp only [nil]; exact hom.map_unit
  | cons x xs ih =>
    simp only [cons]
    apply hom.rel_trans (hom.homomorphism _ _)
    exact hom.op_proper (hom.rel_refl _) (ih _)

/-- Weak monoid homomorphisms distribute over non-empty big ops. -/
theorem hom_weak {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : Nat → B → M₁) (l : List B) (hne : l ≠ []) :
    R (f ([^ op₁ list] k ↦ x ∈ l, Φ k x)) ([^ op₂ list] k ↦ x ∈ l, f (Φ k x)) := by
  induction l generalizing Φ with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [cons]
    cases xs with
    | nil =>
      simp only [nil]
      haveI : NonExpansive f := hom.f_ne
      apply (hom.rel_proper (NonExpansive.eqv (MonoidOps.op_right_id _))
        (MonoidOps.op_right_id _)).mpr
      exact hom.rel_refl _
    | cons y ys =>
      apply hom.rel_trans (hom.homomorphism _ _)
      exact hom.op_proper (hom.rel_refl _) (ih _ (List.cons_ne_nil y ys))

end BigOpL

namespace BigOpS

variable {M : Type _} {A : Type _} {S : Type _} [OFE M] {op : M → M → M} {unit : M}
  [MonoidOps op unit] [LawfulFiniteSet S A]

private theorem fold_init_equiv (Φ : A → M) (s : List A) (b : M) :
    List.foldl (fun acc x => op (Φ x) acc) b s ≡
      op b (List.foldl (fun acc x => op (Φ x) acc) unit s) := by
  induction s generalizing b with
  | nil => simp only [List.foldl_nil]; exact Equiv.symm (MonoidOps.op_right_id _)
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply (ih (op (Φ x) b)).trans
    symm
    apply (MonoidOps.op_congr_r (ih _)).trans
    apply (MonoidOps.op_assoc _ _ _).symm.trans
    apply (MonoidOps.op_congr_l (MonoidOps.op_assoc _ _ _).symm).trans
    apply (MonoidOps.op_congr_l (MonoidOps.op_right_id _)).trans
    apply (MonoidOps.op_congr_l (MonoidOps.op_comm _ _)).trans
    rfl

@[simp] theorem empty {Φ : A → M} :
    ([^ op set] x ∈ (∅ : S), Φ x) = unit := by
  simp only [bigOpS, fold_empty]

theorem bigOpS_bigOpL (Φ : A → M) (s : S)
  : ([^ op set] x ∈ s, Φ x) ≡ ([^ op list] x ∈ toList s, Φ x) := by
  simp only [bigOpS, fold]
  generalize FiniteSet.toList s = l
  induction l with
  | nil => simp
  | cons x xs IH =>
    simp only [BigOpL.cons, List.foldl_cons]
    apply (fold_init_equiv Φ xs (op (Φ x) unit)).trans
    apply (MonoidOps.op_congr_l (MonoidOps.op_right_id _)).trans
    apply (MonoidOps.op_congr_r IH)

theorem const_unit (s : S) :
    ([^ op set] _x ∈ s, unit) ≡ unit := by
  simp only [bigOpS]
  induction s using set_ind with
  | hemp => simp
  | hadd x X hnin IH =>
    rw [fold_insert]
    · exact (MonoidOps.op_left_id _).trans IH
    · simp
    · assumption

@[simp] theorem singleton {Φ : A → M} {a : A} :
    ([^ op set] x ∈ ({a} : S), Φ x) ≡ Φ a := by
  simp only [bigOpS, fold_singleton]; exact MonoidOps.op_right_id _

@[simp] theorem insert {Φ : A → M} {s : S} {x : A} (Hnin : x ∉ s) :
  ([^ op set] x ∈ ({x} ∪ s), Φ x) ≡ op (Φ x) ([^ op set] x ∈ s, Φ x) := by
  apply (bigOpS_bigOpL Φ _).trans
  apply (BigOpL.perm Φ (toList_insert_perm Hnin)).trans
  simp only [BigOpL.cons]
  apply (MonoidOps.op_congr_r (bigOpS_bigOpL Φ _).symm)

@[simp] theorem union {Φ : A → M} {s₁ s₂ : S} (Hdisj : s₁ ## s₂) :
  ([^ op set] x ∈ (s₁ ∪ s₂), Φ x) ≡ op ([^ op set] x ∈ s₁, Φ x) ([^ op set] x ∈ s₂, Φ x) := by
  induction s₁ using set_ind with
  | hemp =>
    simp only [union_empty_left, empty]
    apply (MonoidOps.op_left_id _).symm
  | hadd x X Hnin IH =>
    rw [insert_union, <-union_assoc]
    rw [insert_union, disjoint_union_left, disjoint_singleton_left] at Hdisj
    have nunion : x ∉ X ∪ s₂ := by
      rw [mem_union]; rintro (h|h)
      · apply Hnin h
      · apply Hdisj.left h
    apply (insert nunion).trans
    apply (MonoidOps.op_congr_r (IH Hdisj.right)).trans
    symm
    apply (MonoidOps.op_congr_l (insert Hnin)).trans
    apply MonoidOps.op_assoc

theorem congr {Φ Ψ : A → M} {s : S}
    (h : ∀ x, x ∈ s → Φ x ≡ Ψ x) :
    ([^ op set] x ∈ s, Φ x) ≡ ([^ op set] x ∈ s, Ψ x) := by
  apply (bigOpS_bigOpL Φ _).trans; symm; apply (bigOpS_bigOpL Ψ _).trans
  apply BigOpL.congr
  intro i x hin
  symm; apply h
  rw [<-Set.mem_toList, List.mem_iff_getElem?]
  exists i

theorem congr_dist {Φ Ψ : A → M} {s : S} {n : Nat}
    (h : ∀ x, x ∈ s → Φ x ≡{n}≡ Ψ x) :
    ([^ op set] x ∈ s, Φ x) ≡{n}≡ ([^ op set] x ∈ s, Ψ x) := by
  apply ((bigOpS_bigOpL Φ _).dist).trans; symm; apply ((bigOpS_bigOpL Ψ _).dist).trans
  apply BigOpL.congr_dist
  intro i x hin
  symm; apply h
  rw [<-Set.mem_toList, List.mem_iff_getElem?]
  exists i

theorem op_distrib (Φ Ψ : A → M) (s : S) :
    ([^ op set] x ∈ s, op (Φ x) (Ψ x)) ≡
      op ([^ op set] x ∈ s, Φ x) ([^ op set] x ∈ s, Ψ x) := by
  apply (bigOpS_bigOpL _ _).trans
  apply (BigOpL.op_distrib _ _ _).trans
  apply (MonoidOps.op_congr_l (bigOpS_bigOpL _ _).symm).trans
  apply MonoidOps.op_congr_r (bigOpS_bigOpL _ _).symm

theorem closed (P : M → Prop) (Φ : A → M) (s : S)
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ x, x ∈ s → P (Φ x)) :
    P ([^ op set] x ∈ s, Φ x) := by
  unfold bigOpS Set.fold
  generalize hg : toList s = l
  have htoList : ∀ x, x ∈ l → P (Φ x) := by
    intro x hx
    apply hf
    rw [←Set.mem_toList, hg]
    exact hx
  clear hf hg s
  suffices ∀ b, P b → P (l.foldl (fun acc x => op (Φ x) acc) b) by exact this unit hunit
  intro b hb
  induction l generalizing b with
  | nil => simp only [List.foldl_nil]; exact hb
  | cons y ys ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro x Hxin
      apply htoList x (List.mem_cons.mpr (Or.inr Hxin))
    · apply hop
      · apply htoList y (List.mem_cons.mpr (Or.inl rfl))
      · assumption

theorem map {B : Type v} {S' : Type _} [LawfulFiniteSet S' B] (h : A → B) (hinj : Injective h)
    (Φ : B → M) (s : S) :
    ([^ op set] x ∈ map (S' := S') h s, Φ x) ≡
      ([^ op set] x ∈ s, Φ (h x)) := by
  apply (bigOpS_bigOpL Φ _).trans
  apply (BigOpL.perm Φ (toList_map_perm _ hinj)).trans
  apply (BigOpL.map _ _ _).trans
  apply (bigOpS_bigOpL _ _).symm.trans
  rfl

theorem ext {Φ Ψ : A → M} {s : S}
    (h : ∀ x, x ∈ s → Φ x = Ψ x) :
    ([^ op set] x ∈ s, Φ x) = ([^ op set] x ∈ s, Ψ x) := by
  unfold bigOpS Set.fold
  generalize hg : toList s = l
  generalize unit = t
  have htoList : ∀ x, x ∈ l → Φ x = Ψ x := by
    intro x hx
    apply h
    rw [←Set.mem_toList, hg]
    exact hx
  clear h hg s
  induction l generalizing t with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [htoList y (by simp)]
    apply ih
    intro x Hxin
    apply htoList x (List.mem_cons.mpr (Or.inr Hxin))

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]

theorem hom {B : Type w} {S' : Type _} [LawfulFiniteSet S' B] {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : B → M₁) (s : S') :
    R (f ([^ op₁ set] x ∈ s, Φ x)) ([^ op₂ set] x ∈ s, f (Φ x)) := by
  rw [hom.rel_proper (hom.f_ne.eqv (bigOpS_bigOpL Φ s)) Equiv.rfl]
  apply (hom.rel_trans (BigOpL.hom hom (fun x y => Φ y) (toList s)))
  rw [hom.rel_proper (bigOpS_bigOpL _ s).symm Equiv.rfl]
  apply hom.rel_refl

theorem hom_weak {B : Type w} {S' : Type _} [LawfulFiniteSet S' B] {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : B → M₁) (s : S') (hne : s ≠ ∅) :
    R (f ([^ op₁ set] x ∈ s, Φ x)) ([^ op₂ set] x ∈ s, f (Φ x)) := by
  rw [hom.rel_proper (hom.f_ne.eqv (bigOpS_bigOpL Φ s)) Equiv.rfl]
  apply (hom.rel_trans (BigOpL.hom_weak hom (fun x y => Φ y) (toList s) _))
  · rw [hom.rel_proper (bigOpS_bigOpL _ s).symm Equiv.rfl]
    apply hom.rel_refl
  · intro heq
    apply hne; ext i; simp only [<-Set.mem_toList, heq, toList_empty]

end BigOpS

end Iris.Algebra
