import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Std.GenSets

open Iris

open OFE CMRA UCMRA
open Std

section Def

variable (S : Type _)

inductive SetDisj S where
  | set_valid : S → SetDisj S
  | set_invalid : SetDisj S

abbrev SetDisjO := LeibnizO (SetDisj S)

instance : OFE (SetDisjO S) := inferInstance

end Def

abbrev set_valid : S → SetDisjO S := fun X => .mk (.set_valid X)

namespace Set
open Set

variable {S : Type _} [LawfulSet S A]

def unit : SetDisjO S := .mk (.set_valid ∅)

def pcore : SetDisjO S → Option (SetDisjO S) := fun _ => some unit

def valid (x : SetDisjO S) : Prop :=
  match x.car with
  | .set_valid _ => True
  | _ => False

theorem unit_valid : valid (unit (S := S)) := by simp [unit, valid]

def validN : Nat → SetDisjO S → Prop := fun _ x => valid x

theorem pcore_ne {x y : SetDisjO S} : x ≡{n}≡ y → pcore x = some cx →
  ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := by
  intro H1 H2
  exists cx

theorem validN_ne : x ≡{n}≡ y → validN n x → validN n y := by
  intro H G; rw [<-H]; assumption

theorem valid_iff_validN : valid x ↔ ∀ n, validN n x := by
  apply Iff.intro
  · intro H n; apply H
  · intro H; apply H 0

theorem validN_succ : validN n.succ x → validN n x := by
  intro H; apply H

theorem pcore_idem {x : SetDisjO S} : pcore x = some cx → pcore cx ≡ some cx := by
  rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [pcore, unit]

theorem pcore_unit : pcore (unit : SetDisjO S) ≡ some unit := by
  simp [pcore, unit]

variable [∀ X₁ X₂ : S, Decidable (X₁ ## X₂)]

def op (x y : SetDisjO S) : SetDisjO S :=
  match x.car, y.car with
  | .set_valid x, .set_valid y => if (x ## y) then .mk (.set_valid (x ∪ y)) else .mk .set_invalid
  | _, _ => .mk .set_invalid

theorem validN_op_left {x y : SetDisjO S} : validN n (op x y) → validN n x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op, validN, valid]

instance op_ne {x : SetDisjO S} : OFE.NonExpansive (op x) where
  ne n y z H := by rw [H]

theorem assoc {x y z : SetDisjO S} : op x (op y z) ≡ op (op x y) z := by
  rcases x, y, z with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩, ⟨⟨z⟩ | _⟩⟩ <;> simp [op]
  if H : y ## z
  then
    simp [H]
    if G : x ## y
    then
      simp [G]
      if J : x ## z
      then
        have K1 : x ## y ∪ z := by
          symm
          rw [disjoint_union_left]; apply And.intro <;> (symm; assumption)
        have K2 : x ∪ y ## z := by
          rw [disjoint_union_left]; apply And.intro <;> assumption
        simp [K1, K2]
        rw [union_assoc]
      else
        have K1 : ¬ x ## y ∪ z := by
          intro C
          symm at C; rw [disjoint_union_left] at C
          apply J; symm; exact C.right
        have K2 : ¬ x ∪ y ## z := by
          rw [disjoint_union_left, not_and]
          intro C
          exfalso; apply J C
        simp [K1, K2]
    else
      simp [G]
      intro C; symm at C; rw [disjoint_union_left] at C
      apply (G (disjoint_symm C.left))
  else
    simp [H]
    if G : x ## y
    then
      simp [G]
      intro C; apply H
      rw [disjoint_union_left] at C
      apply C.right
    else
      simp [G]

theorem comm {x y : SetDisjO S} : op x y ≡ op y x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op]
  if H : x ## y
  then
    have H' : y ## x := by symm; assumption
    simp [H, H', union_comm]
  else simp [H]
       intro c; apply H (disjoint_symm c)

theorem pcore_op_left {x : SetDisjO S} : pcore x = some cx → op cx x ≡ x := by
  rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [op, pcore, unit]
  intro H; rw [<-H]; simp [disjoint_empty_left]

theorem pcore_op_mono {x : SetDisjO S} : pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) ≡ some (op cx cy) := by
  rcases x with ⟨x | _⟩ <;> simp [pcore] <;> intro H y <;> rw [<-H]
  <;> (exists unit; simp only [unit, op, disjoint_empty_left, ↓reduceIte, union_idem])

def extend {x y₁ y₂ : SetDisjO S} (H : x ≡{n}≡ op y₁ y₂) :
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  exists y₁, y₂

theorem unit_left_id {x : SetDisjO S} : op unit x ≡ x := by
  rcases x with ⟨x | _⟩ <;> simp [op, unit, disjoint_empty_left]

instance : CMRA (SetDisjO S) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne := pcore_ne
  validN_ne := validN_ne
  valid_iff_validN := valid_iff_validN
  validN_succ := validN_succ
  validN_op_left := validN_op_left
  assoc := assoc
  comm := comm
  pcore_op_left := pcore_op_left
  pcore_idem := pcore_idem
  pcore_op_mono := pcore_op_mono
  extend _ := extend

instance : UCMRA (SetDisjO S) where
  unit := unit
  unit_valid := unit_valid
  unit_left_id := unit_left_id
  pcore_unit := pcore_unit

theorem set_disj_included (X Y : S) :
   set_valid X ≼ set_valid Y ↔ X ⊆ Y := by
  simp only [CMRA.Included]
  apply Iff.intro
  · intro ⟨Z, HZ⟩
    rcases Z with ⟨Z | _⟩
    · if H : X ## Z
      then
        simp [CMRA.op, op, H] at HZ
        rw [HZ]
        intro p Hp; rw [mem_union]; left; exact Hp
      else
        simp [CMRA.op, op, H] at HZ
    · simp [CMRA.op, op] at HZ
  · intro Hsub
    exists set_valid (Y \ X)
    have H : X ## (Y \ X) := by
      intro p ⟨H1, H2⟩
      rw [mem_diff] at H2
      apply H2.right H1
    simp [CMRA.op, op, H]
    ext p; rw [mem_union, mem_diff]
    apply Iff.intro
    · intro G
      by_cases H : (p ∈ X)
      · left; exact H
      · right; exact ⟨G, H⟩
    · rintro (G|G)
      · apply Hsub _ G
      · apply G.left

theorem set_disj_union (X Y : S) (Hdisj : X ## Y) :
  (set_valid X) • (set_valid Y) ≡ set_valid (X ∪ Y) := by
  simp [CMRA.op, op]
  exact Hdisj

theorem set_disj_valid_op (X Y : S) :
    ✓ ((set_valid X) • (set_valid Y)) ↔ X ## Y := by
  simp [CMRA.op, op, CMRA.Valid, valid]
  by_cases H : X ## Y <;> simp [H]

theorem set_disj_valid_inv_l (X : S) (Y : SetDisjO S) :
    ✓ ((set_valid X) • Y) → ∃ Y', Y = set_valid Y' ∧ X ## Y' := by
  simp [CMRA.op, op, CMRA.Valid, valid]
  rcases Y with ⟨Y | _⟩ <;> simp <;> by_cases H : X ## Y <;> simp [H]

end Set
