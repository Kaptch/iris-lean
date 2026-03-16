import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Std.Positives
import Iris.Std.CoPset

open Iris

open OFE CMRA UCMRA
open Std.CoPset

inductive CoPsetDisj where
  | copset : CoPset → CoPsetDisj
  | copset_invalid : CoPsetDisj

abbrev CoPsetDisjO := LeibnizO CoPsetDisj

abbrev copset : CoPset → CoPsetDisjO := fun X => .mk (.copset X)

instance : OFE CoPsetDisjO := inferInstance

namespace CoPset

def unit : CoPsetDisjO := .mk (.copset ∅)

def pcore : CoPsetDisjO → Option CoPsetDisjO := fun _ => some unit

def op (x y : CoPsetDisjO) : CoPsetDisjO :=
  match x.car, y.car with
  | .copset x, .copset y => if (x ## y) then .mk (.copset (x ∪ y)) else .mk .copset_invalid
  | _, _ => .mk .copset_invalid

def valid (x : CoPsetDisjO) : Prop :=
  match x.car with
  | .copset _ => True
  | _ => False

theorem unit_valid : valid unit := by simp [unit, valid]

def validN : Nat → CoPsetDisjO → Prop := fun _ x => valid x

instance op_ne : OFE.NonExpansive (op x) where
  ne n y z H := by rw [H]

theorem pcore_ne : x ≡{n}≡ y → pcore x = some cx →
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

theorem validN_op_left : validN n (op x y) → validN n x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op, validN, valid]

theorem assoc : op x (op y z) ≡ op (op x y) z := by
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
          rw [disj_union]; apply And.intro <;> (symm; assumption)
        have K2 : x ∪ y ## z := by
          rw [disj_union]; apply And.intro <;> assumption
        simp [K1, K2]
        rw [Iris.Std.Associative.assoc (R := Eq) (α := CoPset) (f := Union.union)]
      else
        have K1 : ¬ x ## y ∪ z := by
          intro C
          symm at C; rw [disj_union] at C
          apply J; symm; exact C.right
        have K2 : ¬ x ∪ y ## z := by
          rw [disj_union, not_and]
          intro C
          exfalso; apply J C
        simp [K1, K2]
    else
      simp [G]
      intro C; symm at C; rw [disj_union] at C
      apply (G (disj_symm _ _ C.left))
  else
    simp [H]
    if G : x ## y
    then
      simp [G]
      intro C; apply H
      rw [disj_union] at C
      apply C.right
    else
      simp [G]

theorem comm : op x y ≡ op y x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op]
  if H : x ## y
  then
    have H' : y ## x := by symm; assumption
    simp [H, H', Iris.Std.Commutative.comm (R := Eq) (α := CoPset) (f := Union.union)]
  else simp [H]
       intro c; apply H (disj_symm _ _ c)

theorem pcore_op_left : pcore x = some cx → op cx x ≡ x := by
  rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [op, pcore, unit]
  intro H; rw [<-H]; simp [disj_empty_l]
  ext p; rw [in_union]
  apply Iff.intro
  · intro H; cases H with | inl H => exfalso; apply in_empty H | inr H => apply H
  · intro H; right; assumption

theorem pcore_idem : pcore x = some cx → pcore cx ≡ some cx := by
  rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [pcore, unit]

theorem pcore_op_mono : pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) ≡ some (op cx cy) := by
  rcases x with ⟨x | _⟩ <;> simp [pcore] <;> intro H y <;> rw [<-H]
  <;> (exists unit; simp only [unit, op, disj_empty_l, ↓reduceIte, union_empty_l.left_id])

def extend (H : x ≡{n}≡ op y₁ y₂) :
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  exists y₁, y₂

theorem unit_left_id : op unit x ≡ x := by
  rcases x with ⟨x | _⟩ <;> simp [op, unit, disj_empty_l, union_empty_l.left_id]

theorem pcore_unit : pcore unit ≡ some unit := by
  simp [pcore, unit]

instance : CMRA CoPsetDisjO where
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

instance : UCMRA CoPsetDisjO where
  unit := unit
  unit_valid := unit_valid
  unit_left_id := unit_left_id
  pcore_unit := pcore_unit

theorem copset_disj_included (X Y : CoPset) :
   copset X ≼ copset Y ↔ X ⊆ Y := by
  simp only [CMRA.Included]
  apply Iff.intro
  · intro ⟨Z, HZ⟩
    rcases Z with ⟨Z | _⟩
    · if H : X ## Z
      then
        simp [CMRA.op, op, H] at HZ
        rw [HZ]
        intro p Hp; rw [in_union]; left; exact Hp
      else
        simp [CMRA.op, op, H] at HZ
    · simp [CMRA.op, op] at HZ
  · intro Hsub
    exists copset (Y \ X)
    have H : X ## (Y \ X) := by
      intro p H1 H2
      rw [in_diff] at H2
      apply H2.right H1
    simp [CMRA.op, op, H]
    ext p; rw [in_union, in_diff]
    apply Iff.intro
    · intro G
      cases H : (decide (p ∈ X)) with
      | true =>
        simp only [decide_eq_true_eq] at H
        left; exact H
      | false =>
        simp only [decide_eq_false_iff_not] at H
        right; exact ⟨G, H⟩
    · rintro (G|G)
      · apply Hsub _ G
      · apply G.left

theorem copset_disj_union (X Y : CoPset) (Hdisj : X ## Y) :
  (copset X) • (copset Y) ≡ copset (X ∪ Y) := by
  simp [CMRA.op, op]
  exact Hdisj

theorem copset_disj_valid_op (X Y : CoPset) :
    ✓ ((copset X) • (copset Y)) ↔ X ## Y := by
  simp [CMRA.op, op, CMRA.Valid, valid]
  by_cases H : X ## Y <;> simp [H]

theorem copset_disj_valid_inv_l (X : CoPset) (Y : CoPsetDisjO) :
    ✓ ((copset X) • Y) → ∃ Y', Y = copset Y' ∧ X ## Y' := by
  simp [CMRA.op, op, CMRA.Valid, valid]
  rcases Y with ⟨Y | _⟩ <;> simp <;> by_cases H : X ## Y <;> simp [H]

end CoPset
