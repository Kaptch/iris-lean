/-
Copyright (c) 2026 Remy Seassau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Iris.Std.Positives
import Iris.Std.Classes

/- This file implements an abstract type [CoPset] of (possibly infinite) sets
of positive binary natural numbers ([Pos]). This type supports the
following operations:

· the empty set;
· a singleton set;
· the full set;
· union, intersection, and complement;
· picking an element in an infinite set;
· splitting a set into two disjoint subsets in such a way that if the original
  set is infinite then both parts are infinite;
· the (infinite) set of all numbers that have a certain suffix;
· conversions to and from other representations of sets.
-/

/-- The raw tree data structure -/

/- [coPset.leaf false] is the empty set; [coPset.leaf true] is the full set. -/
/- In [coPset.node b l r], the Boolean flag [b] indicates whether the number
1 is a member of the set, while the subtrees [l] and [r] must be
consulted to determine whether a number of the form [2i] or [2i+1]
is a member of the set. -/

private inductive CoPsetRaw where
  | leaf : Bool → CoPsetRaw
  | node : Bool → CoPsetRaw → CoPsetRaw → CoPsetRaw
deriving DecidableEq

/-- The type of raw trees (above) offers several representations of the
empty set and several representations of the full set. In order to
achieve extensional equality, this redundancy must be eliminated.
This is achieved by imposing a well-formedness criterion on trees. -/
def coPsetWf (t : CoPsetRaw) : Bool :=
  match t with
  | .leaf _ => true
  | .node true (.leaf true) (.leaf true) => false
  | .node false (.leaf false) (.leaf false) => false
  | .node _ l r => coPsetWf l && coPsetWf r

theorem node_wf_l b l r : coPsetWf (.node b l r) -> coPsetWf l := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp_all [coPsetWf]
theorem node_wf_r b l r : coPsetWf (.node b l r) -> coPsetWf r := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp_all [coPsetWf]

/-- The smart constructor [node'] preserves well-formedness. -/
def CoPsetRaw.node' (b : Bool) (l r : CoPsetRaw) : CoPsetRaw :=
  match b, l, r with
  | true, .leaf true, .leaf true => .leaf true
  | false, .leaf false, .leaf false => .leaf false
  | _, _, _ => .node b l r

theorem node'_wf b l r :
  coPsetWf l -> coPsetWf r -> coPsetWf (CoPsetRaw.node' b l r) := by
  cases b <;> rcases l with ⟨ ⟨⟩ ⟩ | _ <;> rcases r with ⟨ ⟨⟩ ⟩ | _ <;>
  simp [CoPsetRaw.node', coPsetWf] <;> exact fun a_6 a_7 => ⟨a_6, a_7⟩

open CoPsetRaw

/-- The membership test. -/
def CoPsetRaw.ElemOf : Pos → CoPsetRaw → Bool
  | _, leaf b => b
  | .xH, node b _ _ => b
  | p~0, node _ l _ => CoPsetRaw.ElemOf p l
  | p~1, node _ _ r => CoPsetRaw.ElemOf p r
instance : Membership Pos CoPsetRaw  where
  mem := fun t p => CoPsetRaw.ElemOf p t

theorem elem_of_node b l r (p : Pos) :
  (CoPsetRaw.ElemOf p (CoPsetRaw.node' b l r))
  = (CoPsetRaw.ElemOf p (CoPsetRaw.node b l r)) := by
  cases p <;> cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp [node', CoPsetRaw.ElemOf]


/-- Singleton. -/
def CoPsetRaw.Singleton : Pos → CoPsetRaw
  | .xH => node true (leaf false) (leaf false)
  | p~0 => node' false (Singleton p) (leaf false)
  | p~1 => node' false (leaf false) (Singleton p)

/-- Union -/
def CoPsetRaw.Union : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf false, t => t
  | t, leaf false => t
  | leaf true, _ => leaf true
  | _, leaf true => leaf true
  | node b1 l1 r1, node b2 l2 r2 =>
    node' (b1 || b2) (Union l1 l2) (Union r1 r2)
instance : Union CoPsetRaw where union := CoPsetRaw.Union

/-- Intersection -/
def CoPsetRaw.Intersection : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf true, t => t
  | t, leaf true => t
  | leaf false, _ => leaf false
  | _, leaf false => leaf false
  | node b1 l1 r1, node b2 l2 r2 =>
    node' (b1 && b2) (Intersection l1 l2) (Intersection r1 r2)
instance : Inter CoPsetRaw where inter := CoPsetRaw.Intersection

/-- Complement -/
def CoPsetRaw.Complement : CoPsetRaw → CoPsetRaw
  | leaf b => leaf (!b)
  | node b l r => node' (!b) (Complement l) (Complement r)

/-- Well-formedness for the above operations -/

theorem coPsetSingleton_wf p : coPsetWf (CoPsetRaw.Singleton p) := by
  induction p <;> simp_all only [CoPsetRaw.Singleton, coPsetWf]
  · apply node'_wf; simp only [coPsetWf]; assumption
  · apply node'_wf; assumption; simp [coPsetWf]
  · simp

theorem coPsetUnion_wf t1 t2 :
  coPsetWf t1 -> coPsetWf t2 -> coPsetWf (t1 ∪ t2) := by
  revert t2; induction t1 with
  | leaf b =>
    intros t2 Hwf1 Hwf2; cases b <;> simp only [Union.union, CoPsetRaw.Union]
    · assumption
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Union, coPsetWf]
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _
    <;> simp only [Union.union, CoPsetRaw.Union, coPsetWf]
    · assumption
    · apply node'_wf
      · apply IH1; exact node_wf_l b l r Hwf1
        exact node_wf_l _ _ _ Hwf2
      · apply IH2; exact node_wf_r b l r Hwf1
        exact node_wf_r _ _ _ Hwf2

theorem coPsetIntersection_wf t1 t2 :
  coPsetWf t1 -> coPsetWf t2 -> coPsetWf (t1 ∩ t2) := by
  revert t2; induction t1 with
  | leaf b =>
    intros t2 Hwf1 Hwf2; cases b
    <;> simp only [Inter.inter, CoPsetRaw.Intersection]
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Intersection, coPsetWf]
    · assumption
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _
    <;> simp only [Inter.inter, CoPsetRaw.Intersection, coPsetWf]
    · assumption
    · apply node'_wf
      · apply IH1; exact node_wf_l b l r Hwf1
        exact node_wf_l _ _ _ Hwf2
      · apply IH2; exact node_wf_r b l r Hwf1
        exact node_wf_r _ _ _ Hwf2

theorem coPsetComplement_wf t : coPsetWf (CoPsetRaw.Complement t) := by
  induction t with
  | leaf b => cases b <;> simp [CoPsetRaw.Complement, coPsetWf]
  | node b l r => cases b <;> simp only [CoPsetRaw.Complement] <;>
    apply node'_wf <;> assumption

def CoPsetRaw.isFinite : CoPsetRaw → Bool
  | CoPsetRaw.leaf b => !b
  | CoPsetRaw.node _ l r => isFinite l && isFinite r

  def CoPsetRaw.pickRaw : CoPsetRaw → Option Pos
  | CoPsetRaw.leaf true => some Pos.P1
  | CoPsetRaw.node true _ _ => some Pos.P1
  | CoPsetRaw.leaf false => none
  | CoPsetRaw.node false l r =>
    match pickRaw l with
    | some i => some (i~0)
    | none => Option.map (λ i => i~1) (pickRaw r)

def CoPsetRaw.suffixesRaw : Pos → CoPsetRaw
  | .xH => .leaf true
  | p~0 => CoPsetRaw.node' false (suffixesRaw p) (.leaf false)
  | p~1 => CoPsetRaw.node' false (.leaf false) (suffixesRaw p)

theorem coPsetSuffixes_wf p : coPsetWf (CoPsetRaw.suffixesRaw p) := by
  induction p <;> simp [CoPsetRaw.suffixesRaw, coPsetWf] <;>
  apply node'_wf <;> simp_all [coPsetWf]

/-- The abstract type [CoPset] -/
/- A set is a well-formed tree. -/
structure CoPset where
  tree : CoPsetRaw
  wf : coPsetWf tree = true

instance : Membership Pos CoPset where mem E p := p ∈ E.tree

namespace Iris.Std.CoPset

/-- Helper: if a well-formed tree has uniform membership, it must be a leaf.
    Corresponds to `coPLeaf_wf` in Rocq Iris. -/
private theorem coPsetLeaf_wf : ∀ (t : CoPsetRaw) (b : Bool),
    coPsetWf t = true → (∀ p, ElemOf p t = b) → t = .leaf b := by
  intro t b Hwf Hall
  cases t with
  | leaf b' =>
    congr
    exact Hall .xH
  | node b' l r =>
    exfalso
    have hb : b' = b := Hall .xH
    have hl : ∀ p, ElemOf p l = b := fun p => by
      have := Hall (.xO p); simp [ElemOf] at this; exact this
    have hr : ∀ p, ElemOf p r = b := fun p => by
      have := Hall (.xI p); simp [ElemOf] at this; exact this
    have hl_leaf : l = .leaf b := coPsetLeaf_wf l b (node_wf_l b' l r Hwf) hl
    have hr_leaf : r = .leaf b := coPsetLeaf_wf r b (node_wf_r b' l r Hwf) hr
    rw [hb, hl_leaf, hr_leaf] at Hwf
    cases b <;> simp [coPsetWf] at Hwf

/-- Two CoPsetRaw trees are equal if they have the same membership function
    and both are well-formed. -/
private theorem coPsetRaw_eq (t1 t2 : CoPsetRaw) :
    (∀ p, ElemOf p t1 = ElemOf p t2) →
    coPsetWf t1 = true → coPsetWf t2 = true → t1 = t2 := by
  intro Ht Hwf1 Hwf2
  match t1, t2 with
  | .leaf b1, .leaf b2 =>
    congr 1
    exact Ht .xH
  | .leaf b1, .node b2 l2 r2 =>
    cases b1 <;> cases b2
    <;> rcases l2 with ⟨⟨⟩⟩ | ⟨_, _, _⟩
    <;> rcases r2 with ⟨⟨⟩⟩ | ⟨_, _, _⟩
    <;> (have h1 := Ht (.xH);
         have h2 := Ht (.xI .xH);
         have h3 := Ht (.xO .xH);
         dsimp [ElemOf] at h1 h2 h3;
         cases h1 <;> cases h2 <;> cases h3)
    · simp [coPsetWf] at Hwf2
    · symm
      apply coPsetLeaf_wf _ false Hwf2
      intro p; specialize (Ht p); simp only [ElemOf, Bool.false_eq] at Ht; apply Ht
    · symm
      apply coPsetLeaf_wf _ false Hwf2
      intro p; specialize (Ht p); simp only [ElemOf, Bool.false_eq] at Ht; apply Ht
    · symm
      apply coPsetLeaf_wf _ false Hwf2
      intro p; specialize (Ht p); simp only [ElemOf, Bool.false_eq] at Ht; apply Ht
    · simp [coPsetWf] at Hwf2
    · symm
      apply coPsetLeaf_wf _ true Hwf2
      intro p; specialize (Ht p); simp only [ElemOf, Bool.true_eq] at Ht; apply Ht
    · symm
      apply coPsetLeaf_wf _ true Hwf2
      intro p; specialize (Ht p); simp only [ElemOf, Bool.true_eq] at Ht; apply Ht
    · symm
      apply coPsetLeaf_wf _ true Hwf2
      intro p; specialize (Ht p); simp only [ElemOf, Bool.true_eq] at Ht; apply Ht
  | .node b1 l1 r1, .leaf b2 =>
    cases b1 <;> cases b2
    <;> rcases l1 with ⟨⟨⟩⟩ | ⟨_, _, _⟩
    <;> rcases r1 with ⟨⟨⟩⟩ | ⟨_, _, _⟩
    <;> (have h1 := Ht (.xH);
         have h2 := Ht (.xI .xH);
         have h3 := Ht (.xO .xH);
         dsimp [ElemOf] at h1 h2 h3;
         cases h1 <;> cases h2 <;> cases h3)
    · simp [coPsetWf] at Hwf1
    · apply coPsetLeaf_wf _ false Hwf1
      intro p; specialize (Ht p); simp only [ElemOf] at Ht; apply Ht
    · apply coPsetLeaf_wf _ false Hwf1
      intro p; specialize (Ht p); simp only [ElemOf] at Ht; apply Ht
    · apply coPsetLeaf_wf _ false Hwf1
      intro p; specialize (Ht p); simp only [ElemOf] at Ht; apply Ht
    · simp [coPsetWf] at Hwf1
    · apply coPsetLeaf_wf _ true Hwf1
      intro p; specialize (Ht p); simp only [ElemOf] at Ht; apply Ht
    · apply coPsetLeaf_wf _ true Hwf1
      intro p; specialize (Ht p); simp only [ElemOf] at Ht; apply Ht
    · apply coPsetLeaf_wf _ true Hwf1
      intro p; specialize (Ht p); simp only [ElemOf] at Ht; apply Ht
  | .node b1 l1 r1, .node b2 l2 r2 =>
    have hb : b1 = b2 := Ht .xH
    have hl : l1 = l2 := by
      apply coPsetRaw_eq
      · intro p; exact Ht (.xO p)
      · exact node_wf_l _ _ _ Hwf1
      · exact node_wf_l _ _ _ Hwf2
    have hr : r1 = r2 := by
      apply coPsetRaw_eq
      · intro p; exact Ht (.xI p)
      · exact node_wf_r _ _ _ Hwf1
      · exact node_wf_r _ _ _ Hwf2
    congr

instance : Membership Pos CoPset where mem E p := p ∈ E.tree

/-- All operations are refined at the level of [CoPset] -/

@[ext]
theorem ext {X Y : CoPset} (H : ∀ p, p ∈ X <-> p ∈ Y) : X = Y := by
  rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩
  simp only [CoPset.mk.injEq]
  apply coPsetRaw_eq
  · intro p; specialize (H p); simp only [Membership.mem, Bool.coe_iff_coe] at H
    exact H
  · exact xwf
  · exact ywf

def empty : CoPset := ⟨CoPsetRaw.leaf false, rfl⟩
instance : EmptyCollection CoPset where emptyCollection := empty

theorem in_empty : p ∉ (∅ : CoPset) := by
  simp [EmptyCollection.emptyCollection, Membership.mem, empty, ElemOf]

def singleton (p : Pos) : CoPset :=
  ⟨Singleton p, coPsetSingleton_wf p⟩

def union (X Y : CoPset) : CoPset :=
  ⟨Union X.tree Y.tree, coPsetUnion_wf _ _ X.wf Y.wf⟩
instance : Union CoPset where union := union

def inter (X Y : CoPset) : CoPset :=
  ⟨Intersection X.tree Y.tree, coPsetIntersection_wf _ _ X.wf Y.wf⟩
instance : Inter CoPset where inter := inter

def complement (X : CoPset) : CoPset :=
  ⟨Complement X.tree, coPsetComplement_wf _⟩

def diff (X Y : CoPset) : CoPset := X ∩ (complement Y)

def mem (p : Pos) (X : CoPset) : Bool :=
  ElemOf p X.tree

instance : HasSubset CoPset where
  Subset t1 t2 := ∀ (p : Pos), p ∈ t1 -> p ∈ t2

def full : CoPset := ⟨leaf true, rfl⟩

theorem in_full : p ∈ full := by
  simp [Membership.mem, full, ElemOf]

instance : SDiff CoPset where
  sdiff := CoPset.diff

theorem in_inter p (X Y : CoPset) :
  p ∈ X ∩ Y <-> p ∈ X ∧ p ∈ Y := by
  simp only [Inter.inter, inter, Membership.mem]
  constructor
  · rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩; dsimp
    induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp only [Intersection] <;> intros Hnin <;>
      simp_all [ElemOf]
      apply (IH _ (node_wf_r _ _ _ xwf) _ (node_wf_r _ _ _ ywf))
      rewrite [elem_of_node] at Hnin; simp_all [ElemOf]
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp only [Intersection] <;> intros Hnin <;>
      simp_all [ElemOf]
      apply (IH _ (node_wf_l _ _ _ xwf) _ (node_wf_l _ _ _ ywf))
      rewrite [elem_of_node] at Hnin; simp_all [ElemOf]
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [Intersection, ElemOf, elem_of_node]

  · rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩; simp []
    induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [ElemOf, elem_of_node, Intersection]
      apply (IH _ (node_wf_r _ _ _ xwf) _ (node_wf_r _ _ _ ywf))
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [ElemOf, elem_of_node, Intersection]
      apply (IH _ (node_wf_l _ _ _ xwf) _ (node_wf_l _ _ _ ywf))
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [ElemOf, elem_of_node, Intersection]
      exact fun a_6 a_7 => ⟨a_6, a_7⟩

theorem in_complement p (X : CoPset) :
  p ∈ complement X <-> p ∉ X := by
  simp [complement]
  simp [Membership.mem]
  rcases X with ⟨X, xwf⟩; simp []
  induction p generalizing X with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;>
      simp [CoPsetRaw.Complement, ElemOf, elem_of_node]
      apply IH; apply node_wf_r _ _ _ xwf
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;>
      simp [CoPsetRaw.Complement, ElemOf, elem_of_node]
      apply IH; apply node_wf_l _ _ _ xwf
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Complement, ElemOf, elem_of_node]

theorem in_diff p (X Y : CoPset) :
  p ∈ X \ Y <-> p ∈ X ∧ p ∉ Y := by
  simp [SDiff.sdiff, diff]
  constructor
  · intros Hnin; obtain ⟨ Hx, Hy ⟩ := (in_inter p X (complement Y)).1 Hnin
    constructor
    · exact Hx
    · exact ((in_complement p Y).1 Hy)
  · rintro ⟨ Hx, Hy ⟩
    simp only [in_inter]
    constructor
    · exact Hx
    · exact ((in_complement p Y).2 Hy)

theorem in_union p (X Y : CoPset) :
  p ∈ X ∪ Y <-> p ∈ X ∨ p ∈ Y := by
  rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩
  simp [Membership.mem]
  constructor
  · induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]
      <;> intros Hin
      apply (IH _ (node_wf_r _ _ _ xwf) _ (node_wf_r _ _ _ ywf))
      apply Hin
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [ElemOf, Union.union, union, CoPsetRaw.Union]
      simp_all [elem_of_node, ElemOf]; intros Hin
      apply (IH _ (node_wf_l _ _ _ xwf) _ (node_wf_l _ _ _ ywf))
      apply Hin
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]

  · induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node] <;> intros Hin <;>
      apply (IH _ (node_wf_r _ _ _ xwf) _ (node_wf_r _ _ _ ywf) Hin)
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [ElemOf, Union.union, union, CoPsetRaw.Union]
      simp_all [elem_of_node, ElemOf]; intros Hin
      apply (IH _ (node_wf_l _ _ _ xwf) _ (node_wf_l _ _ _ ywf) Hin)
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]

theorem not_in_union p (X1 X2 : CoPset) :
  ¬ p ∈ X1 ∪ X2 <-> ¬ p ∈ X1 ∧ ¬ p ∈ X2 := by
  constructor
  · intros Hunion; constructor <;> intro Hnin <;>
    apply Hunion <;> simp [in_union]
    · left; assumption
    · right; assumption
  · rintro ⟨ Hnin1, Hnin2 ⟩; intro Hunion; simp [in_union] at Hunion
    cases Hunion
    · apply Hnin1; assumption
    · apply Hnin2; assumption

theorem subseteq_trans (X Y Z : CoPset) :
  X ⊆ Y ->
  Y ⊆ Z ->
  X ⊆ Z := by
  intros Hxy Hyz p Hx
  exact Hyz p (Hxy p Hx)

instance : Iris.Std.Associative Eq (Union.union (α := CoPset)) where
  assoc := by
    intros X Y Z
    ext p
    simp only [in_union]
    grind only

instance : Iris.Std.Commutative Eq (Union.union (α := CoPset)) where
  comm := by
    intros X Y
    ext p
    simp only [in_union]
    grind only

instance : Iris.Std.Associative Eq (Inter.inter (α := CoPset)) where
  assoc := by
    intros X Y Z
    ext p
    simp only [in_inter]
    grind only

instance : Iris.Std.Commutative Eq (Inter.inter (α := CoPset)) where
  comm := by
    intros X Y
    ext p
    simp only [in_inter]
    grind only

instance union_empty_l : @Std.LawfulLeftIdentity CoPset CoPset Union.union ∅ where
  left_id p := by
    ext p
    simp only [in_union, in_empty, false_or]

instance union_empty_r : @Std.LawfulRightIdentity CoPset CoPset Union.union ∅ where
  right_id p := by
    ext p
    simp only [in_union, in_empty, or_false]

instance inter_full_l : @Std.LawfulLeftIdentity CoPset CoPset Inter.inter full where
  left_id p := by
    ext p
    simp only [in_inter, in_full, true_and]

instance inter_full_r : @Std.LawfulRightIdentity CoPset CoPset Inter.inter full where
  right_id p := by
    ext p
    simp only [in_inter, in_full, and_true]

theorem union_inter_left {X Y Z : CoPset} :
  X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by
  ext p
  simp only [in_union, in_inter]
  rw [or_and_left]

theorem inter_union_left {X Y Z : CoPset} :
  X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by
  ext p
  simp only [in_union, in_inter]
  rw [and_or_left]

def isFinite (X : CoPset) : Bool :=
  CoPsetRaw.isFinite X.tree

/-- Picking an element out of an infinite set -/

/- Provided that the set [X] is infinite, [pick X] yields an element of
this set. Note that [pick] is implemented by depth-first search, so
using it repeatedly to obtain elements [x] and inserting these elements
[x] into some set [Y] will give rise to a very unbalanced tree. -/

def CoPset.pick (X : CoPset) : Pos :=
  (CoPsetRaw.pickRaw X.tree).getD Pos.P1


-- Inverse suffix closure

/-- [suffixes q] is the set of all numbers [p] such that [q] is a suffix
of [p], when these numbers are viewed as sequences of bits. In other words, it
is the set of all numbers that have the suffix [q]. It is always an infinite
set. -/

def suffixes (p : Pos) : CoPset :=
  ⟨CoPsetRaw.suffixesRaw p, coPsetSuffixes_wf p⟩
theorem elem_suffixes p q : p ∈ suffixes q <-> ∃ q', p = q' ++ q := by
  constructor
  · induction q generalizing p with
    | xI q IH =>
      simp only [suffixes, CoPsetRaw.suffixesRaw, Membership.mem]
      rewrite [elem_of_node]
      intros Hin; cases p <;> simp [CoPsetRaw.ElemOf] at Hin
      obtain ⟨ q', Heq ⟩ := (IH _ Hin)
      exists q'; rewrite [Heq]; rfl
    | xO q IH =>
      simp only [suffixes, CoPsetRaw.suffixesRaw, Membership.mem]
      rewrite [elem_of_node]
      intros Hin; cases p <;> simp [CoPsetRaw.ElemOf] at Hin
      obtain ⟨ q', Heq ⟩ := (IH _ Hin)
      exists q'; rewrite [Heq]; rfl
    | xH =>
      intro _; exists p
  · intros Heq; rcases Heq with ⟨ q', Heq ⟩; rewrite [Heq]
    simp only [suffixes, Membership.mem]
    induction q generalizing p <;> simp [CoPsetRaw.suffixesRaw, elem_of_node] <;>
    simp_all [HAppend.hAppend, Pos.app, CoPsetRaw.ElemOf]

/-- Splitting a set -/

/- Every infinite [X : CoPset] can be split into two disjoint parts, which are
infinite sets. Use the functions [splitLeft] and [splitRight] if you
need a constructive witness. -/

def leftRaw : CoPsetRaw → CoPsetRaw
  | CoPsetRaw.leaf false => CoPsetRaw.leaf false
  | CoPsetRaw.leaf true => CoPsetRaw.node true (CoPsetRaw.leaf true) (CoPsetRaw.leaf false)
  | CoPsetRaw.node b l r => CoPsetRaw.node' b (leftRaw l) (leftRaw r)

def rightRaw : CoPsetRaw → CoPsetRaw
  | CoPsetRaw.leaf false => CoPsetRaw.leaf false
  | CoPsetRaw.leaf true => CoPsetRaw.node false (CoPsetRaw.leaf false) (CoPsetRaw.leaf true)
  | CoPsetRaw.node _ l r => CoPsetRaw.node' false (rightRaw l) (rightRaw r)

theorem left_wf t : coPsetWf (leftRaw t) := by
  induction t with
  | leaf b => cases b <;> simp [leftRaw, coPsetWf]
  | node b l r => simp [leftRaw]; apply node'_wf <;> assumption

theorem right_wf t : coPsetWf (rightRaw t) := by
  induction t with
  | leaf b => cases b <;> simp [rightRaw, coPsetWf]
  | node b l r => simp [rightRaw]; apply node'_wf <;> assumption

def splitLeft (X : CoPset) : CoPset :=
  ⟨leftRaw X.tree, left_wf _⟩

def splitRight (X : CoPset) : CoPset :=
  ⟨rightRaw X.tree, right_wf _⟩

def split (X : CoPset) : CoPset × CoPset :=
  (splitLeft X, splitRight X)

instance : Disjoint CoPset where
  disjoint s t := ∀ p, p ∈ s -> p ∈ t -> False

@[symm]
theorem disj_symm (E1 E2 : CoPset) :
  E1 ## E2 -> E2 ## E1 := by
  exact fun Hdisj p HE1 HE2 => Hdisj p HE2 HE1

theorem disj_empty_l (X : CoPset) : ∅ ## X := by
  intro p Hempty HX
  apply CoPset.in_empty Hempty

theorem disj_empty_r (X : CoPset) : X ## ∅ := by
  symm; apply disj_empty_l

theorem disjoint_intersection (X Y : CoPset) : X ## Y ↔ X ∩ Y = ∅ := by
  apply Iff.intro
  · intro H; ext p
    apply Iff.intro
    · intro G
      rw [CoPset.in_inter] at G
      exfalso; apply H p G.1 G.2
    · intro G; exfalso; apply CoPset.in_empty G
  · intro H p G J
    apply CoPset.in_empty (p := p)
    rw [<-H, CoPset.in_inter]
    apply And.intro G J

theorem disj_union {X1 X2 Y : CoPset} :
  (X1 ∪ X2) ## Y <-> X1 ## Y ∧ X2 ## Y := by
  rw [disjoint_intersection, disjoint_intersection, disjoint_intersection]
  rw [Iris.Std.Commutative.comm (R := Eq) (f := Inter.inter), CoPset.inter_union_left]
  rw [Iris.Std.Commutative.comm (R := Eq) (f := Inter.inter) (x := Y)]
  rw [Iris.Std.Commutative.comm (R := Eq) (f := Inter.inter) (y := X2)]
  apply Iff.intro
  · intro C
    apply And.intro
    · ext p
      rw [CoPset.ext_iff] at C
      specialize (C p)
      simp only [CoPset.in_union] at C
      apply Iff.intro
      · intro H; apply (C.mp (Or.inl H))
      · intro C; exfalso; apply (CoPset.in_empty C)
    · ext p
      rw [CoPset.ext_iff] at C
      specialize (C p)
      simp only [CoPset.in_union] at C
      apply Iff.intro
      · intro H; apply (C.mp (Or.inr H))
      · intro C; exfalso; apply (CoPset.in_empty C)
  · rintro ⟨H1, H2⟩
    rw [H1, H2]
    rw [CoPset.union_empty_l.left_id]

instance : DecidableEq CoPset := by
  intro E1 E2
  rcases E1, E2 with ⟨⟨E1⟩, ⟨E2⟩⟩
  simp only [CoPset.mk.injEq]
  infer_instance

instance {E1 E2 : CoPset} : Decidable (E1 ## E2) := by
  rw [disjoint_intersection]
  infer_instance

instance {p : Pos} {E : CoPset} : Decidable (p ∈ E) := by
  simp only [Membership.mem]
  infer_instance

/-- Insert instance for CoPset: insert p X = {p} ∪ X -/
instance : Insert Pos CoPset where
  insert p X := singleton p ∪ X

instance : Singleton Pos CoPset where
  singleton := CoPset.singleton

end Iris.Std.CoPset
