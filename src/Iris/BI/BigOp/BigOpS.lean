/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Sergei Stepanenko
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.Instances
import Iris.Std.TC
import Iris.Std.GenSets

import Iris.BI.DerivedLawsLater

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open Iris.Std.Set
open BIBase

/-! # Big Separating Conjunction over Sets

- Rocq Iris: `iris/bi/big_op.v`, Section `sep_set` -/

variable {PROP : Type _} [BI PROP]
variable {S : Type _} {A : Type _}

namespace BigSepS


/-! ## Monotonicity and Congruence -/

private theorem mono_list {Φ Ψ : A → PROP} {l : List A}
    (h : ∀ x, x ∈ l → Φ x ⊢ Ψ x) :
    bigOpL sep (fun _ x => Φ x) l ⊢ bigOpL sep (fun _ x => Ψ x) l := by
  induction l with
  | nil => exact Entails.rfl
  | cons x xs ih =>
    simp only [BigOpL.cons]
    apply sep_mono
    · exact h x (List.Mem.head xs)
    · apply ih
      intro y hy
      exact h y (List.Mem.tail x hy)

variable [LawfulFiniteSet S A]

/-- Corresponds to `big_sepS_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x := by
  unfold bigSepS
  apply (equiv_iff.mp (BigOpS.bigOpS_bigOpL Φ X)).mp.trans
  apply Entails.trans _ (equiv_iff.mp (BigOpS.bigOpS_bigOpL Ψ X).symm).mp
  apply mono_list
  intro x; rw [Set.mem_toList]
  apply h

/-- Corresponds to `big_sepS_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : A → PROP} {X : S} {n : Nat}
    (h : ∀ x, x ∈ X → Φ x ≡{n}≡ Ψ x) :
    ([∗set] x ∈ X, Φ x) ≡{n}≡ ([∗set] x ∈ X, Ψ x) := by
  unfold bigSepS
  apply BigOpS.congr_dist h

/-- Corresponds to `big_sepS_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊣⊢ ([∗set] x ∈ X, Ψ x) := by
  unfold bigSepS
  apply equiv_iff.mp
  apply BigOpS.congr
  intro x Hin
  apply equiv_iff.mpr (h x Hin)

/-- Corresponds to `big_sepS_mono'` in Rocq Iris. -/
theorem mono' {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x :=
  mono (fun x _ => h x)

/-- Corresponds to `big_sepS_flip_mono'` in Rocq Iris. -/
theorem flip_mono' {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Ψ x ⊢ Φ x) :
    ([∗set] x ∈ X, Ψ x) ⊢ [∗set] x ∈ X, Φ x :=
  mono' h

/-! ## Basic Structural Lemmas -/

/-- Corresponds to `big_sepS_elements` in Rocq Iris. -/
theorem elements {Φ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊣⊢ [∗list] x ∈ toList X, Φ x := by
  unfold bigSepS bigSepL
  apply equiv_iff.mp
  apply BigOpS.bigOpS_bigOpL

/-- Corresponds to `big_sepS_empty` in Rocq Iris. -/
@[simp]
theorem empty {Φ : A → PROP} :
    ([∗set] x ∈ (∅ : S), Φ x) ⊣⊢ emp := by
  unfold bigSepS
  simp only [BigOpS.empty]
  exact .rfl

/-- Corresponds to `big_sepS_empty'` in Rocq Iris. -/
theorem empty' {P : PROP} [Affine P] {Φ : A → PROP} :
    P ⊢ [∗set] x ∈ (∅ : S), Φ x :=
  Affine.affine.trans empty.2

/-- Corresponds to `big_sepS_emp` in Rocq Iris. -/
theorem emp' {X : S} :
    ([∗set] _x ∈ X, emp) ⊣⊢ (emp : PROP) := by
  unfold bigSepS
  apply equiv_iff.mp
  simp only [BigOpS.const_unit]

/-- Corresponds to `big_sepS_singleton` in Rocq Iris. -/
theorem singleton {Φ : A → PROP} {x : A} :
    ([∗set] y ∈ ({x} : S), Φ y) ⊣⊢ Φ x := by
  unfold bigSepS
  apply equiv_iff.mp
  simp only [BigOpS.singleton]

/-- Corresponds to `big_sepS_union` in Rocq Iris. -/
theorem union {Φ : A → PROP} {X Y : S}
    (h : X ## Y) :
    ([∗set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ Y, Φ y) := by
  unfold bigSepS
  apply equiv_iff.mp
  simp only [BigOpS.union h]

/-- Corresponds to `big_sepS_insert` in Rocq Iris. -/
theorem insert {Φ : A → PROP} {X : S} {x : A}
    (h : x ∉ X) :
    ([∗set] y ∈ {x} ∪ X, Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X, Φ y := by
  unfold bigSepS
  apply equiv_iff.mp
  simp [BigOpS.insert h]

/-- Corresponds to `big_sepS_delete` in Rocq Iris. -/
theorem delete {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X \ {x}, Φ y := by
  unfold bigSepS
  rw [<-insert_delete h, insert_union, ←delete_diff
    , delete_union, delete_delete, delete_diff
    , delete_diff, diff_all, union_empty_left]
  apply insert
  rw [mem_diff, mem_singleton]
  intro ⟨_, h⟩; apply h rfl

/-! ## Typeclass Instances -/

/-- Corresponds to `big_sepS_empty_persistent` in Rocq Iris. -/
instance empty_persistent {Φ : A → PROP} :
    Persistent ([∗set] x ∈ (∅ : S), Φ x) where
  persistent := by
    unfold bigSepS
    simp [BigOpS.empty]
    exact persistently_emp_intro (PROP := PROP) (P := emp)

/-- Corresponds to `big_sepS_persistent` in Rocq Iris. -/
theorem persistent_cond {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Persistent (Φ x)) :
    Persistent ([∗set] x ∈ X, Φ x) where
  persistent := by
    unfold bigSepS
    apply (equiv_iff.mp (BigOpS.bigOpS_bigOpL Φ X)).mp.trans
    apply Entails.trans _ (equiv_iff.mp (persistently_ne.eqv (BigOpS.bigOpS_bigOpL _ X)).symm).mp
    have : ∀ (x : A), x ∈ toList X → Persistent (Φ x) := by
      intro x; rw [Set.mem_toList]; apply h
    generalize toList X = l at this
    induction l with
    | nil => exact persistently_emp_intro
    | cons x xs ih =>
      simp only [BigOpL.cons]
      have h1 : Φ x ⊢ <pers> Φ x := (this x (List.Mem.head xs)).persistent
      have h2 : ∀ (x : A), x ∈ xs → Persistent (Φ x) := by
        intro x xin; apply this x (List.Mem.tail _ xin)
      exact (sep_mono h1 (ih h2)).trans persistently_sep_2

/-- Corresponds to `big_sepS_persistent'` in Rocq Iris. -/
instance persistent {Φ : A → PROP} {X : S}
    [h : ∀ x, Persistent (Φ x)] :
    Persistent ([∗set] x ∈ X, Φ x) :=
  persistent_cond (Φ := Φ) (X := X) (fun _ _ => h _)

/-- Corresponds to `big_sepS_empty_affine` in Rocq Iris. -/
instance empty_affine {Φ : A → PROP} :
    Affine ([∗set] x ∈ (∅ : S), Φ x) where
  affine := by
    have h := empty (Φ := Φ) (S := S)
    exact h.1

private theorem affine_list {Φ : A → PROP} {l : List A}
    (h : ∀ x, x ∈ l → Affine (Φ x)) :
    bigOpL sep (fun _ x => Φ x) l ⊢ emp := by
  induction l with
  | nil => exact Entails.rfl
  | cons x xs ih =>
    simp only [BigOpL.cons]
    have h1 : Φ x ⊢ emp := (h x (List.Mem.head xs)).affine
    have h2 : bigOpL sep (fun _ y => Φ y) xs ⊢ emp :=
      ih (fun y hy => h y (List.Mem.tail x hy))
    exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepS_affine` in Rocq Iris. -/
theorem affine_cond {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Affine (Φ x)) :
    Affine ([∗set] x ∈ X, Φ x) where
  affine := by
    unfold bigSepS
    apply (equiv_iff.mp (BigOpS.bigOpS_bigOpL Φ X)).mp.trans
    apply affine_list
    intro x hmem_list
    apply h; rw [<-Set.mem_toList]; apply hmem_list

/-- Corresponds to `big_sepS_affine'` in Rocq Iris. -/
instance affine {Φ : A → PROP} {X : S}
    [h : ∀ x, Affine (Φ x)] :
    Affine ([∗set] x ∈ X, Φ x) :=
  affine_cond (fun _ _ => h _)

/-- Empty big separating conjunction is timeless. -/
instance big_sepS_empty_timeless [Timeless (emp : PROP)] (Φ : A → PROP) :
    Timeless ([∗set] x ∈ (∅ : S), Φ x) where
  timeless := by
    apply (later_mono (BigSepS.empty (Φ := Φ) (S := S)).mp).trans
    apply (Timeless.timeless (P := emp)).trans
    apply except0_mono
    apply (BigSepS.empty (Φ := Φ) (S := S)).mpr

/-- Big separating conjunction is timeless if all elements are. -/
theorem big_sepS_timeless [Timeless (emp : PROP)] (Φ : A → PROP) (X : S)
    (h : ∀ x, x ∈ X → Timeless (Φ x)) :
    Timeless ([∗set] x ∈ X, Φ x) where
  timeless := by
    unfold bigSepS
    apply (BigOpS.closed (fun P => ▷ P ⊢ ◇ P) (fun x => Φ x) X)
    · exact Timeless.timeless (P := emp)
    · intros x y hx hy
      exact later_sep.1.trans (sep_mono hx hy) |>.trans except0_sep.2
    · intro x hx
      exact (h x hx).timeless

/-- Big separating conjunction is timeless if the function always produces timeless props. -/
instance big_sepS_timeless' [Timeless (emp : PROP)] (Φ : A → PROP) (X : S)
    [∀ x, Timeless (Φ x)] :
    Timeless ([∗set] x ∈ X, Φ x) :=
  big_sepS_timeless Φ X (fun _ _ => inferInstance)

-- /-- Corresponds to `big_sepS_union_2` in Rocq Iris. -/
-- theorem union_2 {Φ : A → PROP} {X Y : S}
--     [h : ∀ x, TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
--     ⊢ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ Y, Φ y) -∗ ([∗set] y ∈ X ∪ Y, Φ y) := by
--   have h_core : ∀ X : S, ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ Y, Φ y) ⊢ ([∗set] y ∈ X ∪ Y, Φ y) := by
--     intro X
--     induction X using set_ind with
--     | hemp =>
--       refine (sep_mono_l empty.mp).trans ?_
--       refine emp_sep.mp.trans ?_
--       rw [union_empty_left]
--       apply Entails.rfl
--     | hadd x X' hnotin IH =>
--       have hdisj : {x} ## X' := by
--         intro y ⟨hmem1, hmem2⟩
--         by_cases hyx : y = x
--         · subst hyx; simp_all
--         · simp only [mem_singleton] at hmem1
--           apply hyx hmem1
--       rw [insert_union_comm, insert_union, insert_union]
--       by_cases hx_in_Y : x ∈ Y
--       · rw [union_comm (s₁ := X'), union_assoc, ←insert_union (s := Y)
--           , insert_idem hx_in_Y, union_comm (s₁ := Y)]
--         apply (sep_mono_l ((union (Φ := Φ) hdisj).trans (sep_congr_l singleton)).mp).trans
--         apply sep_assoc.mp.trans
--         apply (sep_mono_r IH).trans
--         apply sep_elim_r
--       · have hins : ([∗set] y ∈ {x} ∪ X', Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X', Φ y :=
--           (union (Φ := Φ) hdisj).trans (sep_congr_l singleton)
--         apply (sep_mono_l ((union (Φ := Φ) hdisj).trans (sep_congr_l singleton)).mp).trans
--         apply sep_assoc.mp.trans
--         refine (sep_mono_r IH).trans ?_
--         apply (insert _).mpr
--         simp [mem_union, hnotin, hx_in_Y]
--   have h1 : ([∗set] y ∈ X, Φ y) ⊢ ([∗set] y ∈ Y, Φ y) -∗ ([∗set] y ∈ X ∪ Y, Φ y) :=
--     wand_intro' ((sep_comm (PROP := PROP)).1.trans (h_core X))
--   exact entails_wand h1

/-- Corresponds to `big_sepS_insert_2` in Rocq Iris. -/
theorem insert_2 {Φ : A → PROP} {X : S} {x : A}
    [TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
    Φ x ⊢ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ {x} ∪ X, Φ y) := by
  apply wand_intro
  by_cases hx : x ∈ X
  · have hdel := (@delete PROP _ S A _ Φ X x hx).1
    refine (sep_mono_r hdel).trans ?_
    refine (sep_assoc (PROP := PROP)).2.trans ?_
    refine (sep_mono_l sep_elim_l).trans ?_
    have hunion_sub_X : ({x} ∪ X) ⊆ X := fun y hy => by
      rw [mem_union] at hy
      cases hy with
      | inl h =>
        rw [mem_singleton] at h; cases h; assumption
      | inr h => exact h
    have hX_sub_union : X ⊆ ({x} ∪ X) := fun y hy => by
      rw [mem_union]
      right; exact hy
    have heq : ([∗set] y ∈ {x} ∪ X, Φ y) ⊣⊢ ([∗set] y ∈ X, Φ y) := by
      unfold bigSepS
      rw [←insert_union, insert_idem hx]
      exact .rfl
    exact (@delete PROP _ S A _ Φ X x hx).2.trans heq.2
  · have hinsert := (@insert PROP _ S A _ Φ X x hx).2
    exact hinsert

/-- Corresponds to `big_sepS_insert_2'` in Rocq Iris. -/
theorem insert_2' {Φ : A → PROP} {X : S} {x : A}
    [TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
    ⊢ Φ x -∗ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ X ∪ {x}, Φ y) := by
  have heq : ([∗set] y ∈ X ∪ {x}, Φ y) ⊣⊢
             ([∗set] y ∈ {x} ∪ X, Φ y) := by
    unfold bigSepS
    rw [union_comm]
    exact .rfl
  have h1 : ⊢ Φ x -∗ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ {x} ∪ X, Φ y) :=
    entails_wand insert_2
  exact h1.trans (wand_mono_r (wand_mono_r heq.2))

-- /-! ## Function Insertion -/

-- /-- Function update: returns `b` if `k = i`, otherwise `f k`. -/
-- def fnInsert {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) (k : K) : B :=
--   if k = i then b else f k

-- theorem fnInsert_same {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) :
--     fnInsert f i b i = b := by simp [fnInsert]

-- theorem fnInsert_ne {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) (k : K) (h : k ≠ i) :
--     fnInsert f i b k = f k := by simp [fnInsert, h]

-- /-- Corresponds to `big_sepS_fn_insert` in Rocq Iris. -/
-- theorem fn_insert {B : Type _} {Ψ : A → B → PROP} {f : A → B} {X : S} {x : A} {b : B}
--     (h : x ∉ X) :
--     ([∗set] y ∈ {x} ∪ X, Ψ y (fnInsert f x b y)) ⊣⊢
--       Ψ x b ∗ [∗set] y ∈ X, Ψ y (f y) := by
--   have hins := insert (Φ := fun y => Ψ y (fnInsert f x b y)) h
--   have hhead : Ψ x (fnInsert f x b x) ⊣⊢ Ψ x b := by
--     simp only [fnInsert_same]
--     exact .rfl
--   have htail : ([∗set] y ∈ X, Ψ y (fnInsert f x b y)) ⊣⊢
--       [∗set] y ∈ X, Ψ y (f y) := by
--     apply proper
--     intro y hy
--     have hne : y ≠ x := by
--       intro heq
--       rw [←heq] at h
--       rw [hy] at h
--       cases h
--     simp only [fnInsert_ne f x b y hne]
--     exact .rfl
--   exact hins.trans ⟨(sep_mono hhead.1 htail.1), (sep_mono hhead.2 htail.2)⟩

-- /-- Corresponds to `big_sepS_fn_insert'` in Rocq Iris. -/
-- theorem fn_insert' {Φ : A → PROP} {X : S} {x : A} {P : PROP}
--     (h : x ∉ X) :
--     ([∗set] y ∈ {x} ∪ X, fnInsert Φ x P y) ⊣⊢
--       P ∗ [∗set] y ∈ X, Φ y :=
--   fn_insert (Ψ := fun _ P => P) (f := Φ) (b := P) h

/-- Corresponds to `big_sepS_delete_2` in Rocq Iris. -/
theorem delete_2 {Φ : A → PROP} {X : S} {x : A}
    [hAff : Affine (Φ x)] :
    Φ x ⊢ ([∗set] y ∈ X \ {x}, Φ y) -∗ [∗set] y ∈ X, Φ y := by
  apply wand_intro
  by_cases hx : x ∈ X
  · exact (delete hx).2
  · refine (sep_mono_l hAff.affine).trans emp_sep.1 |>.trans ?_
    rw [<-delete_diff, delete_notin hx]
    exact .rfl

/-! ## Lookup and Access -/

/-- Corresponds to `big_sepS_elem_of` in Rocq Iris. -/
theorem elem_of {Φ : A → PROP} {X : S} {x : A}
    (hmem : x ∈ X) :
    [TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))] →
    ([∗set] y ∈ X, Φ y) ⊢ Φ x
  | TCOr.l => by
    refine (delete hmem).1.trans ?_
    apply sep_comm.mp.trans
    exact sep_elim_r
  | TCOr.r => by
    have hdel := delete (Φ := Φ) (S := S) hmem
    refine hdel.1.trans ?_
    exact sep_elim_l

/-- Corresponds to `big_sepS_elem_of_acc` in Rocq Iris. -/
theorem elem_of_acc {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗set] y ∈ X, Φ y)) := by
  have hdel := delete (Φ := Φ) (S := S) h
  refine hdel.1.trans ?_
  apply sep_mono_r
  exact wand_intro' hdel.2

/-! ## List/Set Conversion -/

/-- Corresponds to `big_sepS_list_to_set` in Rocq Iris. -/
theorem list_to_set {Φ : A → PROP} {l : List A}
    (h : l.Nodup) :
    ([∗set] x ∈ (ofList l : S), Φ x) ⊣⊢ [∗list] x ∈ l, Φ x := by
  unfold bigSepS bigSepL
  apply (equiv_iff.mp (BigOpS.bigOpS_bigOpL _ _)).trans
  exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ (toList_ofList h).symm)

-- /-! ## Filter -/

-- /-- Corresponds to `big_sepS_filter'` in Rocq Iris. -/
-- theorem filter' (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X : S} :
--     ([∗set] y ∈ filter (fun x => decide (φ x)) X, Φ y) ⊣⊢
--     ([∗set] y ∈ X, if φ y then Φ y else emp) := by
--   unfold bigSepS
--   have hperm := FiniteSetLaws.toList_filter (S := S) X (fun x => decide (φ x))
--   have h1 := equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)
--   refine h1.trans ?_
--   have h2 : ∀ l : List A,
--       bigOpL sep emp (fun _ => Φ) (l.filter (fun x => decide (φ x))) ⊣⊢
--       bigOpL sep emp (fun _ x => if φ x then Φ x else emp) l := by
--     intro l
--     induction l with
--     | nil =>
--       simp only [List.filter, BigOpL.nil]
--       exact .rfl
--     | cons y ys ih =>
--       simp only [BigOpL.cons]
--       by_cases hy : φ y
--       · have hdec : decide (φ y) = true := by simp [hy]
--         have hfilt : List.filter (fun x => decide (φ x)) (y :: ys) =
--             y :: List.filter (fun x => decide (φ x)) ys := by
--           simp [List.filter, hdec]
--         rw [hfilt]
--         simp only [BigOpL.cons, hy, ↓reduceIte]
--         exact sep_congr_r ih
--       · have hdec : decide (φ y) = false := by simp [hy]
--         have hfilt : List.filter (fun x => decide (φ x)) (y :: ys) =
--             List.filter (fun x => decide (φ x)) ys := by
--           simp [List.filter, hdec]
--         rw [hfilt]
--         simp only [hy, ↓reduceIte]
--         exact ih.trans (emp_sep (PROP := PROP)).symm
--   exact h2 (toList X)

-- /-- Corresponds to `big_sepS_filter` in Rocq Iris. -/
-- theorem filter [BIAffine PROP] (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X : S} :
--     ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) X, Φ y) ⊣⊢
--     ([∗set] y ∈ X, ⌜φ y⌝ → Φ y) := by
--   refine (filter' φ).trans (proper fun y _ => ?_)
--   by_cases hy : φ y
--   · simp only [hy, ↓reduceIte]
--     exact true_imp (PROP := PROP).symm
--   · simp only [hy, ↓reduceIte]
--     constructor
--     · apply imp_intro'
--       apply pure_elim_l (R := Φ y)
--       intro hf
--       exact hf.elim
--     · exact Affine.affine (self := BIAffine.affine _)

-- /-- Corresponds to `big_sepS_filter_acc'` in Rocq Iris. -/
-- theorem filter_acc' (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X Y : S}
--     (h : ∀ y, FiniteSet.mem y Y = true → φ y → FiniteSet.mem y X = true) :
--     ([∗set] y ∈ X, Φ y) ⊢
--       ([∗set] y ∈ Y, if φ y then Φ y else emp) ∗
--       (([∗set] y ∈ Y, if φ y then Φ y else emp) -∗ [∗set] y ∈ X, Φ y) := by
--   -- First, show that filter φ Y ⊆ X
--   have hfilter_sub : FiniteSet.filter (fun x => decide (φ x)) Y ⊆ X := by
--     intro z hz
--     have ⟨hz_Y, hz_φ⟩ := FiniteSetLaws.mem_filter Y (fun x => decide (φ x)) z |>.mp hz
--     have : φ z := of_decide_eq_true hz_φ
--     exact h z hz_Y this
--   -- Use union_diff to decompose X
--   have ⟨hdisj, hmem_decomp⟩ := FiniteSetLaws.union_diff X (FiniteSet.filter (fun x => decide (φ x)) Y) hfilter_sub
--   -- X = filterY ∪ (X \ filterY), and they are disjoint
--   have hX_decomp : X = FiniteSet.filter (fun x => decide (φ x)) Y ∪
--       FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y) := by
--     apply @FiniteSetLaws.ext S A _ _
--     intro z
--     apply Bool.eq_iff_iff.mpr
--     constructor
--     · intro hz; rw [FiniteSetLaws.mem_union]; exact (hmem_decomp z).mp hz
--     · intro hz; rw [FiniteSetLaws.mem_union] at hz; exact (hmem_decomp z).mpr hz
--   -- Apply union: [∗set] X = [∗set] filterY ∗ [∗set] (X \ filterY)
--   have hunion := @union PROP _ S A _ _ _ Φ (FiniteSet.filter (fun x => decide (φ x)) Y)
--       (FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y)) hdisj
--   have hX_split : ([∗set] y ∈ X, Φ y) ⊣⊢
--       ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) Y, Φ y) ∗
--       ([∗set] y ∈ FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y), Φ y) := by
--     -- Convert equality to equivalence, then compose with hunion
--     have heq : ([∗set] y ∈ X, Φ y) = ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) Y ∪
--         FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y), Φ y) :=
--       congrArg (fun s => bigSepS Φ s) hX_decomp
--     exact BIBase.BiEntails.of_eq heq |>.trans hunion
--   -- Apply filter': [∗set] filterY = [∗set] y ∈ Y, if φ y then Φ y else emp
--   have hfilter := @filter' PROP _ S A _ _ _ φ _ Φ Y
--   -- Combine: [∗set] X ⊣⊢ A ∗ Z where A = [∗set] Y with filter, Z = [∗set] (X \ filterY)
--   have hcombined : ([∗set] y ∈ X, Φ y) ⊣⊢
--       ([∗set] y ∈ Y, if φ y then Φ y else emp) ∗
--       ([∗set] y ∈ FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y), Φ y) :=
--     hX_split.trans (sep_congr_l hfilter)
--   -- Now prove the goal: X ⊢ A ∗ (A -∗ X)
--   -- From X ⊣⊢ A ∗ Z, we have X ⊢ A ∗ Z
--   refine hcombined.1.trans ?_
--   -- Need: A ∗ Z ⊢ A ∗ (A -∗ X)
--   apply sep_mono
--   · -- Prove: A ⊢ A
--     exact BIBase.Entails.rfl
--   · -- Prove: Z ⊢ A -∗ X
--     apply wand_intro'
--     -- Goal becomes: A ∗ Z ⊢ X
--     -- This is exactly hcombined.2
--     exact hcombined.2

-- /-- Corresponds to `big_sepS_filter_acc` in Rocq Iris. -/
-- theorem filter_acc [BIAffine PROP] (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X Y : S}
--     (h : ∀ y, FiniteSet.mem y Y = true → φ y → FiniteSet.mem y X = true) :
--     ([∗set] y ∈ X, Φ y) ⊢
--       ([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) ∗
--       (([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) -∗ [∗set] y ∈ X, Φ y) := by
--   have h1 := @filter_acc' PROP _ S A _ _ _ φ _ Φ X Y h
--   have h_equiv : ([∗set] y ∈ Y, if φ y then Φ y else emp) ⊣⊢ ([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) := by
--     apply proper
--     intro y _
--     by_cases hy : φ y
--     · simp only [hy, ↓reduceIte]
--       exact true_imp (PROP := PROP).symm
--     · simp only [hy, ↓reduceIte]
--       constructor
--       · apply imp_intro'
--         apply pure_elim_l (R := Φ y)
--         intro hf
--         exact hf.elim
--       · exact Affine.affine (self := BIAffine.affine _)
--   refine h1.trans ?_
--   apply sep_mono
--   · exact h_equiv.1
--   · apply wand_mono h_equiv.2
--     exact BIBase.Entails.rfl

/-! ## Separation Logic Combinators -/

/-- Corresponds to `big_sepS_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ X, Ψ y) := by
  unfold bigSepS
  have := @BigOpS.op_distrib PROP _ _ _ sep emp _ _ (fun x => Φ x) (fun x => Ψ x) X
  exact equiv_iff.mp this

/-- Corresponds to `big_sepS_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y) ⊢
    ([∗set] y ∈ X, Ψ y) -∗
    ([∗set] y ∈ X, Φ y ∗ Ψ y) := by
  apply wand_intro (PROP := PROP)
  refine sep_comm (PROP := PROP).1.trans ?_
  have h := @sep' PROP _ S A _ Ψ Φ X
  refine h.2.trans ?_
  apply mono
  intro x _
  exact sep_comm (PROP := PROP).1

/-- Corresponds to `big_sepS_and` in Rocq Iris. -/
theorem and' {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗set] y ∈ X, Φ y) ∧ ([∗set] y ∈ X, Ψ y) := by
  apply and_intro
  · exact mono (fun _ _ => and_elim_l)
  · exact mono (fun _ _ => and_elim_r)

/-! ## Pure Propositions -/

-- /-- Corresponds to `big_sepS_pure_1` in Rocq Iris. -/
-- theorem pure_1 {φ : A → Prop} {X : S} :
--     ([∗set] y ∈ X, ⌜φ y⌝) ⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) := by
--   refine elements.1.trans ?_

--   refine BigSepL.pure_1.trans (pure_mono ?_)
--   intro h y hmem
--   have hlist : List.Mem y (toList X) := (FiniteSetLaws.mem_toList X y).mpr hmem
--   have ⟨i, hget⟩ := List.getElem?_of_mem hlist
--   exact h i y hget

-- /-- Corresponds to `big_sepS_affinely_pure_2` in Rocq Iris. -/
-- theorem affinely_pure_2 {φ : A → Prop} {X : S} :
--     (<affine> (⌜∀ y, y ∈ X → φ y⌝ : PROP)) ⊢ ([∗set] y ∈ X, <affine> ⌜φ y⌝) := by
--   have hlist : (<affine> ⌜∀ k x, (toList X)[k]? = some x → φ x⌝ : PROP) ⊢
--       ([∗list] _k ↦ x ∈ toList X, <affine> ⌜φ x⌝) :=
--     BigSepL.affinely_pure_2
--   refine (affinely_mono (pure_mono ?_)).trans hlist
--   intro h k x hget
--   have hmem : List.Mem x (toList X) := List.mem_of_getElem? hget
--   have hset_mem := (FiniteSetLaws.mem_toList X x).mp hmem
--   exact h x hset_mem

-- /-- Corresponds to `big_sepS_pure` in Rocq Iris. -/
-- theorem pure [BIAffine PROP] {φ : A → Prop} {X : S} :
--     ([∗set] y ∈ X, ⌜φ y⌝) ⊣⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
--   ⟨pure_1, (affine_affinely _).2.trans <| affinely_pure_2.trans (mono fun _ _ => affinely_elim)⟩

/-- Corresponds to `big_sepS_forall` in Rocq Iris. -/
theorem forall' [BIAffine PROP] {Φ : A → PROP} {X : S}
    [hPers : ∀ x, Persistent (Φ x)] :
    ([∗set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x) := by
  constructor
  · apply forall_intro
    intro x
    apply imp_intro'
    apply pure_elim_l
    intro hmem
    haveI hAff : ∀ y, Affine (Φ y) := fun y => BIAffine.affine (Φ y)
    exact @elem_of PROP _ S A _ Φ X x hmem (@TCOr.l _ _ (hAff))
  · unfold bigSepS
    have hmem_all : ∀ x, x ∈ (toList X) → x ∈ X := by intro x; rw [Set.mem_toList]; simp
    have helper : ∀ l, (∀ x, x ∈ l → x ∈ X) →
        (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ bigOpL sep (fun _ => Φ) l := by
      intro l hl
      induction l with
      | nil =>
        simp only [BigOpL.nil]
        exact Affine.affine (self := BIAffine.affine _)
      | cons y ys ih =>
        simp only [BigOpL.cons]
        have hy_mem : y ∈ X := hl y (List.Mem.head ys)
        have hhead : (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ Φ y :=
          (forall_elim y).trans ((and_intro (pure_intro hy_mem) .rfl).trans imp_elim_r)
        refine and_self.2.trans (and_mono_l hhead) |>.trans ?_
        refine (persistent_and_sep_1 (P := Φ y)).trans ?_
        exact sep_mono_r (ih (fun x hx => hl x (List.Mem.tail y hx)))
    apply Entails.trans _ (equiv_iff.mp (BigOpS.bigOpS_bigOpL _ X).symm).mp
    exact helper (toList X) hmem_all

/-! ## Modal Operators -/

-- /-- Corresponds to `big_sepS_persistently` in Rocq Iris. -/
-- theorem persistently [BIAffine PROP] {Φ : A → PROP} {X : S} :
--     (<pers> ([∗set] y ∈ X, Φ y)) ⊣⊢ [∗set] y ∈ X, <pers> (Φ y) :=
--   (persistently_congr elements).trans (BigSepL.persistently.trans elements.symm)

/-- Corresponds to `big_sepS_dup` in Rocq Iris. -/
theorem dup {P : PROP} [hAff : Affine P] {X : S} :
    ⊢ □ (P -∗ P ∗ P) -∗ P -∗ [∗set] _x ∈ X, P := by
  unfold bigSepS
  apply wand_intro
  apply wand_intro
  refine (sep_mono_l emp_sep.1).trans ?_
  induction X using set_ind with
  | hemp =>
    simp only [BigOpS.empty]
    exact sep_elim_r.trans hAff.affine
  | hadd y ys hnin ih =>
    simp only [insert_union]
    refine (sep_mono_l (intuitionistically_sep_idem (PROP := PROP)).2).trans ?_
    refine sep_assoc (PROP := PROP).1.trans ?_
    refine (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans ?_
    refine sep_assoc (PROP := PROP).2.trans ?_
    refine (sep_mono_l ih).trans ?_
    apply Entails.trans _ (insert hnin).symm.mp
    exact sep_comm (PROP := PROP).1

-- /-- Corresponds to `big_sepS_later` in Rocq Iris. -/
-- theorem later [BIAffine PROP] {Φ : A → PROP} {X : S} :
--     iprop(▷ [∗set] y ∈ X, Φ y) ⊣⊢ [∗set] y ∈ X, ▷ Φ y :=
--   (later_congr elements).trans (BigSepL.later.trans elements.symm)

-- /-- Corresponds to `big_sepS_later_2` in Rocq Iris. -/
-- theorem later_2 {Φ : A → PROP} {X : S} :
--     ([∗set] y ∈ X, ▷ Φ y) ⊢ iprop(▷ [∗set] y ∈ X, Φ y) :=
--   elements.1.trans (BigSepL.later_2.trans (later_mono elements.2))

-- /-- Corresponds to `big_sepS_laterN` in Rocq Iris. -/
-- theorem laterN [BIAffine PROP] {Φ : A → PROP} {n : Nat} {X : S} :
--     iprop(▷^[n] [∗set] y ∈ X, Φ y) ⊣⊢ [∗set] y ∈ X, ▷^[n] Φ y := by
--   induction n with
--   | zero => exact .rfl
--   | succ m ih => exact (later_congr ih).trans later

-- /-- Corresponds to `big_sepS_laterN_2` in Rocq Iris. -/
-- theorem laterN_2 {Φ : A → PROP} {n : Nat} {X : S} :
--     ([∗set] y ∈ X, ▷^[n] Φ y) ⊢ iprop(▷^[n] [∗set] y ∈ X, Φ y) := by
--   induction n with
--   | zero => exact .rfl
--   | succ m ih => exact later_2.trans (later_mono ih)

/-! ## Introduction and Elimination -/

private theorem intro_list {Φ : A → PROP} {X : S} {l : List A}
    (hmem : ∀ x, x ∈ l → x ∈ X) :
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x)) ⊢ bigOpL sep (fun _ => Φ) l := by
  induction l with
  | nil => exact Affine.affine (self := intuitionistically_affine (PROP := PROP) _)
  | cons y ys ih =>
    have hy := hmem y (List.Mem.head ys)
    refine intuitionistically_sep_idem.2.trans (sep_mono ?_ (ih (fun x hx => hmem x (List.Mem.tail y hx))))
    exact intuitionistically_elim.trans <|
      (forall_elim y).trans <| (and_intro (pure_intro hy) .rfl).trans imp_elim_r

/-- Corresponds to `big_sepS_intro` in Rocq Iris. -/
theorem intro {Φ : A → PROP} {X : S} :
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x)) ⊢ [∗set] x ∈ X, Φ x := by
  unfold bigSepS
  apply Entails.trans _ (equiv_iff.mp (BigOpS.bigOpS_bigOpL _ X).symm).mp
  apply intro_list (X := X)
  intro x hmem_list
  rw [<-Set.mem_toList]
  assumption

/-- Corresponds to `big_sepS_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) -∗
    [∗set] x ∈ X, Ψ x := by
  apply BI.wand_intro
  have h1 : iprop(□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) ⊢ [∗set] x ∈ X, (Φ x -∗ Ψ x) := intro
  refine (sep_mono_r h1).trans ?_
  refine sep'.2.trans ?_
  apply mono
  intro _ _
  exact wand_elim_r (PROP := PROP)

/-- Corresponds to `big_sepS_wand` in Rocq Iris. -/
theorem wand' {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢
    ([∗set] x ∈ X, Φ x -∗ Ψ x) -∗
    [∗set] x ∈ X, Ψ x := by
  apply BI.wand_intro (PROP := PROP)
  refine sep_comm (PROP := PROP).1.trans ?_
  refine sep'.2.trans ?_
  apply mono
  intro _ _
  exact wand_elim_l (PROP := PROP)

/-- Corresponds to `big_sepS_elem_of_acc_impl` in Rocq Iris. -/
theorem elem_of_acc_impl {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢
    Φ x ∗
    (∀ (Ψ : A → PROP),
       (□ (∀ y, ⌜y ∈ X⌝ → ⌜x ≠ y⌝ → Φ y -∗ Ψ y)) -∗
     Ψ x -∗
     ([∗set] y ∈ X, Ψ y)) := by
  have hdel := (delete (Φ := Φ) h).1
  refine hdel.trans (sep_mono_r ?_)
  apply forall_intro
  intro Ψ
  apply BI.wand_intro
  apply BI.wand_intro
  have hdel_Ψ := (delete (Φ := Ψ) (S := S) h).2
  have h1 : iprop(□ (∀ y, ⌜y ∈ X⌝ → ⌜x ≠ y⌝ → Φ y -∗ Ψ y)) ⊢
      iprop(□ (∀ y, ⌜y ∈ (X \ {x})⌝ → Φ y -∗ Ψ y)) := by
    apply intuitionistically_mono
    apply forall_intro
    intro y
    apply imp_intro'
    apply pure_elim_l
    intro hy_diff
    rw [mem_diff, mem_singleton] at hy_diff
    exact (forall_elim y).trans <|
      (imp_mono_l (pure_mono fun _ => hy_diff.left)).trans true_imp.1 |>.trans <|
      (imp_mono_l (pure_mono fun _ => (fun e => hy_diff.right e.symm))).trans true_imp.1
  refine sep_assoc.1.trans ?_
  refine (sep_mono_r (sep_comm (PROP := PROP).1)).trans ?_
  refine (sep_comm (PROP := PROP).1).trans ?_
  refine sep_assoc.1.trans ?_
  refine (sep_mono_r ?_).trans hdel_Ψ
  refine (sep_mono_l h1).trans ?_
  refine (sep_comm (PROP := PROP).1).trans ?_
  have h_impl := @impl PROP _ S A _ Φ Ψ (X \ {x})
  refine (sep_mono_l h_impl).trans ?_
  refine (sep_comm (PROP := PROP).1).trans ?_
  exact wand_elim_r (PROP := PROP)

/-! ## Subsumption -/

-- /-- Corresponds to `big_sepS_subseteq` in Rocq Iris. -/
-- theorem subseteq {Φ : A → PROP} {X Y : S}
--     [h : ∀ x, Affine (Φ x)]
--     (hsub : Y ⊆ X) :
--     ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ Y, Φ x := by
--   unfold bigSepS

--   sorry
--   -- have ⟨l, hperm⟩ := FiniteSetLaws.toList_subset X Y hsub
--   -- exact BigSepL.submseteq hperm

/-! ## Commuting Lemmas -/

-- /-- Corresponds to `big_sepS_sepL` in Rocq Iris. -/
-- theorem sepL {B : Type _} (Φ : A → Nat → B → PROP) (X : S) (l : List B) :
--     ([∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y) ⊣⊢
--       ([∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y) := by
--   calc [∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y
--       _ ⊣⊢ [∗list] x ∈ toList X, [∗list] k↦y ∈ l, Φ x k y := elements (Φ := fun x => [∗list] k↦y ∈ l, Φ x k y)
--       _ ⊣⊢ [∗list] k↦y ∈ l, [∗list] x ∈ toList X, Φ x k y :=
--           @BigSepL.sepL PROP _ A B (fun _ x k y => Φ x k y) (toList X) l
--       _ ⊣⊢ [∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y :=
--           equiv_iff.mp <| BigSepL.congr (fun k y => equiv_iff.mpr <| elements (Φ := fun x => Φ x k y).symm)

-- /-- Corresponds to `big_sepS_sepS` in Rocq Iris. -/
-- theorem sepS {B : Type _} {T : Type _} [DecidableEq B] [FiniteSet T B] [FiniteSet T B]
--     (Φ : A → B → PROP) (X : S) (Y : T) :
--     ([∗set] x ∈ X, [∗set] y ∈ Y, Φ x y) ⊣⊢
--       ([∗set] y ∈ Y, [∗set] x ∈ X, Φ x y) := by
--   calc [∗set] x ∈ X, [∗set] y ∈ Y, Φ x y
--       _ ⊣⊢ [∗list] x ∈ toList X, [∗set] y ∈ Y, Φ x y := elements (Φ := fun x => [∗set] y ∈ Y, Φ x y)
--       _ ⊣⊢ [∗list] x ∈ toList X, [∗list] y ∈ toList Y, Φ x y :=
--           equiv_iff.mp <| BigOpS.congr (fun _ x => equiv_iff.mpr <| elements (Φ := Φ x))
--       _ ⊣⊢ [∗list] y ∈ toList Y, [∗list] x ∈ toList X, Φ x y :=
--           @BigOpS.sepL PROP _ A B (fun _ x _ y => Φ x y) (toList X) (toList Y)
--       _ ⊣⊢ [∗list] y ∈ toList Y, [∗set] x ∈ X, Φ x y :=
--           equiv_iff.mp <| BigSepL.congr (fun _ y => equiv_iff.mpr <| elements (Φ := fun x => Φ x y).symm)
--       _ ⊣⊢ [∗set] y ∈ Y, [∗set] x ∈ X, Φ x y := elements (Φ := fun y => [∗set] x ∈ X, Φ x y).symm

-- /-- Corresponds to `big_sepS_sepM` in Rocq Iris. -/
-- theorem sepM {B : Type _} {M : Type _} {K : Type _}
--     [DecidableEq K] [FiniteMap M K B] [FiniteMapLaws M K B]
--     (Φ : A → K → B → PROP) (X : S) (m : M) :
--     ([∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y) ⊣⊢
--       ([∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y) := by
--   calc [∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y
--       _ ⊣⊢ [∗list] x ∈ toList X, [∗map] k↦y ∈ m, Φ x k y :=
--           elements (Φ := fun x => [∗map] k↦y ∈ m, Φ x k y)
--       _ ⊣⊢ [∗list] x ∈ toList X, [∗list] kv ∈ toList m, Φ x kv.1 kv.2 := by
--           apply equiv_iff.mp; apply BigSepL.congr
--           intro _ x; unfold bigSepM; exact equiv_iff.mpr .rfl
--       _ ⊣⊢ [∗list] kv ∈ toList m, [∗list] x ∈ toList X, Φ x kv.1 kv.2 :=
--           @BigSepL.sepL PROP _ A (K × B) (fun _ x _ kv => Φ x kv.1 kv.2) (toList X) (toList m)
--       _ ⊣⊢ [∗list] kv ∈ toList m, [∗set] x ∈ X, Φ x kv.1 kv.2 := by
--           apply equiv_iff.mp; apply BigSepL.congr
--           intro _ kv; exact equiv_iff.mpr (elements (Φ := fun x => Φ x kv.1 kv.2)).symm
--       _ ⊣⊢ [∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y :=
--           equiv_iff.mp <| BigSepL.congr fun _ kv => .rfl

end BigSepS

end Iris.BI
