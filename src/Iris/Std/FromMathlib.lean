/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.ExtHashSet

namespace FromMathlib

/-- Two lists without duplicates with the same membership relation are permutations. -/
theorem List.Perm.of_mem {l₁ l₂ : List α} (nd₁ : l₁.Nodup) (nd₂ : l₂.Nodup)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : List.Perm l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons hd tl =>
      have ha : hd ∈ ([] : List α) := (h hd).mpr List.mem_cons_self
      simp at ha
  | cons a l₁' ih =>
    have ha : a ∈ l₂ := (h a).mp List.mem_cons_self
    cases l₂ with
    | nil => simp at ha
    | cons b l₂' =>
      have hb : b ∈ a :: l₁' := (h b).mpr List.mem_cons_self
      have ha_eq_or_mem : a = b ∨ a ∈ l₂' := by
        cases ha with
        | head _ => left; rfl
        | tail _ h' => right; exact h'
      have hb_eq_or_mem : b = a ∨ b ∈ l₁' := by
        cases hb with
        | head _ => left; rfl
        | tail _ h' => right; exact h'
      cases ha_eq_or_mem with
      | inl hab =>
        subst hab
        apply List.Perm.cons
        apply ih
        · exact List.nodup_cons.mp nd₁ |>.right
        · exact List.nodup_cons.mp nd₂ |>.right
        · intro x
          constructor
          · intro hx
            have : x ∈ a :: l₁' := List.mem_cons_of_mem a hx
            have : x ∈ a :: l₂' := (h x).mp this
            cases this with
            | head _ =>
              have : a ∉ l₁' := List.nodup_cons.mp nd₁ |>.left
              contradiction
            | tail _ hx' => exact hx'
          · intro hx
            have : x ∈ a :: l₂' := List.mem_cons_of_mem a hx
            have : x ∈ a :: l₁' := (h x).mpr this
            cases this with
            | head _ =>
              have : a ∉ l₂' := List.nodup_cons.mp nd₂ |>.left
              contradiction
            | tail _ hx' => exact hx'
      | inr hal₂' =>
        cases hb_eq_or_mem with
        | inl hba =>
          have : b ∉ l₂' := List.nodup_cons.mp nd₂ |>.left
          rw [←hba] at hal₂'
          contradiction
        | inr hbl₁' =>
          obtain ⟨l₁'', l₁''', rfl⟩ := List.append_of_mem hbl₁'
          obtain ⟨l₂'', l₂''', rfl⟩ := List.append_of_mem hal₂'
          have step1 : List.Perm (a :: (l₁'' ++ b :: l₁''')) (a :: b :: (l₁'' ++ l₁''')) := by
            apply List.Perm.cons
            exact List.perm_middle
          have step2 : List.Perm (b :: (l₂'' ++ a :: l₂''')) (b :: a :: (l₂'' ++ l₂''')) := by
            apply List.Perm.cons
            exact List.perm_middle
          apply List.Perm.trans step1
          apply List.Perm.trans _ step2.symm
          have swap_step : List.Perm (a :: b :: (l₂'' ++ l₂''')) (b :: a :: (l₂'' ++ l₂''')) :=
            (List.Perm.swap b a (l₂'' ++ l₂'''))
          apply List.Perm.trans _ swap_step
          apply List.Perm.cons
          specialize (@ih (b :: (l₂'' ++ l₂''')))
          apply List.Perm.trans List.perm_middle.symm
          apply ih
          · apply (List.nodup_cons.mp nd₁).right
          · rw [List.nodup_cons]
            rw [List.nodup_cons, List.Perm.nodup_iff List.perm_middle, List.nodup_cons] at nd₂
            apply And.intro
            · intro hin
              apply nd₂.left
              rw [List.mem_append]; rw [List.mem_append] at hin
              cases hin with
              | inl hin =>
                left; exact hin
              | inr hin =>
                right; rw [List.mem_cons]; right; exact hin
            · exact nd₂.right.right
          · intro x
            specialize h x
            rw [List.mem_cons, List.mem_cons, List.mem_append, List.mem_append, List.mem_cons, List.mem_cons] at h
            rw [List.mem_append, List.mem_cons, List.mem_cons, List.mem_append]
            grind only [= List.nodup_cons, = List.nodup_append, =_ List.cons_append,
              usr List.Perm.nodup_iff, = List.mem_append, = List.mem_cons, usr List.Perm.mem_iff]

/-- NB. Copied from Mathlib -/
theorem List.Nodup.of_map (f : α → β) {l : List α} : List.Nodup (List.map f l) → List.Nodup l := by
  refine (List.Pairwise.of_map f) fun _ _ => mt <| fun a => (congrArg f ∘ fun _ => a) α

/-- NB. Copied from Mathlib -/
theorem Pairwise.forall {l : List α} {R : α → α → Prop} (hR : ∀ {a b}, R a b ↔ a ≠ b)
    (hl : l.Pairwise (· ≠ ·)) : ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons]
    rintro x (rfl | hx) y (rfl | hy)
    · simp
    · exact fun a => hR.mpr a
    · exact fun a => hR.mpr a
    · refine ih (List.Pairwise.of_cons hl) hx hy

/-- NB. Copied from Mathlib -/
theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : List.Nodup (List.map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map, List.nodup_cons, List.mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [List.mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

/-- NB. Copied from Mathlib -/
theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : List.Nodup l) :
    (List.map f l).Nodup :=
  List.Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (List.Pairwise.and_mem.1 d)

/-- NB. Copied from Mathlib -/
 theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    List.Nodup l → List.Nodup (List.filterMap f l) :=
  (List.Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n <| h a a' b' (by rw [← e]; exact bm) bm'

/-- NB. Copied from Mathlib -/
theorem Nodup.filter (p : α → Bool) {l} : List.Nodup l → List.Nodup (List.filter p l) := by
  simpa using List.Pairwise.filter p

/-! ## Multiset

NB. Copied and adapted from Mathlib4:
  - Mathlib/Data/Multiset/Defs.lean

A multiset is represented as a quotient of lists under permutation equivalence.
This is a minimal version suitable for Finset.
-/

/-- `Multiset α` is the type of finite multisets (bags) of elements of `α`.
    Represented as a quotient of `List α` by permutation. -/
def Multiset (α : Type u) : Type u := Quotient (List.isSetoid α)

namespace Multiset

variable {α : Type _}

/-- Lift a list to a multiset -/
def ofList (l : List α) : Multiset α := Quot.mk _ l

instance : Coe (List α) (Multiset α) where
  coe := ofList

/-- Membership in a multiset -/
def Mem (s : Multiset α) (a : α) : Prop :=
  Quotient.liftOn s (a ∈ ·) fun _ _ e => propext (List.Perm.mem_iff e)

instance : Membership α (Multiset α) where
  mem := Mem

@[simp]
theorem mem_coe {a : α} {l : List α} : a ∈ (l : Multiset α) ↔ a ∈ l :=
  Iff.rfl

/-- The cardinality of a multiset -/
def card : Multiset α → Nat :=
  Quotient.lift List.length (fun _ _ => List.Perm.length_eq)

@[simp]
theorem card_coe (l : List α) : card (l : Multiset α) = l.length := by
  rfl

/-- A multiset has no duplicates if the underlying list has no duplicates -/
def Nodup (s : Multiset α) : Prop :=
  Quotient.liftOn s List.Nodup fun _ _ p => propext (List.Perm.nodup_iff p)

@[simp]
theorem nodup_coe {l : List α} : Nodup (l : Multiset α) ↔ l.Nodup :=
  Iff.rfl

instance : EmptyCollection (Multiset α) where
  emptyCollection := ofList []

@[simp]
theorem mem_empty {a : α} : ¬(a ∈ (∅ : Multiset α)) := by
  intro h; cases h

@[simp]
theorem card_empty : card (∅ : Multiset α) = 0 := by rfl

@[simp]
theorem nodup_empty : Nodup (∅ : Multiset α) :=
  List.nodup_nil

/-! ### Induction principles -/

/-- Induction principle for multisets: to prove a property for all multisets,
    it suffices to prove it for all lists. -/
@[elab_as_elim]
protected theorem ind {p : Multiset α → Prop} (h : ∀ l : List α, p (ofList l)) (s : Multiset α) :
    p s :=
  Quotient.ind h s

/-- Induction principle for two multisets simultaneously. -/
@[elab_as_elim]
protected theorem ind₂ {p : Multiset α → Multiset β → Prop}
    (h : ∀ (l₁ : List α) (l₂ : List β), p (ofList l₁) (ofList l₂))
    (s : Multiset α) (t : Multiset β) : p s t :=
  Quotient.ind₂ h s t

/-! ### Addition -/

/-- Addition of multisets is list concatenation. -/
def add (s t : Multiset α) : Multiset α :=
  Quotient.lift₂ (fun l₁ l₂ => ofList (l₁ ++ l₂))
    (fun _ _ _ _ p₁ p₂ => Quot.sound (List.Perm.append p₁ p₂))
    s t

instance : HAdd (Multiset α) (Multiset α) (Multiset α) where
  hAdd := add

@[simp]
theorem coe_add (l₁ l₂ : List α) : (l₁ : Multiset α) + (l₂ : Multiset α) = (l₁ ++ l₂ : Multiset α) :=
  rfl

@[simp]
theorem mem_add {a : α} {s t : Multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t := by
  induction s using Multiset.ind with | h l₁ =>
  induction t using Multiset.ind with | h l₂ =>
  show a ∈ (l₁ ++ l₂ : Multiset α) ↔ a ∈ (l₁ : Multiset α) ∨ a ∈ (l₂ : Multiset α)
  simp only [mem_coe, List.mem_append]

/-! ### Lift operations -/

/-- Lift a function from lists to multisets. The function must respect permutations. -/
protected def lift {β : Type _} (f : List α → β)
    (h : ∀ l₁ l₂ : List α, l₁.Perm l₂ → f l₁ = f l₂) : Multiset α → β :=
  Quotient.lift f h

/-- Lift a binary function from lists to multisets. -/
protected def lift₂ {β γ : Type _} (f : List α → List β → γ)
    (h : ∀ l₁ : List α, ∀ l₂ : List β, ∀ l₃ : List α, ∀ l₄ : List β,
      l₁.Perm l₃ → l₂.Perm l₄ → f l₁ l₂ = f l₃ l₄) :
    Multiset α → Multiset β → γ :=
  Quotient.lift₂ f h

/-! ### Map operation -/

/-- Map a function over a multiset.
    Since multisets are quotients by permutation, mapping respects permutation. -/
def map {β : Type _} (f : α → β) (s : Multiset α) : Multiset β :=
  Quotient.lift (fun l => ofList (l.map f))
    (fun _ _ h => Quot.sound (List.Perm.map f h))
    s

@[simp]
theorem map_coe {β : Type _} (f : α → β) (l : List α) :
    map f (l : Multiset α) = (l.map f : Multiset β) := by
  rfl

theorem mem_map {β : Type _} {f : α → β} {s : Multiset α} {b : β} :
    b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b := by
  induction s using Multiset.ind with | h l =>
  simp only [map_coe, mem_coe, List.mem_map]

end Multiset

/-! ## Finset

NB. Copied and adapted from Mathlib4:
  - Mathlib/Data/Finset/Defs.lean
  - Mathlib/Data/Finset/Card.lean
  - Mathlib/Data/Finset/Basic.lean

A finset is a finite set represented as a multiset with no duplicates.
-/

/-- `Finset α` is the type of finite sets of elements of `α`.
    Represented as a multiset with a proof of no duplicates.

    NB. Copied from Mathlib/Data/Finset/Defs.lean -/
structure Finset (α : Type u) where
  val : Multiset α
  nodup : Multiset.Nodup val

namespace Finset

variable {α : Type _}

/-- Membership in a finset -/
instance : Membership α (Finset α) where
  mem s a := a ∈ s.val

@[simp]
theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.val := by
  rfl

/-- The empty finset -/
instance : EmptyCollection (Finset α) where
  emptyCollection := ⟨∅, Multiset.nodup_empty⟩

@[simp]
theorem mem_empty {a : α} : ¬(a ∈ (∅ : Finset α)) := by
  exact Multiset.mem_empty

/-- Extensionality for finsets -/
@[ext]
theorem ext {s t : Finset α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t := by
  cases s with | mk sval snd =>
  cases t with | mk tval tnd =>
  congr
  induction sval, tval using Multiset.ind₂ with | h a b
  apply Quotient.sound
  apply List.Perm.of_mem snd tnd
  intro x
  exact h x

/-- The cardinality (number of elements) of a finset.
    NB. Copied from Mathlib/Data/Finset/Card.lean -/
def card (s : Finset α) : Nat := Multiset.card s.val

@[simp]
theorem card_empty : card (∅ : Finset α) = 0 := by
  exact Multiset.card_empty

/-- Create a finset from a list with no duplicates -/
def ofList (l : List α) (nd : l.Nodup) : Finset α :=
  ⟨l, nd⟩

@[simp]
theorem mem_ofList {l : List α} {nd : l.Nodup} {a : α} :
    a ∈ ofList l nd ↔ a ∈ l := by
  simp [ofList, Membership.mem, Multiset.Mem, Multiset.ofList]

@[simp]
theorem card_ofList {l : List α} {nd : l.Nodup} :
    card (ofList l nd) = l.length := by
  rfl

/-- Singleton finset -/
def singleton (a : α) : Finset α :=
  ofList [a] (by simp [List.Nodup])

instance : Singleton α (Finset α) where
  singleton := singleton

@[simp]
theorem mem_singleton {a b : α} :
    a ∈ ({b} : Finset α) ↔ a = b := by
  show a ∈ (Multiset.ofList [b]) ↔ a = b
  simp only [Multiset.mem_coe, List.mem_singleton]

@[simp]
theorem card_singleton (a : α) :
    card ({a} : Finset α) = 1 := by
  rfl

@[elab_as_elim]
protected theorem ind {p : Finset α → Prop}
    (h : ∀ (l : List α) (nd : l.Nodup), p (ofList l nd))
    (s : Finset α) : p s := by
  cases s with | mk val nodup =>
  induction val using Multiset.ind with | h l =>
  exact h l nodup

/-- Induction on a finset. This is a convenience version of `Finset.ind`
    that can be used with the `induction` tactic. -/
@[elab_as_elim]
protected theorem induction_on {p : Finset α → Prop} (s : Finset α)
    (h : ∀ (l : List α) (nd : l.Nodup), p (ofList l nd)) : p s :=
  Finset.ind h s

/-- Induction principle for two finsets simultaneously. -/
@[elab_as_elim]
protected theorem ind₂ {p : Finset α → Finset β → Prop}
    (h : ∀ (l₁ : List α) (nd₁ : l₁.Nodup) (l₂ : List β) (nd₂ : l₂.Nodup),
      p (ofList l₁ nd₁) (ofList l₂ nd₂))
    (s : Finset α) (t : Finset β) : p s t := by
  cases s with | mk val₁ nodup₁ =>
  cases t with | mk val₂ nodup₂ =>
  induction val₁, val₂ using Multiset.ind₂ with | h l₁ l₂ =>
  exact h l₁ nodup₁ l₂ nodup₂

/-- Case analysis on a finset: either it's empty or it has at least one element. -/
@[elab_as_elim]
protected theorem cases_on {p : Finset α → Prop} (s : Finset α)
    (h_empty : p ∅)
    (h_cons : ∀ (a : α) (l : List α) (nd : (a :: l).Nodup), p (ofList (a :: l) nd)) :
    p s := by
  induction s using Finset.ind with | h l nd =>
  cases l with
  | nil => exact h_empty
  | cons hd tl =>
    exact h_cons hd tl nd

/-! ### Basic operations -/

/-- Insert an element into a finset. If the element is already present, the set is unchanged. -/
def insert [DecidableEq α] (a : α) (s : Finset α) : Finset α :=
  ⟨Multiset.lift (fun l => if a ∈ l then (l : Multiset α) else (a :: l : Multiset α))
    (fun l₁ l₂ p => by
      by_cases h₁ : a ∈ l₁
      · have h₂ : a ∈ l₂ := (List.Perm.mem_iff p).mp h₁
        simp [h₁, h₂]
        exact Quot.sound p
      · have h₂ : a ∉ l₂ := fun h => h₁ ((List.Perm.mem_iff p.symm).mp h)
        simp [h₁, h₂]
        exact Quot.sound (List.Perm.cons a p))
    s.val,
   by
    induction s using Finset.ind with | h l nd =>
    simp only [Multiset.lift, Quotient.lift, ofList, Multiset.ofList]
    by_cases h : a ∈ l
    · simp [h]; exact nd
    · simp [h]; exact List.nodup_cons.mpr ⟨h, nd⟩⟩

instance [DecidableEq α] : Insert α (Finset α) where
  insert := insert

@[simp]
theorem mem_insert [DecidableEq α] {a b : α} {s : Finset α} :
    a ∈ insert b s ↔ a = b ∨ a ∈ s := by
  induction s using Finset.ind with | h l nd =>
  show a ∈ (if b ∈ l then (l : Multiset α) else (b :: l : Multiset α)) ↔ a = b ∨ a ∈ l
  by_cases h : b ∈ l
  · simp only [h, ite_true, Multiset.mem_coe]
    constructor
    · intro ha; exact Or.inr ha
    · intro hab
      cases hab with
      | inl heq => subst heq; exact h
      | inr ha => exact ha
  · simp [h, Multiset.mem_coe, List.mem_cons]

/-- Subset relation on finsets. -/
def subset (s t : Finset α) : Prop := ∀ ⦃x⦄, x ∈ s → x ∈ t

instance : HasSubset (Finset α) where
  Subset := subset

@[simp]
theorem subset_def {s t : Finset α} : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t := Iff.rfl

theorem subset_refl (s : Finset α) : s ⊆ s := fun _ h => h

theorem subset_trans {s t u : Finset α} : s ⊆ t → t ⊆ u → s ⊆ u :=
  fun h₁ h₂ _ hx => h₂ (h₁ hx)

theorem empty_subset (s : Finset α) : ∅ ⊆ s := fun _ h => absurd h mem_empty

/-- Union of two finsets. -/
def union [DecidableEq α] (s t : Finset α) : Finset α :=
  ⟨Multiset.lift₂ (fun l₁ l₂ => (l₁.filter (· ∉ l₂) ++ l₂ : Multiset α))
    (fun l₁ l₂ l₃ l₄ p₁ p₂ => by
      apply Quot.sound
      -- Step 1: filter (· ∉ l₂) l₁ ~ filter (· ∉ l₂) l₃
      have step1 : (l₁.filter (fun x => decide (x ∉ l₂))).Perm (l₃.filter (fun x => decide (x ∉ l₂))) :=
        List.Perm.filter (fun x => decide (x ∉ l₂)) p₁
      -- Step 2: filter (· ∉ l₂) l₃ = filter (· ∉ l₄) l₃ because l₂ ~ l₄
      have mem_equiv : ∀ x, x ∈ l₂ ↔ x ∈ l₄ := fun x => List.Perm.mem_iff p₂
      have step2 : l₃.filter (fun x => decide (x ∉ l₂)) = l₃.filter (fun x => decide (x ∉ l₄)) := by
        apply List.filter_congr
        intro a _
        simp only [decide_eq_decide]
        constructor
        · intro h hx; exact h ((mem_equiv a).mpr hx)
        · intro h hx; exact h ((mem_equiv a).mp hx)
      -- Step 3: Combine with l₂ ~ l₄ to get the full permutation
      exact List.Perm.append (step1.trans (step2 ▸ List.Perm.refl _)) p₂)
    s.val t.val,
   by
    induction s using Finset.ind with | h l₁ nd₁ =>
    induction t using Finset.ind with | h l₂ nd₂ =>
    simp only [Multiset.lift₂, Quotient.lift₂, ofList, Multiset.ofList]
    apply List.nodup_append.mpr
    constructor
    · exact Nodup.filter _ nd₁
    constructor
    · exact nd₂
    · intro a ha b hb
      simp only [List.mem_filter, decide_eq_true_eq] at ha
      intro heq
      subst heq
      exact ha.2 hb⟩

instance [DecidableEq α] : Union (Finset α) where
  union := union

@[simp]
theorem mem_union [DecidableEq α] {a : α} {s t : Finset α} :
    a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := by
  induction s using Finset.ind with | h l₁ nd₁ =>
  induction t using Finset.ind with | h l₂ nd₂ =>
  show a ∈ (l₁.filter (· ∉ l₂) ++ l₂ : Multiset α) ↔ a ∈ (l₁ : Multiset α) ∨ a ∈ (l₂ : Multiset α)
  simp only [Multiset.mem_coe, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    match h with
    | Or.inl ⟨h1, _⟩ => exact Or.inl h1
    | Or.inr h => exact Or.inr h
  · intro h
    match h with
    | Or.inl h =>
      by_cases hm : a ∈ l₂
      · exact Or.inr hm
      · exact Or.inl ⟨h, hm⟩
    | Or.inr h => exact Or.inr h

/-- Intersection of two finsets. -/
def inter [DecidableEq α] (s t : Finset α) : Finset α :=
  ⟨Multiset.lift₂ (fun l₁ l₂ => (l₁.filter (· ∈ l₂) : Multiset α))
    (fun l₁ l₂ l₃ l₄ p₁ p₂ => by
      apply Quot.sound
      -- Step 1: Use p₁ to get l₁.filter (· ∈ l₂).Perm (l₃.filter (· ∈ l₂))
      have step1 : (l₁.filter (fun x => decide (x ∈ l₂))).Perm (l₃.filter (fun x => decide (x ∈ l₂))) :=
        List.Perm.filter (fun x => decide (x ∈ l₂)) p₁
      -- Step 2: Show l₃.filter (· ∈ l₂) = l₃.filter (· ∈ l₄) because l₂.Perm l₄
      have mem_equiv : ∀ x, x ∈ l₂ ↔ x ∈ l₄ := fun x => List.Perm.mem_iff p₂
      have step2 : l₃.filter (fun x => decide (x ∈ l₂)) = l₃.filter (fun x => decide (x ∈ l₄)) := by
        apply List.filter_congr
        intro a _
        simp only [decide_eq_decide]
        exact mem_equiv a
      exact step1.trans (step2 ▸ List.Perm.refl _))
    s.val t.val,
   by
    induction s using Finset.ind with | h l₁ nd₁ =>
    induction t using Finset.ind with | h l₂ nd₂ =>
    simp only [Multiset.lift₂, Quotient.lift₂, ofList, Multiset.ofList]
    exact Nodup.filter _ nd₁⟩

instance [DecidableEq α] : Inter (Finset α) where
  inter := inter

@[simp]
theorem mem_inter [DecidableEq α] {a : α} {s t : Finset α} :
    a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := by
  induction s using Finset.ind with | h l₁ nd₁ =>
  induction t using Finset.ind with | h l₂ nd₂ =>
  show a ∈ (l₁.filter (· ∈ l₂) : Multiset α) ↔ a ∈ (l₁ : Multiset α) ∧ a ∈ (l₂ : Multiset α)
  simp only [Multiset.mem_coe, List.mem_filter, decide_eq_true_eq]

/-- Set difference. -/
def sdiff [DecidableEq α] (s t : Finset α) : Finset α :=
  ⟨Multiset.lift₂ (fun l₁ l₂ => (l₁.filter (· ∉ l₂) : Multiset α))
    (fun l₁ l₂ l₃ l₄ p₁ p₂ => by
      apply Quot.sound
      -- Step 1: filter (· ∉ l₂) l₁ ~ filter (· ∉ l₂) l₃
      have step1 : (l₁.filter (fun x => decide (x ∉ l₂))).Perm (l₃.filter (fun x => decide (x ∉ l₂))) :=
        List.Perm.filter (fun x => decide (x ∉ l₂)) p₁
      -- Step 2: filter (· ∉ l₂) l₃ = filter (· ∉ l₄) l₃ because l₂ ~ l₄
      have mem_equiv : ∀ x, x ∈ l₂ ↔ x ∈ l₄ := fun x => List.Perm.mem_iff p₂
      have step2 : l₃.filter (fun x => decide (x ∉ l₂)) = l₃.filter (fun x => decide (x ∉ l₄)) := by
        apply List.filter_congr
        intro a _
        simp only [decide_eq_decide]
        constructor
        · intro h hx; exact h ((mem_equiv a).mpr hx)
        · intro h hx; exact h ((mem_equiv a).mp hx)
      exact step1.trans (step2 ▸ List.Perm.refl _))
    s.val t.val,
   by
    induction s using Finset.ind with | h l₁ nd₁ =>
    induction t using Finset.ind with | h l₂ nd₂ =>
    simp only [Multiset.lift₂, Quotient.lift₂, ofList, Multiset.ofList]
    exact Nodup.filter _ nd₁⟩

instance [DecidableEq α] : SDiff (Finset α) where
  sdiff := sdiff

@[simp]
theorem mem_sdiff [DecidableEq α] {a : α} {s t : Finset α} :
    a ∈ s \ t ↔ a ∈ s ∧ a ∉ t := by
  induction s using Finset.ind with | h l₁ nd₁ =>
  induction t using Finset.ind with | h l₂ nd₂ =>
  show a ∈ (l₁.filter (· ∉ l₂) : Multiset α) ↔ a ∈ (l₁ : Multiset α) ∧ a ∉ (l₂ : Multiset α)
  simp only [Multiset.mem_coe, List.mem_filter, decide_eq_true_eq]

/-! ### Fold operation -/

/-- A binary operation is left-commutative if `f (f acc x) y = f (f acc y) x`.
    This is the condition needed for fold to be well-defined on sets. -/
def LeftCommutative (f : β → α → β) : Prop :=
  ∀ acc x y, f (f acc x) y = f (f acc y) x

/-- Helper lemma: left-commutative foldl respects permutations -/
theorem List.foldl_perm_of_leftComm {f : β → α → β} (hcomm : LeftCommutative f)
    {l₁ l₂ : List α} (h : l₁.Perm l₂) (init : β) :
    l₁.foldl f init = l₂.foldl f init := by
  induction h generalizing init with
  | nil => rfl
  | cons _ _ ih => simp [List.foldl]; exact ih (f init _)
  | swap x y l =>
    simp only [List.foldl]
    rw [hcomm]
  | trans _ _ ih₁ ih₂ => exact Eq.trans (ih₁ init) (ih₂ init)

/-- Fold over a finite set with a left-commutative operation.
    The operation must be left-commutative to ensure the result is independent
    of the order in which elements are processed.
-/
def fold {α β : Type _} (f : β → α → β) (hcomm : LeftCommutative f)
    (init : β) (s : Finset α) : β :=
  Quotient.liftOn s.val
    (fun l => l.foldl f init)
    (fun _ _ perm => List.foldl_perm_of_leftComm hcomm perm init)

@[simp]
theorem fold_empty {f : β → α → β} {hcomm : LeftCommutative f} {init : β} :
    fold f hcomm init ∅ = init := by
  rfl

@[simp]
theorem fold_singleton {f : β → α → β} {hcomm : LeftCommutative f} {init : β} {a : α} :
    fold f hcomm init {a} = f init a := by
  rfl

/-- Basic computation lemma: fold on ofList reduces to list foldl -/
theorem fold_ofList (f : β → α → β) (hcomm : LeftCommutative f)
    (init : β) (l : List α) (nd : l.Nodup) :
    fold f hcomm init (ofList l nd) = l.foldl f init := by
  rfl

/-! ### Example: Cardinality using fold -/

/-- Example: Count function for cardinality -/
def count_fn : Nat → α → Nat := fun acc _ => acc + 1

/-- Proof that count_fn is left-commutative -/
theorem count_fn_leftComm : LeftCommutative (count_fn : Nat → α → Nat) := by
  intro acc x y
  rfl

/-- Cardinality of a finite set using fold -/
def card' (s : Finset α) : Nat :=
  fold count_fn count_fn_leftComm 0 s

theorem card'_empty : card' (∅ : Finset α) = 0 := by
  unfold card' fold
  rfl

theorem card'_singleton (a : α) : card' ({a} : Finset α) = 1 := by
  unfold card' fold count_fn
  rfl

end Finset

/-! ### Conversion from ExtHashSet to Finset -/

namespace ExtHashSet

open Std

variable {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]

def ext_hash_set_elems {β : α → Type _} (x : ExtDHashMap α β) : Multiset (Σ x, β x) :=
  Quotient.lift (fun x => x.toList) (fun _ _ h => Quotient.sound (Std.DHashMap.equiv_iff_toList_perm.mp h)) x.inner

theorem ext_hash_set_elems_no_dup {β : α → Type _} (x : ExtDHashMap α β)
  : ((ext_hash_set_elems x).map Sigma.fst).Nodup := by
  simp only [ext_hash_set_elems]
  induction x.inner using Quot.ind with | mk a =>
  simp [Multiset.nodup_coe]
  apply DHashMap.nodup_keys

def keysToFiniteSet {β : α → Type _} (x : ExtDHashMap α β) : Finset α :=
  ⟨(ext_hash_set_elems x).map Sigma.fst, ext_hash_set_elems_no_dup x⟩

end ExtHashSet

end FromMathlib
