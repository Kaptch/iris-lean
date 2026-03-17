/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace FromMathlib

-- FIXME: it's not in Mathlib as far as I can tell
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
-/

/-- `Multiset α` is the type of finite multisets of elements of `α`.
    Represented as a quotient of `List α` by permutation. -/
def Multiset (α : Type u) : Type u := Quotient (List.isSetoid α)

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

theorem List.foldl_comm_left {f : β → α → β} (hcomm : LeftCommutative f)
  (init : β) (a : α) (l : List α) :
    List.foldl f (f init a) l = f (List.foldl f init l) a := by
  induction l generalizing init with
  | nil => simp
  | cons x xs IH =>
    simp only [List.foldl_cons]
    have comm : f (f init a) x = f (f init x) a := hcomm init a x
    rw [comm, IH]

namespace Multiset

variable {α : Type _}

def ofList (l : List α) : Multiset α := Quot.mk _ l

instance : Coe (List α) (Multiset α) where
  coe := ofList

def Mem (s : Multiset α) (a : α) : Prop :=
  Quotient.liftOn s (a ∈ ·) fun _ _ e => propext (List.Perm.mem_iff e)

instance : Membership α (Multiset α) where
  mem := Mem

@[simp]
theorem mem_coe {a : α} {l : List α} : a ∈ (l : Multiset α) ↔ a ∈ l :=
  Iff.rfl

/-- The size of a multiset -/
def size : Multiset α → Nat :=
  Quotient.lift List.length (fun _ _ => List.Perm.length_eq)

@[simp]
theorem card_coe (l : List α) : size (l : Multiset α) = l.length := by
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
theorem nodup_empty : Nodup (∅ : Multiset α) :=
  List.nodup_nil

/-- Singleton finset -/
def singleton (a : α) : Multiset α :=
  ofList [a]

instance : Singleton α (Multiset α) where
  singleton := singleton

@[simp]
theorem size_singleton : size ({x} : Multiset α) = 1 := by rfl

@[simp]
theorem nodup_singleton : Nodup ({x} : Multiset α) :=
  List.nodup_cons.mpr ⟨(List.mem_nil_iff _).mp, List.nodup_nil⟩

/-! ### Induction principles -/

/-- Induction principle for multisets: to prove a property for all multisets,
    it suffices to prove it for all lists. -/
@[elab_as_elim]
protected theorem ind {p : Multiset α → Prop} (h : ∀ l : List α, p (ofList l)) (s : Multiset α) :
    p s :=
  Quotient.ind h s

protected def recursor {p : Multiset α → Type _} (h : ∀ l : List α, p (Quotient.mk _ l))
  (H : ∀ (a b : List α) (p : a ≈ b), Quotient.sound p ▸ h a = h b)
  (s : Multiset α) :
    p s :=
  Quotient.rec h H s

@[elab_as_elim]
protected theorem ind₂ {p : Multiset α → Multiset β → Prop}
    (h : ∀ (l₁ : List α) (l₂ : List β), p (ofList l₁) (ofList l₂))
    (s : Multiset α) (t : Multiset β) : p s t :=
  Quotient.ind₂ h s t

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

theorem size_empty : S = ∅ ↔ size (S : Multiset α) = 0 := by
  induction S using Multiset.ind with | h a =>
  simp only [card_coe, List.length_eq_zero_iff, EmptyCollection.emptyCollection]
  simp only [ofList]
  cases a with
  | nil => simp
  | cons x xs =>
    simp only [reduceCtorEq, iff_false]
    intro heq
    have t : List.Perm (x :: xs) [] := Quotient.exact heq
    rw [List.perm_nil] at t
    simp at t

/-! ### Fold operation -/

/-- Fold over a multiset with a left-commutative operation.
    The operation must be left-commutative to ensure the result is independent
    of the order of elements.
-/
def fold {α β : Type _} (f : β → α → β) (hcomm : LeftCommutative f)
    (init : β) (s : Multiset α) : β :=
  Quotient.liftOn s
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
    (init : β) (l : List α) :
    fold f hcomm init (ofList l) = l.foldl f init := by
  rfl

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

/-- Concatenation of multisets is list concatenation. -/
def concat (s t : Multiset α) : Multiset α :=
  Quotient.lift₂ (fun l₁ l₂ => ofList (l₁ ++ l₂))
    (fun _ _ _ _ p₁ p₂ => Quot.sound (List.Perm.append p₁ p₂))
    s t

@[simp]
theorem coe_concat (l₁ l₂ : List α) : concat (l₁ : Multiset α) (l₂ : Multiset α) = (l₁ ++ l₂ : Multiset α) :=
  rfl

@[simp]
theorem mem_concat {a : α} {s t : Multiset α} : a ∈ concat s t ↔ a ∈ s ∨ a ∈ t := by
  induction s using Multiset.ind with | h l₁ =>
  induction t using Multiset.ind with | h l₂ =>
  show a ∈ (l₁ ++ l₂ : Multiset α) ↔ a ∈ (l₁ : Multiset α) ∨ a ∈ (l₂ : Multiset α)
  simp only [mem_coe, List.mem_append]

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

def Mem (a : α) (s : Finset α) : Prop :=
  a ∈ s.val

/-- Membership in a finset -/
local instance inst_mem : Membership α (Finset α) where
  mem s a := Mem a s

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.val := by
  rfl

/-- The empty finset -/
local instance inst_empty : EmptyCollection (Finset α) where
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
  exact Quotient.sound (List.Perm.of_mem snd tnd (fun x => h x))

/-- The cardinality (number of elements) of a finset.
    NB. Copied from Mathlib/Data/Finset/Card.lean -/
def card (s : Finset α) : Nat := Multiset.size s.val

theorem card_empty : S = ∅ ↔ card (S : Finset α) = 0 := by
  simp only [card]
  rw [<-Multiset.size_empty]
  constructor
  · intro h
    subst h
    rfl
  · intro h
    cases S with | mk val nodup =>
    cases val using Multiset.ind with | h l =>
    cases l with
    | nil => rfl
    | cons hd tl => simp [List.length, Multiset.size_empty] at h

/-- Create a finset from a list with no duplicates -/
def ofList (l : List α) (nd : l.Nodup) : Finset α :=
  ⟨l, nd⟩

@[simp]
theorem mem_ofList {l : List α} {nd : l.Nodup} {a : α} :
    a ∈ ofList l nd ↔ a ∈ l := by
  simp [ofList, Membership.mem, Mem, Multiset.Mem, Multiset.ofList]

@[simp]
theorem card_ofList {l : List α} {nd : l.Nodup} :
    card (ofList l nd) = l.length := by
  rfl

/-- Singleton finset -/
def singleton (a : α) : Finset α :=
  ofList [a] (by simp [List.Nodup])

local instance inst_singleton : Singleton α (Finset α) where
  singleton := singleton

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

@[elab_as_elim]
protected theorem induction_on {p : Finset α → Prop} (s : Finset α)
    (h : ∀ (l : List α) (nd : l.Nodup), p (ofList l nd)) : p s :=
  Finset.ind h s

@[elab_as_elim]
protected theorem ind₂ {p : Finset α → Finset β → Prop}
    (h : ∀ (l₁ : List α) (nd₁ : l₁.Nodup) (l₂ : List β) (nd₂ : l₂.Nodup),
      p (ofList l₁ nd₁) (ofList l₂ nd₂))
    (s : Finset α) (t : Finset β) : p s t := by
  cases s with | mk val₁ nodup₁ =>
  cases t with | mk val₂ nodup₂ =>
  induction val₁, val₂ using Multiset.ind₂ with | h l₁ l₂ =>
  exact h l₁ nodup₁ l₂ nodup₂

private theorem ofList_perm {l₁ l₂ : List α} (perm : l₁.Perm l₂) (nd₁ : l₁.Nodup) (nd₂ : l₂.Nodup) :
    ofList l₁ nd₁ = ofList l₂ nd₂ := by
  ext a
  simp only [mem_ofList]
  exact List.Perm.mem_iff perm

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

local instance inst_insert [DecidableEq α] : Insert α (Finset α) where
  insert := insert

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

def union [DecidableEq α] (s t : Finset α) : Finset α :=
  ⟨Multiset.lift₂ (fun l₁ l₂ => (l₁.filter (· ∉ l₂) ++ l₂ : Multiset α))
    (fun l₁ l₂ l₃ l₄ p₁ p₂ => by
      apply Quotient.sound
      have step1 : (l₁.filter (fun x => decide (x ∉ l₂))).Perm (l₃.filter (fun x => decide (x ∉ l₂))) :=
        List.Perm.filter (fun x => decide (x ∉ l₂)) p₁
      have mem_equiv : ∀ x, x ∈ l₂ ↔ x ∈ l₄ := fun x => List.Perm.mem_iff p₂
      have step2 : l₃.filter (fun x => decide (x ∉ l₂)) = l₃.filter (fun x => decide (x ∉ l₄)) := by
        apply List.filter_congr
        intro a _
        simp only [decide_eq_decide]
        constructor
        · intro h hx; exact h ((mem_equiv a).mpr hx)
        · intro h hx; exact h ((mem_equiv a).mp hx)
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

local instance inst_union [DecidableEq α] : Union (Finset α) where
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

/-- Cardinality of disjoint union. -/
theorem card_union [DecidableEq α] {s t : Finset α} (h : ∀ x, ¬(x ∈ s ∧ x ∈ t)) :
    card (s ∪ t) = card s + card t := by
  induction s using Finset.ind with | h l₁ nd₁ =>
  induction t using Finset.ind with | h l₂ nd₂ =>
  simp only [card, union, inst_union]
  simp only [Multiset.lift₂, Quotient.lift₂, ofList, Multiset.ofList]
  show Multiset.size (Quot.mk _ (List.filter (fun x => decide (x ∉ l₂)) l₁ ++ l₂)) =
       Multiset.size (Quot.mk _ l₁) + Multiset.size (Quot.mk _ l₂)
  show (List.filter (fun x => decide (x ∉ l₂)) l₁ ++ l₂).length = l₁.length + l₂.length
  rw [List.length_append]
  have disjoint : ∀ x, x ∈ l₁ → x ∉ l₂ := by
    intro x hx₁
    have : x ∈ (ofList l₁ nd₁ : Finset α) := by
      rw [mem_ofList]
      exact hx₁
    intro hin
    exact (h x ⟨this, hin⟩)
  have filter_eq : List.filter (fun x => decide (x ∉ l₂)) l₁ = l₁ := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact disjoint x hx
  rw [filter_eq]

def inter [DecidableEq α] (s t : Finset α) : Finset α :=
  ⟨Multiset.lift₂ (fun l₁ l₂ => (l₁.filter (· ∈ l₂) : Multiset α))
    (fun l₁ l₂ l₃ l₄ p₁ p₂ => by
      apply Quot.sound
      have step1 : (l₁.filter (fun x => decide (x ∈ l₂))).Perm (l₃.filter (fun x => decide (x ∈ l₂))) :=
        List.Perm.filter (fun x => decide (x ∈ l₂)) p₁
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

local instance inst_inter [DecidableEq α] : Inter (Finset α) where
  inter := inter

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
      have step1 : (l₁.filter (fun x => decide (x ∉ l₂))).Perm (l₃.filter (fun x => decide (x ∉ l₂))) :=
        List.Perm.filter (fun x => decide (x ∉ l₂)) p₁
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

local instance inst_sdiff [DecidableEq α] : SDiff (Finset α) where
  sdiff := sdiff

theorem mem_sdiff [DecidableEq α] {a : α} {s t : Finset α} :
    a ∈ s \ t ↔ a ∈ s ∧ a ∉ t := by
  induction s using Finset.ind with | h l₁ nd₁ =>
  induction t using Finset.ind with | h l₂ nd₂ =>
  show a ∈ (l₁.filter (· ∉ l₂) : Multiset α) ↔ a ∈ (l₁ : Multiset α) ∧ a ∉ (l₂ : Multiset α)
  simp only [Multiset.mem_coe, List.mem_filter, decide_eq_true_eq]

theorem ofList_nil : ofList [] List.nodup_nil = (∅ : Finset A) := by
  rfl

theorem ofList_cons [DecidableEq A] {hd : A} {nd : List.Nodup (hd :: tl)} :
  ofList (hd :: tl) nd = {hd} ∪ ofList tl (List.nodup_cons.mp nd).right := by
  ext a
  simp only [mem_union, mem_singleton, mem_ofList, List.mem_cons]

/-- Case analysis on a finset: either it's empty or it has at least one element. -/
@[elab_as_elim]
protected theorem cases_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α)
    (h_empty : p ∅)
    (h_add : ∀ x X, x ∉ X → p X → p ({x} ∪ X)) :
    p s := by
  induction s using Finset.ind with | h l nd =>
  induction l with
  | nil => exact h_empty
  | cons hd tl ih =>
    have hd_notin : hd ∉ tl := (List.nodup_cons.mp nd).left
    have hd_notin_finset : hd ∉ (ofList tl ((List.nodup_cons.mp nd).right)) := by
      simp; exact hd_notin
    rw [ofList_cons]
    exact h_add hd (ofList tl ((List.nodup_cons.mp nd).right)) hd_notin_finset (ih ((List.nodup_cons.mp nd).right))



/-- Fold over a finite set with a left-commutative operation.
    The operation must be left-commutative to ensure the result is independent
    of the order of elements.
-/
def fold {α β : Type _} (f : β → α → β) (hcomm : LeftCommutative f)
    (init : β) (s : Finset α) : β := s.val.fold f hcomm init

@[simp]
theorem fold_empty {f : β → α → β} {hcomm : LeftCommutative f} {init : β} :
    fold f hcomm init ∅ = init := by
  rfl

@[simp]
theorem fold_singleton {f : β → α → β} {hcomm : LeftCommutative f} {init : β} {a : α} :
    fold f hcomm init {a} = f init a := by
  rfl

@[simp]
theorem fold_insert [DecidableEq α] {f : β → α → β} {hcomm : LeftCommutative f} {init : β}
  {a : α} {s : Finset α} (h : a ∉ s) :
  fold f hcomm init ({a} ∪ s) = f (fold f hcomm init s) a := by
  induction s using Finset.ind with | h l nd =>
  simp only [fold, union, inst_union]
  simp only [Multiset.lift₂, Quotient.lift₂, ofList, Multiset.ofList]
  show Multiset.fold f hcomm init (Quot.mk _ (List.filter (fun x => decide (x ∉ l)) [a] ++ l)) =
       f (Multiset.fold f hcomm init (Quot.mk _ l)) a
  simp only [mem_ofList] at h
  have filter_eq : List.filter (fun x => decide (x ∉ l)) [a] = [a] := by
    simp only [List.filter]
    simp [h]
  rw [filter_eq]
  show Multiset.fold f hcomm init (Multiset.ofList ([a] ++ l)) =
       f (Multiset.fold f hcomm init (Multiset.ofList l)) a
  simp only [Multiset.fold_ofList, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact List.foldl_comm_left hcomm init a l

@[simp]
theorem fold_insert_idemp [DecidableEq α] {f : β → α → β} {hcomm : LeftCommutative f} {init : β}
  {a : α} {s : Finset α} (h : a ∈ s) :
  fold f hcomm init ({a} ∪ s) = fold f hcomm init s := by
  induction s using Finset.ind with | h l nd =>
  simp only [fold, union, inst_union, singleton, inst_singleton]
  simp only [Multiset.lift₂, Quotient.lift₂, ofList, Multiset.ofList]
  simp only [mem_ofList] at h
  show Multiset.fold f hcomm init (Quot.mk _ (List.filter (fun x => decide (x ∉ l)) [a] ++ l)) =
       Multiset.fold f hcomm init (Quot.mk _ l)
  have filter_eq : List.filter (fun x => decide (x ∉ l)) [a] = [] := by
    simp only [List.filter]
    simp [h]
  rw [filter_eq]
  simp only [List.nil_append]

/-- Basic computation lemma: fold on ofList reduces to list foldl -/
theorem fold_ofList (f : β → α → β) (hcomm : LeftCommutative f)
    (init : β) (l : List α) (nd : l.Nodup) :
    fold f hcomm init (ofList l nd) = l.foldl f init := by
  rfl

def map {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) : Finset β :=
  s.fold (fun x y => {f y} ∪ x)
  (by
    intro acc x y; simp only
    ext el; simp only [mem_union, mem_singleton]
    apply Iff.intro
    · rintro (heq | heq | hin)
      · subst heq; right; left; rfl
      · subst heq; left; rfl
      · right; right; exact hin
    · rintro (heq | heq | hin)
      · subst heq; right; left; rfl
      · subst heq; left; rfl
      · right; right; exact hin)
  ∅

theorem map_nil {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → β) :
  map f (ofList [] List.nodup_nil) = (ofList [] List.nodup_nil) := by rfl

private theorem foldl_union_distrib {β : Type _} [DecidableEq β]
    (f : α → β) (s t : Finset β) (xs : List α) :
    List.foldl (fun acc y => {f y} ∪ acc) (s ∪ t) xs =
    s ∪ List.foldl (fun acc y => {f y} ∪ acc) t xs := by
  induction xs generalizing s t with
  | nil => rfl
  | cons x xs IH =>
    simp only [List.foldl_cons]
    rw [IH]
    ext el
    simp only [mem_union, mem_singleton]
    grind only [= mem_union, = mem_singleton]

theorem map_cons {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → β)  (hnd : (x :: xs).Nodup) :
  map f (ofList (x :: xs) hnd) = {f x} ∪ map f (ofList xs (List.nodup_cons.mp hnd).right) := by
    simp [map, fold, Multiset.fold, ofList, Multiset.ofList]
    simp [Quotient.liftOn, Quot.liftOn]
    clear hnd

    induction xs with
    | nil => rfl
    | cons y xs IH =>
      simp only [List.foldl_cons]
      have h := foldl_union_distrib f {f x} {f y} xs
      calc List.foldl (fun acc y => {f y} ∪ acc) ({f y} ∪ ({f x} ∪ ∅)) xs
          = List.foldl (fun acc y => {f y} ∪ acc) ({f x} ∪ {f y}) xs := by
            congr 1
            ext el
            simp only [mem_union, mem_singleton, mem_empty, or_false]
            grind only [= mem_union, = mem_singleton]
        _ = {f x} ∪ List.foldl (fun acc y => {f y} ∪ acc) {f y} xs := h
        _ = {f x} ∪ List.foldl (fun acc y => {f y} ∪ acc) ({f y} ∪ ∅) xs := by congr 2
        _ = {f x} ∪ List.foldl (fun x y => {f y} ∪ x) ({f y} ∪ ∅) xs := rfl

theorem mem_map {β : Type _} [DecidableEq α] [DecidableEq β]
    {f : α → β} {s : Finset α} {b : β} :
    b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b := by
  induction s using Finset.ind with | h l hnd =>
  induction l with
  | nil =>
    rw [map_nil]
    simp only [mem_def, ofList, Multiset.mem_coe, List.not_mem_nil, false_and, exists_false]
  | cons x xs IH =>
    rw [map_cons, mem_union, IH, mem_singleton]
    simp only [ofList, mem_def, Multiset.mem_coe, List.mem_cons, exists_eq_or_imp]
    apply Iff.intro
    · rintro (heq | ⟨a, h1, h2⟩)
      · subst heq; left; rfl
      · subst h2; right; exists a
    · rintro (heq | ⟨a, h1, h2⟩)
      · subst heq; left; rfl
      · subst h2; right; exists a

/-- FlatMap (bind) operation for finsets. Maps each element to a finset and unions all results. -/
def flatMap {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → Finset β) (s : Finset α) : Finset β :=
  s.fold (fun acc x => f x ∪ acc)
  (by
    intro acc x y; simp only
    ext el; simp only [mem_union]
    apply Iff.intro
    · rintro (hfx | hacc | hfy)
      · right; left; exact hfx
      · left; exact hacc
      · right; right; exact hfy
    · rintro (hacc | hfx | hfy)
      · right; left; exact hacc
      · left; exact hfx
      · right; right; exact hfy)
  ∅

theorem flatMap_nil {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → Finset β) :
  flatMap f (ofList [] List.nodup_nil) = (ofList [] List.nodup_nil) := by rfl

private theorem foldl_union_distrib_finset {β : Type _} [DecidableEq β]
    (f : α → Finset β) (s t : Finset β) (xs : List α) :
    List.foldl (fun acc y => f y ∪ acc) (s ∪ t) xs =
    s ∪ List.foldl (fun acc y => f y ∪ acc) t xs := by
  induction xs generalizing s t with
  | nil => rfl
  | cons x xs IH =>
    simp only [List.foldl_cons]
    rw [IH]
    ext el
    simp only [mem_union]
    grind only [= mem_union]

theorem flatMap_cons {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → Finset β) (hnd : (x :: xs).Nodup) :
  flatMap f (ofList (x :: xs) hnd) = f x ∪ flatMap f (ofList xs (List.nodup_cons.mp hnd).right) := by
    simp [flatMap, fold, Multiset.fold, ofList, Multiset.ofList]
    simp [Quotient.liftOn, Quot.liftOn]
    clear hnd
    induction xs with
    | nil => rfl
    | cons y xs IH =>
      simp only [List.foldl_cons]
      have h := foldl_union_distrib_finset f (f x) (f y) xs
      calc List.foldl (fun acc y => f y ∪ acc) (f y ∪ (f x ∪ ∅)) xs
          = List.foldl (fun acc y => f y ∪ acc) (f x ∪ f y) xs := by
            congr 1
            ext el
            simp only [mem_union, mem_empty, or_false]
            grind only [= mem_union]
        _ = f x ∪ List.foldl (fun acc y => f y ∪ acc) (f y) xs := h
        _ = f x ∪ List.foldl (fun acc y => f y ∪ acc) (f y ∪ ∅) xs := by
            congr 2
            ext el
            simp only [mem_union, mem_empty, or_false]
        _ = f x ∪ List.foldl (fun x y => f y ∪ x) (f y ∪ ∅) xs := rfl

theorem mem_flatMap {β : Type _} [DecidableEq α] [DecidableEq β]
    {f : α → Finset β} {s : Finset α} {b : β} :
    b ∈ flatMap f s ↔ ∃ a, a ∈ s ∧ b ∈ f a := by
  induction s using Finset.ind with | h l hnd =>
  induction l with
  | nil =>
    rw [flatMap_nil]
    simp only [mem_def, ofList, Multiset.mem_coe, List.not_mem_nil, false_and, exists_false]
  | cons x xs IH =>
    rw [flatMap_cons, mem_union, IH]
    simp only [ofList, mem_def, Multiset.mem_coe, List.mem_cons, exists_eq_or_imp]

@[simp]
theorem flatMap_empty {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → Finset β) :
  flatMap f ∅ = ∅ := by
  rfl

theorem flatMap_singleton {β : Type _} [DecidableEq α] [DecidableEq β] (f : α → Finset β) (a : α) :
  flatMap f {a} = f a := by
  ext x
  rw [mem_flatMap]
  simp only [mem_singleton]
  constructor
  · intro ⟨y, hy, hx⟩
    subst hy
    exact hx
  · intro hx
    exact ⟨a, rfl, hx⟩

theorem flatMap_union {β : Type _} [DecidableEq α] [DecidableEq β]
    (f : α → Finset β) (s t : Finset α) :
  flatMap f (s ∪ t) = flatMap f s ∪ flatMap f t := by
  ext b
  rw [mem_flatMap, mem_union, mem_flatMap, mem_flatMap]
  constructor
  · intro ⟨a, ha, hb⟩
    rw [mem_union] at ha
    cases ha with
    | inl ha => left; exact ⟨a, ha, hb⟩
    | inr ha => right; exact ⟨a, ha, hb⟩
  · intro h
    cases h with
    | inl h => obtain ⟨a, ha, hb⟩ := h; exact ⟨a, mem_union.mpr (Or.inl ha), hb⟩
    | inr h => obtain ⟨a, ha, hb⟩ := h; exact ⟨a, mem_union.mpr (Or.inr ha), hb⟩

private def mem_dec [DecidableEq A] (x : A) (s : Finset A) : Bool
  := fold (fun acc y => decide (x = y) ∨ acc) (by intro P a b; simp only; grind only) false s

private theorem mem_dec_mem [DecidableEq A] {x : A} {X : Finset A}
  : mem_dec x X = (x ∈ X) := by
  induction X using Finset.cases_on with
  | h_empty => simp [mem_dec]
  | h_add y X hnin IH =>
    simp [mem_dec]
    rw [mem_singleton, fold_insert hnin]
    simp [mem_dec] at IH
    simp [IH]

instance [DecidableEq A] {x : A} {s : Finset A} : Decidable (x ∈ s) := by
  rw [<-mem_dec_mem]
  infer_instance

instance [DecidableEq A] : DecidableEq (Finset A) := by
  intro X Y
  cases X with | mk val _ =>
  cases Y with | mk val' _ =>
  simp
  unfold Multiset at *
  have : (a b : List A) → Decidable (a ≈ b) := by
    intro a b; simp only [HasEquiv.Equiv, List.isSetoid]
    infer_instance
  apply Quotient.decidableEq (s := List.isSetoid A) val val'

end Finset

end FromMathlib
