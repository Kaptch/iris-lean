/-
Copyright (c) 2025 Leo Stefanesco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Stefanesco, Puming Liu, Sergei Stepanenko
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

/-!
# The agreement camera

The agreement construction is built in two layers. The raw representation `Agree.Raw α` is a
nonempty list of elements of `α`, together with the step-indexed relation `Agree.Raw.dist` that
identifies two such lists when they have the same elements up to `≡{n}≡` (essentially, the old definition).

The interface type `Agree α` is the quotient of `Agree.Raw α` by the relation
`fun x y => ∀ n, Agree.Raw.dist n x y` (which is exactly the OFE equivalence). Quotienting by the
OFE equivalence makes `=` coincide with `=`, so `Agree α` is `OFE.Leibniz` by construction.
-/

/-! ## The raw representation -/

section raw

variable {α : Type u} {β : Type v}

structure Agree.Raw (α : Type u) where
  car : List α
  not_nil : car ≠ []
attribute [simp] Agree.Raw.not_nil

namespace Agree.Raw

@[ext] theorem ext {x y : Raw α} (h : x.car = y.car) : x = y := by
  cases x; cases y; cases h; rfl

def toAgree (a : α) : Raw α := ⟨[a], by simp⟩

@[rocq_alias elem_of_agree]
theorem mem (x : Raw α) : ∃ a, a ∈ x.car := by
  rcases x with ⟨as, h⟩
  rcases as
  · contradiction
  · simp_all

def map' (f : α → β) (a : Raw α) : Raw β := ⟨a.car.map f, by simp⟩

@[simp] theorem map'_car {f : α → β} {x : Raw α} : (map' f x).car = x.car.map f := rfl

def op (x y : Raw α) : Raw α :=
  ⟨x.car ++ y.car, by apply List.append_ne_nil_of_left_ne_nil; exact x.not_nil⟩

theorem map'_op {f : α → β} {x y : Raw α} : map' f (op x y) = op (map' f x) (map' f y) := by
  apply ext; simp [op, map']

variable [OFE α]

@[rocq_alias agree_dist]
def dist (n : Nat) (x y : Raw α) : Prop :=
  (∀ a ∈ x.car, ∃ b ∈ y.car, a ≡{n}≡ b) ∧
  (∀ b ∈ y.car, ∃ a ∈ x.car, a ≡{n}≡ b)

theorem dist_equiv : Equivalence (dist (α := α) n) where
  refl := fun ⟨x, h⟩ => by
    constructor
    · intro a ha; exists a
    · intro b hb; exists b
  symm := fun ⟨h₁, h₂⟩ => by
    constructor
    · intro a ha
      obtain ⟨b, hb, hd⟩ := h₂ a ha
      exact ⟨b, hb, hd.symm⟩
    · intro b hb
      obtain ⟨a, ha, hd⟩ := h₁ b hb
      exact ⟨a, ha, hd.symm⟩
  trans := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => by
    constructor
    · intro a ha
      obtain ⟨b, hb, hd₁⟩ := h₁ a ha
      obtain ⟨c, hc, hd₂⟩ := h₂ b hb
      exact ⟨c, hc, hd₁.trans hd₂⟩
    · intro c hc
      obtain ⟨b, hb, hd₁⟩ := h₂' c hc
      obtain ⟨a, ha, hd₂⟩ := h₁' b hb
      exact ⟨a, ha, hd₂.trans hd₁⟩

theorem dist_lt {x y : Raw α} (h : dist n x y) (hlt : m < n) : dist m x y := by
  constructor
  · intro a ha; obtain ⟨b, hb, hd⟩ := h.1 a ha; exact ⟨b, hb, OFE.Dist.lt hd hlt⟩
  · intro b hb; obtain ⟨a, ha, hd⟩ := h.2 b hb; exact ⟨a, ha, OFE.Dist.lt hd hlt⟩

def validN (n : Nat) (x : Raw α) : Prop :=
  match x.car with
  | [_] => True
  | _ => ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b

@[rocq_alias agree_validN_def]
theorem validN_iff {x : Raw α} :
    x.validN n ↔ ∀ a ∈ x.car, ∀ b ∈ x.car, a ≡{n}≡ b := by
  rcases x with ⟨⟨⟩ | ⟨a, ⟨⟩| _⟩, _⟩ <;> simp_all [validN, OFE.Dist.rfl]

def valid (x : Raw α) : Prop := ∀ n, x.validN n

theorem op_comm {x y : Raw α} (n) : dist n (op x y) (op y x) := by
  simp only [dist, op, List.mem_append]
  constructor <;> exact fun _ ha => ⟨_, ha.symm, .rfl⟩

theorem op_commN {x y : Raw α} : dist n (op x y) (op y x) := op_comm n

theorem op_assoc {x y z : Raw α} (n) : dist n (op x (op y z)) (op (op x y) z) := by
  simp only [dist, op, List.mem_append, List.append_assoc]
  constructor <;> (intro a ha; exists a)

theorem idemp {x : Raw α} (n) : dist n (op x x) x := by
  constructor <;> (intro a ha; exists a; simp_all [op])

theorem validN_ne {x y : Raw α} : dist n x y → x.validN n → y.validN n := by
  simp only [dist, validN_iff, and_imp]
  intro h₁ h₂ hn a ha b hb
  have ⟨a', ha', ha'a⟩ := h₂ _ ha
  have ⟨b', hb', hb'b⟩ := h₂ _ hb
  have ha'b' := hn _ ha' _ hb'
  exact ha'a.symm.trans (ha'b'.trans hb'b)

theorem validN_succ {x : Raw α} : x.validN (n + 1) → x.validN n := by
  simp only [validN_iff]; intro hsuc a ha b hb
  exact OFE.Dist.lt (hsuc a ha b hb) (by omega)

theorem validN_op_left {x y : Raw α} : (op x y).validN n → x.validN n := by
  simp only [op, validN_iff, List.mem_append]
  exact fun h a ha b hb => h _ (.inl ha) _ (.inl hb)

theorem op_ne_dist {x : Raw α} {y₁ y₂ : Raw α} (h : dist n y₁ y₂) :
    dist n (op x y₁) (op x y₂) := by
  simp only [dist, op, List.mem_append]
  constructor
  · rintro a (hx | hy)
    · exact ⟨a, .inl hx, .rfl⟩
    · obtain ⟨b, hb, heq⟩ := h.1 _ hy; exact ⟨b, .inr hb, heq⟩
  · rintro a (hx | hy)
    · exact ⟨a, .inl hx, .rfl⟩
    · obtain ⟨b, hb, heq⟩ := h.2 _ hy; exact ⟨b, .inr hb, heq⟩

theorem op_ne₂_dist {x₁ x₂ y₁ y₂ : Raw α} (hx : dist n x₁ x₂) (hy : dist n y₁ y₂) :
    dist n (op x₁ y₁) (op x₂ y₂) :=
  dist_equiv.trans (dist_equiv.trans (op_ne_dist hy) (op_comm n))
    (dist_equiv.trans (op_ne_dist hx) (op_comm n))

theorem op_invN {x y : Raw α} : (op x y).validN n → dist n x y := by
  simp only [op, validN_iff, List.mem_append, dist]
  intro h; constructor
  · intro a ha; obtain ⟨b, hb⟩ := mem y; exact ⟨b, hb, by simp_all⟩
  · intro a ha; obtain ⟨b, hb⟩ := mem x; exact ⟨b, hb, by simp_all⟩

theorem op_inv {x y : Raw α} : (op x y).valid → ∀ n, dist n x y :=
  fun h n => op_invN (h n)

@[simp] theorem toAgree_validN {a : α} : (toAgree a).validN n := by
  simp [validN, toAgree]

theorem toAgree_injN {a b : α} : dist n (toAgree a) (toAgree b) → a ≡{n}≡ b := by
  intro ⟨h₁, h₂⟩; simp_all [toAgree]

theorem toAgree_uninjN {x : Raw α} : x.validN n → ∃ a, dist n (toAgree a) x := by
  rw [validN_iff]
  obtain ⟨a, ha⟩ := mem x
  intro h; exists a
  constructor <;> intros
  · exists a; simp_all [toAgree]
  · simp_all [toAgree]

theorem toAgree_uninj {x : Raw α} : x.valid → ∃ a, ∀ n, dist n (toAgree a) x := by
  simp only [valid, validN_iff]
  obtain ⟨a, ha⟩ := mem x
  intro h; exists a; intro n
  constructor <;> intros
  · exists a; simp_all [toAgree]
  · simp_all [toAgree]

variable [OFE β] {f : α → β}

theorem map'_ne [OFE.NonExpansive f] {n} {x₁ x₂ : Raw α} (h : dist n x₁ x₂) :
    dist n (map' f x₁) (map' f x₂) := by
  simp only [dist, map'_car, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h ⊢
  constructor
  · intro a ha; obtain ⟨b, hb, heq⟩ := h.1 a ha
    exact ⟨f b, ⟨b, hb, rfl⟩, OFE.NonExpansive.ne heq⟩
  · intro a ha; obtain ⟨b, hb, heq⟩ := h.2 a ha
    exact ⟨f b, ⟨b, hb, rfl⟩, OFE.NonExpansive.ne heq⟩


theorem map'_validN [OFE.NonExpansive f] {x : Raw α} (h : x.validN n) : (map' f x).validN n := by
  rw [validN_iff] at h ⊢
  simp only [map'_car, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun a ha b hb => OFE.NonExpansive.ne (h a ha b hb)

theorem discrete_0 [OFE.Discrete α] {x y : Raw α} (h : dist 0 x y) (n) : dist n x y := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb, heq⟩ := h.1 a ha; exact ⟨b, hb, OFE.discrete_n heq⟩
  · obtain ⟨a, ha, heq⟩ := h.2 b hb; exact ⟨a, ha, OFE.discrete_n heq⟩

theorem discrete_valid [OFE.Discrete α] {x : Raw α} (h : x.validN 0) : x.valid := by
  rw [validN_iff] at h
  intro n; rw [validN_iff]
  exact fun a ha b hb => OFE.discrete_n (h a ha b hb)

theorem toAgree_discrete {a : α} [Ha : OFE.DiscreteE a] {y : Raw α}
    (h : dist 0 (toAgree a) y) (n) : dist n (toAgree a) y := by
  refine ⟨fun x hx => ?_, fun c hc => ?_⟩
  · rw [show x = a from by simpa [toAgree] using hx]
    obtain ⟨b, hb, hd⟩ := h.1 a (by simp [toAgree])
    exact ⟨b, hb, (Ha.discrete hd).dist⟩
  · obtain ⟨x, hx, hd⟩ := h.2 c hc
    rw [show x = a from by simpa [toAgree] using hx] at hd
    exact ⟨a, by simp [toAgree], (Ha.discrete hd).dist⟩

end Agree.Raw

end raw

/-! ## The quotient -/

section quotient

variable {α : Type u} {β : Type v} [OFE α] [OFE β]

open Agree (Raw)

instance Agree.Raw.instSetoid : Setoid (Raw α) :=
  OFE.distSetoid Raw.dist fun _ => Raw.dist_equiv

@[rocq_alias agree]
def Agree (α : Type u) [OFE α] : Type u := Quotient (Agree.Raw.instSetoid (α := α))

namespace Agree

def mk (x : Raw α) : Agree α := Quotient.mk _ x

@[elab_as_elim, induction_eliminator]
theorem ind {motive : Agree α → Prop} (mk : ∀ x : Raw α, motive (Agree.mk x)) (x : Agree α) :
    motive x := Quotient.ind mk x

theorem sound {x y : Raw α} (h : ∀ n, Raw.dist n x y) : mk x = mk y := Quotient.sound h

theorem validN_resp {n} {x y : Raw α} (h : x ≈ y) : Raw.validN n x = Raw.validN n y :=
  propext ⟨Raw.validN_ne (h n), Raw.validN_ne (Raw.dist_equiv.symm (h n))⟩

theorem valid_resp {x y : Raw α} (h : x ≈ y) : Raw.valid x = Raw.valid y := by
  simp only [Raw.valid, validN_resp h]

@[rocq_alias agree_ofe_mixin]
instance instOFE : OFE (Agree α) :=
  OFE.mkLeibniz Raw.dist (fun _ => Raw.dist_equiv) (fun h hlt => Raw.dist_lt h hlt)

#rocq_ignore agreeO "Use Agree with a typeclass instance instead."
#rocq_ignore agree_equiv "Defined in Agree OFE instance."


def validN (n : Nat) : Agree α → Prop := Quotient.lift (Raw.validN n) (fun _ _ h => validN_resp h)

def valid : Agree α → Prop := Quotient.lift Raw.valid (fun _ _ h => valid_resp h)

def op : Agree α → Agree α → Agree α :=
  Quotient.lift₂ (fun x y => mk (Raw.op x y))
    (fun _ _ _ _ hx hy => sound fun n => Raw.op_ne₂_dist (hx n) (hy n))

@[simp] theorem dist_mk {n} {x y : Raw α} : mk x ≡{n}≡ mk y ↔ Raw.dist n x y := .rfl
@[simp] theorem validN_mk {n} {x : Raw α} : validN n (mk x) ↔ x.validN n := .rfl
@[simp] theorem valid_mk {x : Raw α} : valid (mk x) ↔ x.valid := .rfl
@[simp] theorem op_mk {x y : Raw α} : op (mk x) (mk y) = mk (Raw.op x y) := rfl

@[rocq_alias agree_comm]
theorem op_comm {x y : Agree α} : op x y = op y x := by
  induction x with | _ x => induction y with | _ y =>
  exact OFE.eq_iff_forall_dist.mpr fun n => Raw.op_comm n

theorem op_commN {x y : Agree α} : op x y ≡{n}≡ op y x := OFE.Dist.of_eq op_comm

@[rocq_alias agree_assoc]
theorem op_assoc {x y z : Agree α} : op x (op y z) = op (op x y) z := by
  induction x with | _ x => induction y with | _ y => induction z with | _ z =>
  exact OFE.eq_iff_forall_dist.mpr fun n => Raw.op_assoc n

theorem op_idemp {x : Agree α} : op x x = x := by
  induction x with | _ x => exact OFE.eq_iff_forall_dist.mpr fun n => Raw.idemp n

@[rocq_alias agree_validN_ne]
theorem validN_ne {x y : Agree α} : x ≡{n}≡ y → validN n x → validN n y := by
  induction x with | _ x => induction y with | _ y => exact Raw.validN_ne

theorem validN_succ {x : Agree α} : validN (n + 1) x → validN n x := by
  induction x with | _ x => exact Raw.validN_succ

theorem validN_op_left {x y : Agree α} : validN n (op x y) → validN n x := by
  induction x with | _ x => induction y with | _ y => exact Raw.validN_op_left

@[rocq_alias agree_op_ne']
theorem op_ne {x : Agree α} : OFE.NonExpansive (op x) := by
  refine ⟨fun {n} y₁ y₂ h => ?_⟩
  induction x with | _ x =>
  induction y₁ with | _ y₁ => induction y₂ with | _ y₂ =>
  exact dist_mk.mpr (Raw.op_ne_dist (dist_mk.mp h))

@[rocq_alias agree_op_ne]
theorem op_ne₂ : OFE.NonExpansive₂ (op (α := α)) := by
  refine ⟨fun {n} x₁ x₂ hx y₁ y₂ hy => ?_⟩
  induction x₁ with | _ x₁ => induction x₂ with | _ x₂ =>
  induction y₁ with | _ y₁ => induction y₂ with | _ y₂ =>
  exact dist_mk.mpr (Raw.op_ne₂_dist (dist_mk.mp hx) (dist_mk.mp hy))

@[rocq_alias agree_op_invN]
theorem op_invN {x y : Agree α} : validN n (op x y) → x ≡{n}≡ y := by
  induction x with | _ x => induction y with | _ y => exact Raw.op_invN

@[rocq_alias agree_op_inv]
theorem op_inv {x y : Agree α} : valid (op x y) → x = y := by
  induction x with | _ x => induction y with | _ y =>
  exact fun h => OFE.eq_iff_forall_dist.mpr (Raw.op_inv h)

@[rocq_alias agree_cmra_mixin]
instance instCMRA : CMRA (Agree α) where
  pcore := some
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne := by simp
  validN_ne := validN_ne
  valid_iff_validN := fun {x} => by induction x with | _ x => exact .rfl
  validN_succ := validN_succ
  assoc := op_assoc
  comm := op_comm
  pcore_op_left := fun {x cx} h => by obtain rfl := Option.some.inj h; exact op_idemp
  pcore_idem := fun {x cx} h => by obtain rfl := Option.some.inj h; rfl
  pcore_op_mono := fun {x cx} h y => by obtain rfl := Option.some.inj h; exact ⟨y, rfl⟩
  validN_op_left := validN_op_left
  extend := by
    intro n x y₁ y₂ hval heq₁
    have heq₂ := op_invN (validN_ne heq₁ hval)
    have heq₃ : op y₁ y₂ ≡{n}≡ y₁ := op_ne.ne heq₂.symm |>.trans (OFE.Dist.of_eq op_idemp)
    exact ⟨x, x, op_idemp.symm, heq₁.trans heq₃, heq₁.trans heq₃ |>.trans heq₂⟩

#rocq_ignore agreeR "Use the plain Agree type with a typeclass instance instead."
#rocq_ignore agree_op_instance "Use the CMRA instance instead."
#rocq_ignore agree_pcore_instance "Use the CMRA instance instead."
#rocq_ignore agree_validN_instance "Use the CMRA instance instead."
#rocq_ignore agree_valid_instance "Use the CMRA instance instead."

theorem op_def {x y : Agree α} : x • y = op x y := rfl
theorem validN_def {x : Agree α} : ✓{n} x ↔ validN n x := .rfl
theorem valid_def {x : Agree α} : ✓ x ↔ valid x := .rfl

@[rocq_alias agree_pcore]
theorem pcore_some {x : Agree α} : CMRA.pcore x = some x := rfl

@[rocq_alias agree_cmra_total]
instance : CMRA.IsTotal (Agree α) where
  total x := ⟨x, rfl⟩

@[rocq_alias agree_idemp]
theorem idemp {x : Agree α} : x • x = x := op_idemp

#rocq_ignore agree_validN_proper "Derivable from Agree.validN_ne using NonExpansive.congr"
#rocq_ignore agree_op_proper "Derivable from Agree.op_ne₂ using NonExpansive₂.congr"
#rocq_ignore to_agree_op_inv "Use the general op_invN theorem."
#rocq_ignore to_agree_op_invN "Use the general op_inv theorem."

@[rocq_alias agree_cmra_discrete]
instance instCMRADiscrete [OFE.Discrete α] : CMRA.Discrete (Agree α) where
  discrete_0 {x y} h := by
    induction x with | _ x => induction y with | _ y =>
    exact OFE.eq_iff_forall_dist.mpr (Raw.discrete_0 h)
  discrete_valid {x} h := by induction x with | _ x => exact Raw.discrete_valid h

instance instDiscrete [OFE.Discrete α] : OFE.Discrete (Agree α) where
  discrete_0 {x y} h := by
    induction x with | _ x => induction y with | _ y =>
    exact OFE.eq_iff_forall_dist.mpr (Raw.discrete_0 h)

@[rocq_alias agree_includedN]
theorem includedN {x y : Agree α} : x ≼{n} y ↔ y ≡{n}≡ y • x := by
  refine ⟨fun ⟨z, h⟩ => ?_, fun h => ⟨y, h.trans op_commN⟩⟩
  have hid : x ≡{n}≡ x • x := OFE.Dist.of_eq idemp.symm
  calc
    y ≡{n}≡ x • z := h
    _ ≡{n}≡ (x • x) • z := .op_l hid
    _ ≡{n}≡ x • (x • z) := CMRA.op_assocN.symm
    _ ≡{n}≡ x • y := h.symm.op_r
    _ ≡{n}≡ y • x := op_commN

@[rocq_alias agree_included]
theorem included {x y : Agree α} : x ≼ y ↔ y = y • x :=
  ⟨fun ⟨z, h⟩ => OFE.eq_iff_forall_dist.mpr fun _ => includedN.mp ⟨z, OFE.Dist.of_eq h⟩,
   fun h => ⟨y, h.trans op_comm⟩⟩

@[rocq_alias agree_valid_includedN]
theorem valid_includedN {x y : Agree α} : ✓{n} y → x ≼{n} y → x ≡{n}≡ y := by
  intro hval ⟨z, heq⟩
  have : ✓{n} (x • z) := heq.validN.mp hval
  calc
    x ≡{n}≡ x • x := OFE.Dist.of_eq idemp.symm
    _ ≡{n}≡ x • z := (op_invN this).op_r
    _ ≡{n}≡ y := heq.symm

@[rocq_alias agree_valid_included]
theorem valid_included {x y : Agree α} : ✓ y → x ≼ y → x = y := by
  intro hval ⟨z, heq⟩
  have heq' : x = z := op_inv <| (CMRA.valid_iff heq).mp hval
  calc
    x = x • x := idemp.symm
    _ = x • z := CMRA.op_right_congr x heq'
    _ = y := heq.symm

set_option synthInstance.checkSynthOrder false in
instance {x : Agree α} : IsOp io1 x io2 x io3 x where
  is_op := idemp.symm

end Agree

/-! ## `toAgree` -/

@[rocq_alias to_agree]
def toAgree (a : α) : Agree α := Agree.mk (Agree.Raw.toAgree a)

theorem toAgree_def {a : α} : toAgree a = Agree.mk (Agree.Raw.toAgree a) := rfl

@[rocq_alias to_agree_ne]
instance instNonExpansive_toAgree : OFE.NonExpansive (@toAgree α _) where
  ne n x₁ x₂ heq := by constructor <;> simp_all [Agree.Raw.toAgree]

#rocq_ignore to_agree_proper "Derivable from instNonExpansive_toAgree with NonExpansive.congr"

@[rocq_alias to_agree_injN]
theorem Agree.toAgree_injN {a b : α} : toAgree a ≡{n}≡ toAgree b → a ≡{n}≡ b :=
  Raw.toAgree_injN

@[rocq_alias to_agree_inj]
theorem Agree.toAgree_inj {a b : α} : toAgree a = toAgree b → a = b := by
  simp only [OFE.eq_iff_forall_dist]
  exact fun heq n => toAgree_injN (heq n)

@[simp] theorem Agree.toAgree_validN {a : α} : ✓{n} toAgree a := Raw.toAgree_validN (a := a) (n := n)

@[simp] theorem Agree.toAgree_valid {a : α} : ✓ toAgree a :=
  fun m => Agree.toAgree_validN (a := a) (n := m)

@[rocq_alias to_agree_uninjN]
theorem Agree.toAgree_uninjN {x : Agree α} : ✓{n} x → ∃ a, toAgree a ≡{n}≡ x := by
  induction x with | _ x => exact fun h => Raw.toAgree_uninjN h

@[rocq_alias to_agree_uninj]
theorem Agree.toAgree_uninj {x : Agree α} : ✓ x → ∃ a, toAgree a = x := by
  induction x with | _ x =>
  exact fun h => (Raw.toAgree_uninj h).imp fun a hd => OFE.eq_iff_forall_dist.mpr hd

instance toAgree.ne : OFE.NonExpansive (toAgree : α → Agree α) := instNonExpansive_toAgree

theorem toAgree.inj {a1 a2 : α} {n} (H : toAgree a1 ≡{n}≡ toAgree a2) : a1 ≡{n}≡ a2 :=
  Agree.toAgree_injN H

namespace Agree

@[rocq_alias agree_cancelable]
instance {x : Agree α} : CMRA.Cancelable x where
  cancelableN {n y z} hval heq := by
    obtain ⟨a, ha⟩ := Agree.toAgree_uninjN (CMRA.validN_op_left hval)
    obtain ⟨b, hb⟩ := Agree.toAgree_uninjN (CMRA.validN_op_right hval)
    have hval' : ✓{n} x • z := (OFE.Dist.validN heq).mp hval
    have : ✓{n} z := CMRA.validN_op_right hval'
    obtain ⟨c, hc⟩ := Agree.toAgree_uninjN this
    have heq₁ : a ≡{n}≡ b := Agree.toAgree_injN <| calc
      toAgree a ≡{n}≡ x         := ha
      _         ≡{n}≡ y         := Agree.op_invN hval
      _         ≡{n}≡ toAgree b := hb.symm
    have heq₂ : a ≡{n}≡ c := Agree.toAgree_injN <| calc
      toAgree a ≡{n}≡ x         := ha
      _         ≡{n}≡ z         := Agree.op_invN hval'
      _         ≡{n}≡ toAgree c := hc.symm
    have heq₃ : b ≡{n}≡ c := heq₁.symm.trans heq₂
    calc
      y ≡{n}≡ toAgree b := hb.symm
      _ ≡{n}≡ toAgree c := OFE.NonExpansive.ne heq₃
      _ ≡{n}≡ z := hc

@[rocq_alias agree_core_id]
instance (a : α) : CMRA.CoreId (toAgree a) where
  core_id := by simp [CMRA.pcore]

@[simp, rocq_alias to_agree_includedN]
theorem toAgree_includedN {a b : α} : toAgree a ≼{n} toAgree b ↔ a ≡{n}≡ b := by
  constructor <;> intro h
  · exact toAgree_injN (valid_includedN trivial h)
  · exists toAgree a
    calc
      toAgree b ≡{n}≡ toAgree a := OFE.NonExpansive.ne h.symm
      _         ≡{n}≡ toAgree a • toAgree a := OFE.Dist.of_eq idemp |>.symm

@[simp, rocq_alias to_agree_included]
theorem toAgree_included {a b : α} : toAgree a ≼ toAgree b ↔ a = b := by
  constructor <;> intro h
  · exact toAgree_inj (valid_included (fun _ => trivial) h)
  · exists toAgree a
    calc
      toAgree b = toAgree a := OFE.NonExpansive.congr h.symm
      _         = toAgree a • toAgree a := idemp.symm

@[simp, rocq_alias to_agree_included_L]
theorem toAgree_included_L {a b : α} :
    toAgree a ≼ toAgree b ↔ a = b := toAgree_included

@[rocq_alias to_agree_op_validN]
theorem toAgree_op_validN_iff_dist {a b : α} :
    ✓{n} (toAgree a • toAgree b) ↔ a ≡{n}≡ b := by
  constructor <;> intro h
  · exact toAgree_injN (op_invN h)
  · have : toAgree a ≡{n}≡ toAgree b := OFE.NonExpansive.ne h
    have : toAgree a • toAgree b ≡{n}≡ toAgree a := calc
      toAgree a • toAgree b ≡{n}≡ toAgree a • toAgree a := this.symm.op_r
      _ ≡{n}≡ toAgree a := OFE.Dist.of_eq idemp
    exact this.symm.validN.mp trivial

@[rocq_alias to_agree_op_valid]
theorem toAgree_op_valid_iff_eq {a : α} : ✓ (toAgree a • toAgree b) ↔ a = b := by
  simp [OFE.eq_iff_forall_dist, CMRA.valid_iff_validN, toAgree_op_validN_iff_dist]

@[rocq_alias to_agree_discrete]
instance toAgree.is_discrete {a : α} [OFE.DiscreteE a] : OFE.DiscreteE (toAgree a) where
  discrete {y} h := by
    induction y with | _ y => exact OFE.eq_iff_forall_dist.mpr (Raw.toAgree_discrete h)

end Agree

#rocq_ignore to_agree_op_valid_L "Now `=`; subsumed by `toAgree_op_valid_iff_eq`."

#rocq_ignore to_agree_op_inv_L "Use toAgree_op_valid_iff_eq"

end quotient

/-! ## Functoriality -/

section agree_map

variable {α β γ : Type _} [OFE α] [OFE β] [OFE γ] {f : α → β} [hne : OFE.NonExpansive f]

open Agree (Raw)

@[rocq_alias agree_map]
def Agree.map' (f : α → β) [OFE.NonExpansive f] : Agree α → Agree β :=
  Quotient.lift (fun a => Agree.mk (Raw.map' f a))
    (fun _ _ h => Agree.sound fun n => Raw.map'_ne (h n))

@[simp] theorem Agree.map'_mk (f : α → β) [OFE.NonExpansive f] {x : Raw α} :
    Agree.map' f (Agree.mk x) = Agree.mk (Raw.map' f x) := rfl

@[rocq_alias agree_map_ne]
instance instNonExpansive_AgreeMap' : OFE.NonExpansive (Agree.map' f) where
  ne n x y h := by
    induction x with | _ x => induction y with | _ y =>
    exact Raw.map'_ne (Agree.dist_mk.mp h)

#rocq_ignore agree_map_proper "Derivable from instNonExpansive_AgreeMap' with NonExpansive.congr"

variable (f) in
@[rocq_alias agree_map_morphism]
def Agree.map : (Agree α) -C> (Agree β) where
  f := map' f
  ne := instNonExpansive_AgreeMap'
  validN {n x} hval := by
    induction x with | _ x => exact Raw.map'_validN hval
  pcore x := rfl
  op x y := by
    induction x with | _ x => induction y with | _ y =>
    show mk (Raw.map' f (Raw.op x y)) = mk (Raw.op (Raw.map' f x) (Raw.map' f y))
    exact congrArg mk Raw.map'_op

@[simp] theorem Agree.map_mk (f : α → β) [OFE.NonExpansive f] (x : Raw α) :
    Agree.map f (mk x) = mk (Raw.map' f x) := rfl

@[simp] theorem Agree.map'_id (x : Agree α) : Agree.map' id x = x := by
  induction x with | _ x => rw [map'_mk]; exact congrArg mk (Raw.ext (by simp [Raw.map'_car]))

theorem Agree.map'_compose {f : α → β} {g : β → γ}
    [OFE.NonExpansive f] [OFE.NonExpansive g] [OFE.NonExpansive (g ∘ f)] (x : Agree α) :
    Agree.map' (g ∘ f) x = Agree.map' g (Agree.map' f x) := by
  induction x with | _ x =>
  rw [map'_mk, map'_mk, map'_mk]
  exact congrArg mk (Raw.ext (by simp [Raw.map'_car, List.map_map]))

@[rocq_alias agreeO_map]
abbrev Agree.map_hom : (Agree α) -n> (Agree β) := CMRA.Hom.toHom (Agree.map f)

@[rocq_alias agreeO_map_ne]
theorem Agree.map_ne {f g : α → β} [OFE.NonExpansive f] [OFE.NonExpansive g] {x : Agree α}
    (heq : ∀ a, f a ≡{n}≡ g a) : map f x ≡{n}≡ map g x := by
  induction x with | _ x =>
  rw [map_mk, map_mk]
  refine dist_mk.mpr ⟨?_, ?_⟩ <;> simp only [Raw.map'_car, List.mem_map] <;> rintro _ ⟨a, ha, rfl⟩
  · exact ⟨g a, ⟨a, ha, rfl⟩, heq a⟩
  · exact ⟨f a, ⟨a, ha, rfl⟩, heq a⟩

@[rocq_alias agree_map_ext]
theorem Agree.agree_map_ext {f g : α → β} [OFE.NonExpansive f] [OFE.NonExpansive g] {x : Agree α}
    (H : ∀ a, f a = g a) : map f x = map g x :=
  OFE.eq_iff_forall_dist.mpr fun _ => map_ne (H · |>.dist)

@[rocq_alias agree_map_id]
theorem Agree.map_id (x : Agree α) : Agree.map id x = x := by
  induction x with | _ x => rw [map_mk]; exact congrArg mk (Raw.ext (by simp [Raw.map'_car]))

@[rocq_alias agree_map_compose]
theorem Agree.map_compose (f : α -n> β) (g : β -n> γ) (x : Agree α) :
    Agree.map (g.comp f) x = Agree.map g (Agree.map f x) := by
  induction x with | _ x =>
  rw [map_mk, map_mk, map_mk]
  exact congrArg mk (Raw.ext (by simp [Raw.map'_car, OFE.Hom.comp, List.map_map]))

theorem toAgree.incN {a b : α} {n} : toAgree a ≼{n} toAgree b ↔ a ≡{n}≡ b :=
  Agree.toAgree_includedN

@[rocq_alias agree_map_to_agree]
theorem Agree.map_toAgree {x : α} : Agree.map f (toAgree x) = toAgree (f x) := by
  show Agree.map f (mk (Raw.toAgree x)) = mk (Raw.toAgree (f x))
  rw [map_mk]; exact congrArg mk (Raw.ext rfl)

end agree_map

section agree_rfunctor

@[rocq_alias agreeRF]
abbrev AgreeRF (F : COFE.OFunctorPre) [COFE.OFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => Agree (F A B)

instance {F} [COFE.OFunctor F] : RFunctor (AgreeRF F) where
  map f g := Agree.map (COFE.OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ := Agree.map_ne <| COFE.OFunctor.map_ne.ne Hx Hy
  map_id x := by
    conv => right; rw [← (Agree.map_id x)]
    exact (Agree.map_id x) ▸ Agree.agree_map_ext COFE.OFunctor.map_id
  map_comp f g f' g' x := by
    rw [← Agree.map_compose]
    apply Agree.agree_map_ext
    apply COFE.OFunctor.map_comp

@[rocq_alias agreeRF_contractive]
instance {F} [COFE.OFunctorContractive F] : RFunctorContractive (AgreeRF F) where
  map_contractive.1 H _ := Agree.map_ne (COFE.OFunctorContractive.map_contractive.1 H)

end agree_rfunctor
