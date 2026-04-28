/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.Agree
public import Iris.Algebra.CMRA

/-!
# Hyperspace Camera

In this file we construct a (hyper)space of compact subspaces of a given X : UMet, show that it is complete, and provide CMRA for it.
-/

@[expose] public section

-- TODO:
-- - Figure out and derive more algebraic properties of Powerset
-- - ?Leibniz? need to change Agree/provide an alternative for it
-- - See if it's enough to model nondeterminism
-- - Experiment with Vietoris spaces

namespace Iris

def Completion (α : Type u) [OFE α] := Chain α
instance {α : Type u} [OFE α] : OFE (Completion α) where
  Dist n x y := (x.chain n) ≡{n}≡ (y.chain n)
  Equiv x y := ∀ n : Nat, (x.chain n) ≡{n}≡ (y.chain n)
  dist_eqv {n} := by
    constructor
    · intro x; rfl
    · intro x y H; symm; apply H
    · intro x y z H1 H2; exact H1.trans H2
  equiv_dist := .rfl
  dist_lt {n x y m H Hlt} := by
    refine (x.cauchy (Nat.le_of_lt Hlt)).symm.trans ?_
    refine (H.lt Hlt).trans ?_
    exact y.cauchy (Nat.le_of_lt Hlt)
instance {α : Type u} [OFE α] : IsCOFE (Completion α) where
  compl c := {
    chain n := (c.chain n).chain n
    cauchy {n i} Hle := .trans (((c.chain i).cauchy Hle).trans .rfl) (c.cauchy Hle)
  }
  conv_compl {n c} := by simp only [OFE.Dist, OFE.Dist.rfl]

namespace Completion

-- completion monad
def unit {α : Type u} [OFE α] : α -n> Completion α := ⟨Chain.const, ⟨fun {_ _ _} H => H⟩⟩
def bind {α β : Type u} [OFE α] [OFE β] : (α -n> Completion β) -n> (Completion α -n> Completion β) :=
  ⟨fun f => ⟨fun x => IsCOFE.compl (x.map f)
    , ⟨fun _ _ _ H => by refine IsCOFE.conv_compl.trans (.trans ?_ IsCOFE.conv_compl.symm); exact (f.ne.ne H)⟩⟩
  , ⟨fun _ x y H => by
      intro a; simp [OFE.Dist]
      refine (IsCOFE.conv_compl (c := Chain.map x a)).trans ?_
      exact .trans (H _) (IsCOFE.conv_compl (c := Chain.map y a)).symm⟩⟩
theorem unit_left {α β : Type u} [OFE α] [OFE β] {f : α -n> Completion β}
  : (bind f).comp (unit (α := α)) ≡ f := by
  intro x; simp only [bind, unit, OFE.Hom.comp_apply]
  exact OFE.equiv_dist.mpr (fun n => IsCOFE.conv_compl)
theorem unit_right {α : Type u} [OFE α]
  : bind (α := α) (β := α) unit ≡ OFE.Hom.id := by
  intro x; simp only [bind, unit]
  refine OFE.equiv_dist.mpr (fun n => ?_)
  refine IsCOFE.conv_compl.trans ?_
  simp [Chain.const, OFE.Dist]
theorem bind_assoc {α β γ : Type u} [OFE α] [OFE β] [OFE γ]
  {f : α -n> Completion β} {g : β -n> Completion γ}
  : (bind g).comp (bind f) ≡ bind ((bind g).comp f) := by
  intro x; simp only [bind]
  refine OFE.equiv_dist.mpr (fun n => ?_)
  refine IsCOFE.conv_compl.trans ?_
  refine .trans ?_ IsCOFE.conv_compl.symm
  refine .trans ?_ IsCOFE.conv_compl.symm
  simp only [Chain.map_apply]
  refine OFE.NonExpansive.ne ?_
  exact (IsCOFE.conv_compl (c := Chain.map f x))

-- derived functor
abbrev map {α β : Type u} [OFE α] [OFE β] : (α -n> β) → (Completion α -n> Completion β) :=
  fun f => bind (unit.comp f)
theorem map_def {α β : Type u} [OFE α] [OFE β] {f : α -n> β} {x : Completion α} : ((map f) x) ≡{n}≡ (Chain.map f x) := .rfl
instance {α β : Type u} [OFE α] [OFE β] : OFE.NonExpansive (map (α := α) (β := β)) where
  ne {n x y} H := by
    simp only [map]
    refine OFE.NonExpansive.ne (fun a => ?_)
    simp only [OFE.Hom.comp_apply]
    refine OFE.NonExpansive.ne ?_
    exact H _
theorem map_id {α : Type u} [OFE α] : map (OFE.Hom.id (α := α)) ≡ OFE.Hom.id := by
  simp only [map, OFE.Hom.comp_id]
  exact unit_right
theorem map_comp {α β γ : Type u} [OFE α] [OFE β] [OFE γ] {g : β -n> γ} {f : α -n> β}
  : map (g.comp f) ≡ (map g).comp (map f) := by
  simp only [map, ←OFE.Hom.comp_assoc]
  refine .trans ?_ bind_assoc.symm
  rfl
theorem unit_natural {α β : Type u} [OFE α] [OFE β] {f : α -n> β}
  : (map f).comp unit ≡ unit.comp f := by
  simp only [map]
  exact unit_left

-- completion is idempotent
def idemp {α : Type u} [OFE α] [IsCOFE α] : OFE.Iso α (Completion α) where
  hom := unit
  inv := ⟨IsCOFE.compl, ⟨fun {_ _ _} H => by
    refine IsCOFE.conv_compl.trans ?_
    refine .trans ?_ IsCOFE.conv_compl.symm
    exact H⟩⟩
  hom_inv {x} i := by
    simp only [unit, Chain.const]
    exact IsCOFE.conv_compl
  inv_hom {x} := by
    simp only [unit]
    refine OFE.equiv_dist.mpr (fun n => ?_)
    exact IsCOFE.conv_compl

-- universality
def universal {α β : Type u} [OFE α] [OFE β] [IsCOFE β] (f : α -n> β) : Completion α -n> β where
  f x := IsCOFE.compl (x.map f)
  ne := ⟨fun n x y H => by
    refine IsCOFE.conv_compl.trans ?_
    refine .trans ?_ IsCOFE.conv_compl.symm
    simp only [map]
    suffices H : ((bind.f (unit.comp f)).f x) ≡{n}≡ ((bind.f (unit.comp f)).f y) by
      exact H
    exact OFE.NonExpansive.ne H⟩
theorem universal_comm {α β : Type u} [OFE α] [OFE β] [IsCOFE β] {f : α -n> β} : f ≡ (universal f).comp unit := by
  intro x; simp only [universal, OFE.Hom.comp_apply]
  refine OFE.equiv_dist.mpr (fun n => ?_)
  refine .trans ?_ IsCOFE.conv_compl.symm
  rfl
theorem universal_unique {α β : Type u} [OFE α] [OFE β] [IsCOFE β] {f : α -n> β} {g : Completion α -n> β}
  (H : f ≡ g.comp unit) : g ≡ universal f := by
  intro x; simp only [universal]
  refine OFE.equiv_dist.mpr (fun n => ?_)
  refine .trans ?_ IsCOFE.conv_compl.symm
  refine .trans ?_ map_def.symm
  refine .trans ?_ (H _).symm.dist
  simp only [unit, OFE.Hom.comp_apply]
  refine OFE.NonExpansive.ne ?_
  simp [OFE.Dist]

end Completion

instance [OFE α] [OFE.Discrete α] : OFE.Discrete (Completion α) where
  discrete_0 {x y} h := by
    intro n
    have h0 : x.chain 0 ≡{0}≡ y.chain 0 := h
    have heq : x.chain 0 ≡ y.chain 0 := OFE.discrete_0 h0
    have hx : x.chain n ≡{0}≡ x.chain 0 := x.cauchy (Nat.zero_le n)
    have hy : y.chain n ≡{0}≡ y.chain 0 := y.cauchy (Nat.zero_le n)
    have h_at_0 : x.chain n ≡{0}≡ y.chain n := hx.trans (heq.dist.trans hy.symm)
    have h_equiv : x.chain n ≡ y.chain n := OFE.discrete_0 h_at_0
    exact OFE.equiv_dist.mp h_equiv n

-- wrapper
abbrev CompletionOF (F : COFE.OFunctorPre) [COFE.OFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => Completion (F A B)
instance [COFE.OFunctor F] : COFE.OFunctor (CompletionOF F) where
  cofe := inferInstance
  map f g := Completion.map (COFE.OFunctor.map f g)
  map_ne {_ _ _ _ _ _ _ _} := ⟨fun _ _ _ H _ _ G => OFE.NonExpansive.ne (COFE.OFunctor.map_ne.ne H G)⟩
  map_id {α β _ _} x := by
    refine .trans ?_ (Completion.map_id _)
    suffices H : Completion.map (COFE.OFunctor.map (OFE.Hom.id (α := α)) (OFE.Hom.id (α := β))) ≡ Completion.map (OFE.Hom.id (α := F α β)) by
      exact H _
    refine OFE.equiv_dist.mpr (fun n => ?_)
    refine OFE.NonExpansive.ne ?_
    intro x
    exact (COFE.OFunctor.map_id (F := F) x).dist
  map_comp {α β γ α' β' γ' _ _ _ _ _ _} f g f' g' x := by
    refine .trans ?_ (Completion.map_comp _)
    suffices H : (Completion.map (COFE.OFunctor.map (f.comp g) (g'.comp f')))
      ≡ (Completion.map ((COFE.OFunctor.map g g').comp (COFE.OFunctor.map f f'))) by
      exact H _
    refine OFE.equiv_dist.mpr (fun n => ?_)
    refine OFE.NonExpansive.ne (f := Completion.map) ?_
    intro x
    exact (COFE.OFunctor.map_comp (F := F) _ _ _ _ x).dist
instance [COFE.OFunctorContractive F] : COFE.OFunctorContractive (CompletionOF F) where
  map_contractive {_ _ _ _ _ _ _ _} := by
    refine ⟨?_⟩
    intro n f g H
    simp only [Function.uncurry, CompletionOF, COFE.OFunctor.map]
    refine OFE.NonExpansive.ne (f := Completion.map) ?_
    exact COFE.OFunctorContractive.map_contractive.1 H

abbrev Hyperspace (α : Type u) [OFE α] := Completion (Agree α)

namespace Hyperspace

variable {α : Type u}

def singleton [OFE α] (a : α) : Hyperspace α :=
  Completion.unit.f (toAgree a)

def union [OFE α] (s t : Hyperspace α) : Hyperspace α := {
  chain := fun n => (s.chain n).op (t.chain n)
  cauchy := fun {n i} hni => by
    have hs : s.chain i ≡{n}≡ s.chain n := s.cauchy hni
    have ht : t.chain i ≡{n}≡ t.chain n := t.cauchy hni
    show (s.chain i).op (t.chain i) ≡{n}≡ (s.chain n).op (t.chain n)
    exact Agree.op_ne₂.ne hs ht
}

instance [OFE α] : OFE (Hyperspace α) := inferInstance
instance [OFE α] : IsCOFE (Hyperspace α) := inferInstance

instance singleton_ne [OFE α] : OFE.NonExpansive (singleton (α := α)) where
  ne _ _ _ h := Completion.unit.ne.ne (toAgree.ne.ne h)

instance union_ne [OFE α] : OFE.NonExpansive₂ (union (α := α)) where
  ne {n s₁ s₂} hs {t₁ t₂} ht := by
    show (union s₁ t₁).chain n ≡{n}≡ (union s₂ t₂).chain n
    simp only [union]
    show (s₁.chain n).op (t₁.chain n) ≡{n}≡ (s₂.chain n).op (t₂.chain n)
    exact Agree.op_ne₂.ne hs ht

theorem union_comm [OFE α] (s t : Hyperspace α) : union s t ≡ union t s := by
  intro n
  unfold union
  show (s.chain n).op (t.chain n) ≡{n}≡ (t.chain n).op (s.chain n)
  exact Agree.op_comm n

theorem union_assoc [OFE α] (s t u : Hyperspace α) :
    union (union s t) u ≡ union s (union t u) := by
  intro n
  simp only [union]
  have h : (s.chain n).op ((t.chain n).op (u.chain n)) ≡{n}≡ ((s.chain n).op (t.chain n)).op (u.chain n) :=
    Agree.op_assoc (x := s.chain n) (y := t.chain n) (z := u.chain n) n
  exact h.symm

def mem [OFE α] (a : α) (s : Hyperspace α) (n : Nat) : Prop :=
  ∃ b ∈ (s.chain n).car, a ≡{n}≡ b

instance [OFE α] : Membership α (Hyperspace α) := ⟨fun s a => ∀ n, mem a s n⟩
instance [OFE α] : Singleton α (Hyperspace α) := ⟨singleton⟩
instance [OFE α] : Union (Hyperspace α) := ⟨union⟩

theorem mem_singleton [OFE α] (a b : α) : a ∈ ({b} : Hyperspace α) ↔ a ≡ b := by
  constructor
  · intro h
    apply OFE.equiv_dist.mpr
    intro n
    obtain ⟨c, hc, hac⟩ := h n
    simp only [Singleton.singleton, singleton, Completion.unit, Chain.const_apply, toAgree] at hc
    cases hc with
    | head => exact hac
    | tail _ h => cases h
  · intro h n
    simp only [mem, Singleton.singleton, singleton, Completion.unit, Chain.const_apply]
    exists b
    constructor
    · simp only [toAgree]
      exact List.Mem.head _
    · exact h.dist

theorem mem_union_left [OFE α] (a : α) (s t : Hyperspace α) :
    a ∈ s → a ∈ s ∪ t := by
  intro h n
  obtain ⟨b, hb, hab⟩ := h n
  exists b
  constructor
  · show b ∈ ((s ∪ t).chain n).car
    simp only [Union.union, union, Agree.op, List.mem_append]
    left; exact hb
  · exact hab

theorem mem_union_right [OFE α] (a : α) (s t : Hyperspace α) :
    a ∈ t → a ∈ s ∪ t := by
  intro h n
  obtain ⟨b, hb, hab⟩ := h n
  exists b
  constructor
  · show b ∈ ((s ∪ t).chain n).car
    simp only [Union.union, union, Agree.op, List.mem_append]
    right; exact hb
  · exact hab

theorem mem_union_iff [OFE α] (a : α) (s t : Hyperspace α) (n : Nat) :
    mem a (s ∪ t) n ↔ (∃ b ∈ (s.chain n).car, a ≡{n}≡ b) ∨ (∃ c ∈ (t.chain n).car, a ≡{n}≡ c) := by
  constructor
  · intro ⟨b, hb, hab⟩
    simp only [Union.union, union, Agree.op, List.mem_append] at hb
    cases hb with
    | inl hs => left; exact ⟨b, hs, hab⟩
    | inr ht => right; exact ⟨b, ht, hab⟩
  · intro h
    cases h with
    | inl h =>
      obtain ⟨b, hb, hab⟩ := h
      exists b
      constructor
      · simp only [Union.union, union, Agree.op, List.mem_append]
        left; exact hb
      · exact hab
    | inr h =>
      obtain ⟨c, hc, hac⟩ := h
      exists c
      constructor
      · simp only [Union.union, union, Agree.op, List.mem_append]
        right; exact hc
      · exact hac

theorem singleton_union [OFE α] (a : α) (s : Hyperspace α) :
    {a} ∪ s ≡ union (singleton a) s := by rfl

theorem union_idemp [OFE α] (s : Hyperspace α) : union s s ≡ s := by
  intro n
  simp only [union]
  show (s.chain n).op (s.chain n) ≡{n}≡ s.chain n
  exact Agree.idemp n

instance [OFE α] : CMRA (Hyperspace α) where
  pcore s := some s
  op := union
  ValidN n s := Agree.validN n (s.chain n)
  Valid s := ∀ n, Agree.validN n (s.chain n)
  op_ne := fun {x} => ⟨fun {n y₁ y₂} hy => union_ne.ne (x₁ := x) (x₂ := x) OFE.Dist.rfl hy⟩
  pcore_ne := by simp
  validN_ne := by
    intro n x y hxy hval
    have heq : x.chain n ≡{n}≡ y.chain n := hxy
    exact Agree.validN_ne heq hval
  valid_iff_validN := by
    intro x
    constructor
    · intro h n; exact h n
    · intro h n; exact h n
  validN_succ := @fun (x : Hyperspace α) n hsuc => by
    have h1 : Agree.validN n.succ (x.chain n.succ) := hsuc
    have h2 : Agree.validN n (x.chain n.succ) := CMRA.validN_succ (α := Agree α) h1
    have hcauchy : x.chain n.succ ≡{n}≡ x.chain n := x.cauchy (Nat.le_succ n)
    exact Agree.validN_ne hcauchy h2
  validN_op_left := by
    intro n x y hval
    simp only [union] at hval
    exact CMRA.validN_op_left (α := Agree α) hval
  assoc := fun {x y z} => (union_assoc x y z).symm
  comm := fun {x y} => union_comm x y
  pcore_op_left := by simp [union_idemp]
  pcore_idem := by simp [OFE.Equiv.rfl]
  pcore_op_mono := by simp only [Option.some.injEq]; rintro x _ rfl y; exists y
  extend := by
    intro n x y₁ y₂ hval heq
    simp only [union] at heq
    have heq₂ := Agree.op_invN (Agree.validN_ne heq hval)
    have heq₃ : (y₁.chain n).op (y₂.chain n) ≡{n}≡ y₁.chain n :=
      Agree.op_ne.ne heq₂.symm |>.trans (Agree.idemp n)
    refine ⟨x, x, union_idemp x |>.symm, ?_, ?_⟩
    · exact heq.trans heq₃
    · exact heq.trans heq₃ |>.trans heq₂

instance [OFE α] : CMRA.IsTotal (Hyperspace α) where
  total x := ⟨x, rfl⟩

instance [OFE α] [OFE.Discrete α] : CMRA.Discrete (Hyperspace α) where
  discrete_valid {x} hval := by
    intro n
    have hval0 : Agree.validN 0 (x.chain 0) := hval
    have hval_full : ✓ (x.chain 0) := CMRA.discrete_valid (α := Agree α) hval0
    have hcauchy : x.chain n ≡{0}≡ x.chain 0 := x.cauchy (Nat.zero_le n)
    have heq : x.chain n ≡ x.chain 0 := OFE.discrete_0 hcauchy
    exact CMRA.validN_ne (heq.dist.symm) (hval_full n)

theorem singleton_injN [OFE α] {a b : α} : {a} ≡{n}≡ ({b} : Hyperspace α) → a ≡{n}≡ b := by
  intro heq
  have : (({a} : Hyperspace α).chain n) ≡{n}≡ (({b} : Hyperspace α).chain n) := heq
  simp only [Singleton.singleton, singleton, Completion.unit, Chain.const_apply] at this
  exact Agree.toAgree_injN this

theorem singleton_inj [OFE α] {a b : α} : {a} ≡ ({b} : Hyperspace α) → a ≡ b := by
  simp only [OFE.equiv_dist]
  exact fun heq n => singleton_injN (heq n)

theorem includedN [OFE α] {x y : Hyperspace α} :
    x ≼{n} y ↔ y ≡{n}≡ y ∪ x := by
  refine ⟨fun ⟨z, h⟩ => ?_, fun h => ⟨y, h.trans (union_comm y x n)⟩⟩
  have hid := union_idemp x |>.symm
  calc
    y.chain n ≡{n}≡ (x ∪ z).chain n := h
    _ ≡{n}≡ ((x ∪ x) ∪ z).chain n := .op_l (hid n)
    _ ≡{n}≡ (x ∪ (x ∪ z)).chain n := by
      show ((x ∪ x) ∪ z).chain n ≡{n}≡ (x ∪ (x ∪ z)).chain n
      show ((x.union x).union z).chain n ≡{n}≡ (x.union (x.union z)).chain n
      exact (union_assoc x x z) n
    _ ≡{n}≡ (x ∪ y).chain n := h.symm.op_r
    _ ≡{n}≡ (y ∪ x).chain n := union_comm x y n

theorem included [OFE α] {x y : Hyperspace α} : x ≼ y ↔ y ≡ y ∪ x :=
  ⟨fun ⟨z, h⟩ n => includedN.mp ⟨z, h n⟩, fun h => ⟨y, h.trans (union_comm y x)⟩⟩

theorem valid_includedN [OFE α] {x y : Hyperspace α} :
    ✓{n} y → x ≼{n} y → x ≡{n}≡ y := by
  intro hval ⟨z, heq⟩
  have hvalxz : ✓{n} (x ∪ z) := by
    show Agree.validN n ((x ∪ z).chain n)
    show Agree.validN n ((x.chain n) • (z.chain n))
    exact heq.validN.mp hval
  show x.chain n ≡{n}≡ y.chain n
  have hop_inv := Agree.op_invN hvalxz
  calc
    x.chain n ≡{n}≡ (x ∪ x).chain n := (union_idemp x n).symm
    _ ≡{n}≡ (x ∪ z).chain n := hop_inv.op_r
    _ ≡{n}≡ y.chain n := heq.symm

theorem valid_included [OFE α] {x y : Hyperspace α} :
    ✓ y → x ≼ y → x ≡ y := by
  intro hval ⟨z, heq⟩
  show x ≡ y
  have heq_chain : ∀ n, y.chain n ≡{n}≡ (x.chain n) • (z.chain n) := heq
  have heq' : x ≡ z := by
    intro n
    have hvalxz : Agree.validN n ((x.chain n) • (z.chain n)) :=
      Agree.validN_ne (heq_chain n) (hval n)
    exact Agree.op_invN hvalxz
  calc
    x ≡ x ∪ x := union_idemp x |>.symm
    _ ≡ x ∪ z := .op_r heq'
    _ ≡ y := heq.symm

theorem singleton_includedN [OFE α] {a b : α} :
    {a} ≼{n} ({b} : Hyperspace α) ↔ a ≡{n}≡ b := by
  constructor <;> intro h
  · have hval : ✓{n} ({b} : Hyperspace α) := by
      simp only [CMRA.ValidN, Singleton.singleton, singleton, Completion.unit, Chain.const_apply]
      exact trivial
    exact singleton_injN (valid_includedN hval h)
  · exists {a}
    show ({b} : Hyperspace α).chain n ≡{n}≡ ({a} : Hyperspace α).chain n • ({a} : Hyperspace α).chain n
    simp only [Singleton.singleton, singleton, Completion.unit, Chain.const_apply]
    calc
      toAgree b ≡{n}≡ toAgree a := OFE.NonExpansive.ne h.symm
      _ ≡{n}≡ (toAgree a) • (toAgree a) := Agree.idemp.symm n

theorem singleton_included [OFE α] {a b : α} :
    {a} ≼ ({b} : Hyperspace α) ↔ a ≡ b := by
  constructor <;> intro h
  · have hval : ✓ ({b} : Hyperspace α) := fun _ => trivial
    exact singleton_inj (valid_included hval h)
  · exists {a}
    intro n
    show ({b} : Hyperspace α).chain n ≡{n}≡ ({a} : Hyperspace α).chain n • ({a} : Hyperspace α).chain n
    simp only [Singleton.singleton, singleton, Completion.unit, Chain.const_apply]
    calc
      toAgree b ≡{n}≡ toAgree a := OFE.NonExpansive.ne h.symm.dist
      _ ≡{n}≡ (toAgree a) • (toAgree a) := Agree.idemp.symm n

instance [OFE α] {x : Hyperspace α} : CMRA.Cancelable x where
  cancelableN {n y z} hval heq := by
    show y.chain n ≡{n}≡ z.chain n
    have hval' : Agree.validN n ((x.chain n) • (y.chain n)) := by
      show Agree.validN n ((x ∪ y).chain n)
      simp only [Union.union, union]
      exact hval
    have heq' : (x.chain n) • (y.chain n) ≡{n}≡ (x.chain n) • (z.chain n) := by
      show (x ∪ y).chain n ≡{n}≡ (x ∪ z).chain n
      simp only [Union.union, union]
      exact heq
    exact CMRA.cancelableN (α := Agree α) (x := x.chain n) hval' heq'

instance [OFE α] (a : α) : CMRA.CoreId ({a} : Hyperspace α) where
  core_id := by simp [CMRA.pcore]

theorem singleton_union_validN [OFE α] {a b : α} :
    ✓{n} ({a} ∪ {b} : Hyperspace α) ↔ a ≡{n}≡ b := by
  constructor <;> intro h
  · show a ≡{n}≡ b
    have hval : Agree.validN n (({a} ∪ {b} : Hyperspace α).chain n) := h
    show a ≡{n}≡ b
    simp only [Union.union, union, Singleton.singleton, singleton, Completion.unit, Chain.const_apply] at hval
    show a ≡{n}≡ b
    have := Agree.toAgree_op_validN_iff_dist.mp hval
    exact this
  · show Agree.validN n (({a} ∪ {b} : Hyperspace α).chain n)
    simp only [Union.union, union, Singleton.singleton, singleton, Completion.unit, Chain.const_apply]
    exact Agree.toAgree_op_validN_iff_dist.mpr h

theorem singleton_union_valid [OFE α] {a b : α} :
    ✓ ({a} ∪ {b} : Hyperspace α) ↔ a ≡ b := by
  simp only [OFE.equiv_dist, CMRA.valid_iff_validN]
  constructor <;> intro h n
  · exact singleton_union_validN.mp (h n)
  · exact singleton_union_validN.mpr (h n)

theorem singleton_uninjN [OFE α] {x : Hyperspace α} : ✓{n} x → ∃ a, {a} ≡{n}≡ x := by
  intro hval
  obtain ⟨a, ha⟩ := Agree.toAgree_uninjN hval
  refine ⟨a, ?_⟩
  exact ha

end Hyperspace

abbrev HyperspaceOF (F : COFE.OFunctorPre) [COFE.OFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => Hyperspace (F A B)

def Hyperspace.map {α β : Type u} [OFE α] [OFE β] (f : α -n> β) : Hyperspace α -n> Hyperspace β :=
  Completion.map (Agree.map f).toHom

theorem Hyperspace.map_ne {α β : Type u} [OFE α] [OFE β] (f g : α -n> β) (h : ∀ a, f a ≡{n}≡ g a) :
    Hyperspace.map f ≡{n}≡ Hyperspace.map g := by
  simp only [Hyperspace.map]
  refine OFE.NonExpansive.ne ?_
  intro y
  exact Agree.map_ne h

theorem Hyperspace.map_id {α : Type u} [OFE α] : Hyperspace.map (OFE.Hom.id (α := α)) ≡ OFE.Hom.id := by
  simp only [Hyperspace.map]
  refine OFE.equiv_dist.mpr (fun n => ?_)
  have heq : (Agree.map OFE.Hom.id).toHom = (OFE.Hom.id (α := Agree α)) := by
    ext y
    simp only [OFE.Hom.id, id_eq]
    rw [Agree.map_id y]
  rw [heq]
  exact Completion.map_id.dist

theorem Hyperspace.map_compose {α β γ : Type u} [OFE α] [OFE β] [OFE γ] (f : α -n> β) (g : β -n> γ) :
    Hyperspace.map (g.comp f) ≡ (Hyperspace.map g).comp (Hyperspace.map f) := by
  intro x
  simp only [Hyperspace.map, OFE.Hom.comp_apply]
  refine OFE.equiv_dist.mpr (fun n => ?_)
  have h1 : (Agree.map (g.comp f)).toHom ≡{n}≡ (Agree.map g).toHom.comp (Agree.map f).toHom := by
    intro y
    simp only [OFE.Hom.comp_apply]
    rw [Agree.map_compose f g y]
    rfl
  have inst : OFE.NonExpansive (Completion.map (α := Agree α) (β := Agree γ)) := inferInstance
  have step1 : (Completion.map (Agree.map (g.comp f)).toHom).f x ≡{n}≡
               (Completion.map ((Agree.map g).toHom.comp (Agree.map f).toHom)).f x :=
    inst.ne h1 x
  have step2 := Completion.map_comp (f := (Agree.map f).toHom) (g := (Agree.map g).toHom) x n
  exact step1.trans step2

instance {F} [COFE.OFunctor F] : COFE.OFunctor (HyperspaceOF F) where
  cofe := inferInstance
  map f g := Hyperspace.map (COFE.OFunctor.map f g)
  map_ne {_ _ _ _ _ _ _ _} := ⟨fun {n f₁ f₂} hf {g₁ g₂} hg x =>
    Hyperspace.map_ne _ _ (COFE.OFunctor.map_ne.ne hf hg) x⟩
  map_id {α β _ _} x := by
    simp only [Hyperspace.map]
    refine .trans ?_ (Completion.map_id x)
    suffices H : (Completion.map (Agree.map (COFE.OFunctor.map OFE.Hom.id OFE.Hom.id).f).toHom) ≡ (Completion.map OFE.Hom.id) by
      exact H _
    exact OFE.NonExpansive.eqv (COFE.OFunctor.map_id (F := AgreeRF F))
  map_comp {α β γ α' β' γ' _ _ _ _ _ _} f g f' g' x := by
    simp only [Hyperspace.map]
    refine .trans ?_ (Completion.map_comp x)
    suffices H : (Completion.map (Agree.map (COFE.OFunctor.map (f.comp g) (g'.comp f')).f).toHom)
      ≡ (Completion.map ((Agree.map (COFE.OFunctor.map g g').f).comp (Agree.map (COFE.OFunctor.map f f').f).toHom)) by
      exact H _
    refine OFE.NonExpansive.eqv ?_
    exact (COFE.OFunctor.map_comp (F := AgreeRF F) _ _ _ _)

instance {F} [COFE.OFunctorContractive F] : COFE.OFunctorContractive (HyperspaceOF F) where
  map_contractive {_ _ _ _ _ _ _ _} := by
    refine ⟨?_⟩
    intro n f g h x
    simp only [Function.uncurry, HyperspaceOF, COFE.OFunctor.map]
    refine Hyperspace.map_ne _ _ ?_ x
    exact COFE.OFunctorContractive.map_contractive.1 h

end Iris

end
