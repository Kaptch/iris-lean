/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates

@[expose] public section

namespace Iris
open OFE

section GenMap

/-! ## GenMap

The OFE over gmaps is equivalent to a non-dependent discrete function to an `Option` type with a
`Leibniz` OFE of keys, and a finite number of allocated elements.

In this setting, the CMRA is always unital, and as a consequence the oFunctors do not require
unitality in order to act as a `URFunctor(Contractive)`.

GenMap is only intended to be used in the construction of the core IProp model.
It is a stripped-down version of the generic heap constructions, which you should
use instead. -/

def alter (f : Nat → β) (a : Nat) (b : β) : Nat → β :=
  fun a' => if a = a' then b else f a'

/-- A GenMap is a partial map from `Nat` to `β` with finite support.
The `bound` field witnesses that all keys ≥ some `N` map to `none`. -/
structure GenMap (β : Type _) where
  car : Nat → Option β
  bound : ∃ N, ∀ k, N ≤ k → car k = none

instance : CoeFun (GenMap β) (fun _ => Nat → Option β) where
  coe := GenMap.car

nonrec def GenMap.alter (g : GenMap β) (a : Nat) (b : Option β) : GenMap β where
  car := alter g.car a b
  bound := by
    obtain ⟨N, hN⟩ := g.bound
    refine ⟨max N (a + 1), fun k hk => ?_⟩
    simp only [Iris.alter]
    split
    next heq => subst heq; omega
    next => exact hN k (by omega)

def GenMap.empty : GenMap β := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

def GenMap.singleton (x : Nat) (y : β) : GenMap β :=
  empty.alter x y

theorem GenMap.empty_map_lookup (γ : Nat) : (GenMap.empty : GenMap β).car γ = none := rfl

theorem GenMap.singleton_map_in (x : Nat) (y : β) :
    (GenMap.singleton x y).car x = some y := by
  simp [GenMap.singleton, GenMap.alter, GenMap.empty, Iris.alter]

theorem GenMap.singleton_map_none {x : Nat} {y : β} {x' : Nat} (h : x' ≠ x) :
    (GenMap.singleton x y).car x' = none := by
  simp [GenMap.singleton, GenMap.alter, Iris.alter, GenMap.empty]
  rintro rfl
  contradiction

/-- Any GenMap has a fresh key (one mapping to `none`). -/
theorem GenMap.exists_fresh (g : GenMap β) : ∃ k, g.car k = none := by
  obtain ⟨N, hN⟩ := g.bound
  exact ⟨N, hN N (Nat.le_refl N)⟩

/-- Given a GenMap and a predicate that is satisfied by infinitely many naturals
(witnessed by: for any N, there exists k ≥ N with P k), we can find a fresh key
satisfying P. -/
theorem GenMap.exists_fresh_sat (g : GenMap β) {P : Nat → Prop}
    (hP : ∀ N, ∃ k, N ≤ k ∧ P k) : ∃ k, g.car k = none ∧ P k := by
  obtain ⟨N, hN⟩ := g.bound
  obtain ⟨k, hk_ge, hk_P⟩ := hP N
  exact ⟨k, hN k hk_ge, hk_P⟩

/-- `IsFree f a` means key `a` maps to `none` in `f`. Retained for compatibility
with downstream proofs that pattern-match on this. -/
def IsFree {β : α → Type _} (f : (a : α) → Option (β a)) : α → Prop :=
  fun a => f a = none

@[ext] theorem GenMap.ext {a b : GenMap β} (h : a.car = b.car) : a = b := by
  obtain ⟨ca, ba⟩ := a
  obtain ⟨cb, bb⟩ := b
  simp at h; subst h; rfl

/-! ## OFE -/

section OFE
variable (β : Type _) [OFE β]

instance instOFE_GenMap : OFE (GenMap β) where
  Dist n := (·.car ≡{n}≡ ·.car)
  dist_eqv.refl _ := Dist.of_eq rfl
  dist_eqv.symm := Dist.symm
  dist_eqv.trans := Dist.trans
  dist_lt := Dist.lt
  eq_of_dist {x y} h := GenMap.ext (eq_of_dist fun n => h n)
end OFE

theorem GenMap.singleton_discreteE {v : β} [OFE β] [DiscreteE v] :
    DiscreteE (GenMap.singleton (β := β) k v) where
  discrete {y} H := by
    apply GenMap.ext; funext γ'
    have Hγ := H γ'
    simp only [GenMap.singleton, GenMap.alter, GenMap.empty, Iris.alter] at Hγ ⊢
    split
    · next heq => simp only [heq, ite_true] at Hγ ⊢; exact Option.some_is_discrete.discrete Hγ
    · next hne => simp only [hne, ite_false] at Hγ ⊢; exact Option.none_is_discrete.discrete Hγ

theorem GenMap.empty_discreteE [OFE β] : DiscreteE (GenMap.empty (β := β)) where
  discrete {y} H := by
    apply GenMap.ext; funext γ'
    have Hγ := H γ'
    simp only [GenMap.empty] at Hγ ⊢
    exact Option.none_is_discrete.discrete Hγ

/-! ## CMRA -/

section CMRA
open CMRA GenMap

variable (β : Type _) [CMRA β]

theorem op_bound (x y : GenMap β) :
    ∃ N, ∀ k, N ≤ k → (x.car • y.car) k = none := by
  obtain ⟨Nx, hx⟩ := x.bound
  obtain ⟨Ny, hy⟩ := y.bound
  refine ⟨max Nx Ny, fun k hk => ?_⟩
  simp [CMRA.op, optionOp, hx k (by omega), hy k (by omega)]

theorem pcore_bound (x : GenMap β) (cx : Nat → Option β)
    (hpc : CMRA.pcore x.car = some cx) :
    ∃ N, ∀ k, N ≤ k → cx k = none := by
  obtain ⟨N, hN⟩ := x.bound
  have hcx : cx = fun k => CMRA.core (x.car k) := (Option.some.inj hpc).symm
  refine ⟨N, fun k hk => ?_⟩
  rw [hcx]
  simp [CMRA.core, CMRA.pcore, optionCore, hN k hk]

theorem extend_bound {n : Nat} {x : GenMap β}
    {y1 y2 : Nat → Option β} (Hv : ✓{n} x.car) (He : x.car ≡{n}≡ y1 • y2) :
    let F k := CMRA.extend (Hv k) (He k)
    (∃ N, ∀ k, N ≤ k → (fun k => (F k).1) k = none) ∧
    (∃ N, ∀ k, N ≤ k → (fun k => (F k).2.1) k = none) := by
  obtain ⟨N, hN⟩ := x.bound
  have aux : ∀ k, N ≤ k → ∀ (z₁ z₂ : Option β),
      x.car k = z₁ • z₂ → z₁ = none ∧ z₂ = none := by
    intro k hk z₁ z₂ hp1
    have _ : none = z₁ • z₂ := (hN k hk) ▸ hp1
    cases z₁ <;> cases z₂ <;> first | exact ⟨rfl, rfl⟩ | (simp [CMRA.op, optionOp] at *)
  constructor
  · exact ⟨N, fun k hk => (aux k hk _ _ (CMRA.extend (Hv k) (He k)).2.2.1).1⟩
  · exact ⟨N, fun k hk => (aux k hk _ _ (CMRA.extend (Hv k) (He k)).2.2.1).2⟩

def pcore_genmap (x : GenMap β) : Option (GenMap β) :=
  some ⟨fun k => CMRA.core (x.car k), by
    obtain ⟨N, hN⟩ := x.bound
    refine ⟨N, fun k hk => ?_⟩
    simp [CMRA.core, CMRA.pcore, optionCore, hN k hk]⟩

instance instCMRA_GenMap : CMRA (GenMap β) where
  toOFE := instOFE_GenMap β
  pcore := pcore_genmap β
  op x y := ⟨x.car • y.car, op_bound β x y⟩
  ValidN n x := ✓{n} x.car
  Valid x := ✓ x.car
  op_ne.ne {_ _ _} H := op_ne (α := Nat → Option β) |>.ne H
  pcore_ne {n x y cx} H Hm := by
    refine ⟨⟨fun k => CMRA.core (y.car k), ?_⟩, by simp [pcore_genmap], fun k => ?_⟩
    · obtain ⟨N, hN⟩ := y.bound
      exact ⟨N, fun k hk => by simp [CMRA.core, CMRA.pcore, optionCore, hN k hk]⟩
    · suffices hcx : cx.car = fun k => CMRA.core (x.car k) by rw [hcx]; exact (H k).core
      simp only [pcore_genmap, Option.some.injEq] at Hm
      exact (congrArg GenMap.car Hm).symm
  validN_ne {n x y H} := Dist.validN H |>.mp
  valid_iff_validN {x} :=
    ⟨fun Hv n => Hv.validN, fun H => valid_iff_validN.mpr (H ·)⟩
  validN_succ {x n} := validN_succ
  validN_op_left {n x y} := validN_op_left
  assoc {x y z} := by
    apply GenMap.ext; funext a
    cases _ : x.car a <;> cases _ : y.car a <;> cases _ : z.car a <;>
      simp_all [op, optionOp]
    exact assoc
  comm {x y} := by
    apply GenMap.ext; funext a
    cases _ : x.car a <;> cases _ : y.car a <;>
      simp_all [op, optionOp]
    exact comm
  pcore_op_left {x cx} H := by
    have hcx : cx.car = fun k => CMRA.core (x.car k) := by
      simp [pcore_genmap] at H; exact (congrArg GenMap.car H).symm
    apply GenMap.ext; funext k
    have Hk : cx.car k = CMRA.core (x.car k) := congrFun hcx k
    simp only [CMRA.op, optionOp, Hk]
    exact core_op (x.car k)
  pcore_idem {x cx} H := by
    have hcx : cx.car = fun k => CMRA.core (x.car k) := by
      simp [pcore_genmap] at H; exact (congrArg GenMap.car H).symm
    simp only [pcore_genmap]
    congr 1; apply GenMap.ext; funext k
    have Hk : cx.car k = CMRA.core (x.car k) := congrFun hcx k
    simp only [Hk]; exact core_idem (x.car k)
  pcore_op_mono {x cx} H y := by
    have hcx : cx.car = fun k => CMRA.core (x.car k) := by
      simp [pcore_genmap] at H; exact (congrArg GenMap.car H).symm
    -- per-key: pcore (x.car k) = some (cx.car k)
    have hk : ∀ k, CMRA.pcore (x.car k) = some (cx.car k) := fun k => by
      rw [show cx.car k = CMRA.core (x.car k) from congrFun hcx k]
      cases x.car k <;> simp [CMRA.pcore, CMRA.core, optionCore]
    -- per-key: ∃ cyk, pcore (x.car k • y.car k) = some (cx.car k • cyk)
    have hpt : ∀ k, ∃ cyk : Option β,
        CMRA.pcore (x.car k • y.car k) = some (cx.car k • cyk) := fun k => by
      obtain ⟨cyk, hcyk⟩ := CMRA.pcore_op_mono (hk k) (y.car k)
      exact ⟨cyk, hcyk⟩
    -- Build cy using conditional to ensure it's bounded
    obtain ⟨N, hN⟩ := op_bound β x y
    let cyf : Nat → Option β := fun k =>
      if (x.car • y.car) k = none then none else (hpt k).choose
    refine ⟨⟨cyf, N, fun k hk => by simp [cyf, hN k hk]⟩, ?_⟩
    simp only [pcore_genmap]
    congr 1; apply GenMap.ext; funext k
    -- Goal: core ((x.car • y.car) k) = cx.car k • cyf k
    -- = optionCore ((x.car • y.car) k) = cx.car k • cyf k
    -- In all cases we use: hpt k gives pcore (xk • yk) = some (cxk • (hpt k).choose)
    -- cyf k = none iff (x.car • y.car) k = none, else cyf k = (hpt k).choose
    -- optionOp: none • _ = _; _ • none = _; some a • some b = some (a • b)
    -- So (x.car • y.car) k = none only when x.car k = none AND y.car k = none
    have hcyfval : ∀ k, (x.car • y.car) k ≠ none → cyf k = (hpt k).choose := fun k hne => by
      simp [cyf, hne]
    have hcyfnone : ∀ k, (x.car • y.car) k = none → cyf k = none := fun k heq => by
      simp [cyf, heq]
    -- The per-key equality we need to prove:
    -- CMRA.core ((x.car • y.car) k) = CMRA.op (cx.car k) (cyf k)
    -- Both sides are in Option β, so:
    -- LHS = optionCore ((x.car k) • (y.car k))
    -- RHS = optionOp (cx.car k) (cyf k)
    -- We use hpt k : pcore ((x.car k) • (y.car k)) = some (optionOp (cx.car k) ((hpt k).choose))
    -- and CMRA.core = (pcore ·).getD for Option β
    have hgoal : ∀ k, CMRA.core ((x.car • y.car) k) = CMRA.op (cx.car k) (cyf k) := fun k => by
      cases hx : x.car k <;> cases hy : y.car k
      · -- none • none = none; cyf k = none; cx.car k = none
        simp only [CMRA.op, optionOp, hx, hy]
        have hcxnone : cx.car k = none := by
          rw [congrFun hcx k, hx]; simp [CMRA.core, CMRA.pcore, optionCore]
        have hcyfnone' : cyf k = none := hcyfnone k (by simp [CMRA.op, optionOp, hx, hy])
        simp [CMRA.core, CMRA.pcore, optionCore, hcxnone, hcyfnone']
      · -- none • some b = some b; (x.car • y.car) k = some b ≠ none
        rename_i b
        have hne : (x.car • y.car) k ≠ none := by simp [CMRA.op, optionOp, hx, hy]
        have hcxnone : cx.car k = none := by
          rw [congrFun hcx k, hx]; simp [CMRA.core, CMRA.pcore, optionCore]
        have hcyfval' : cyf k = (hpt k).choose := hcyfval k hne
        have hspec := (hpt k).choose_spec
        simp only [CMRA.pcore, CMRA.op, optionOp, hx, hy] at hspec
        rw [hcyfval']
        have hspec2 := Option.some.inj hspec
        simp only [hcxnone] at hspec2
        simp only [CMRA.core, CMRA.pcore, hcxnone, optionCore, Option.bind, Option.getD,
          CMRA.op, optionOp, hx, hy]
        exact hspec2
      · -- some a • none = some a; (x.car • y.car) k = some a ≠ none
        rename_i a
        have hne : (x.car • y.car) k ≠ none := by simp [CMRA.op, optionOp, hx, hy]
        have hcxval : cx.car k = CMRA.core (x.car k) := congrFun hcx k
        have hcyfval' : cyf k = (hpt k).choose := hcyfval k hne
        have hspec := (hpt k).choose_spec
        simp only [CMRA.pcore, CMRA.op, optionOp, hx, hy] at hspec
        rw [hcyfval']
        have hspec2 := Option.some.inj hspec
        simp only [hcxval, hx, CMRA.core, CMRA.pcore, optionCore, Option.bind, Option.getD]
          at hspec2
        simp only [CMRA.core, CMRA.pcore, hcxval, hx, optionCore, Option.bind, Option.getD,
          CMRA.op, optionOp, hy]
        exact hspec2
      · -- some a • some b = some (a • b) ≠ none
        rename_i a b
        have hne : (x.car • y.car) k ≠ none := by simp [CMRA.op, optionOp, hx, hy]
        have hcxval : cx.car k = CMRA.core (x.car k) := congrFun hcx k
        have hcyfval' : cyf k = (hpt k).choose := hcyfval k hne
        have hspec := (hpt k).choose_spec
        simp only [CMRA.pcore, CMRA.op, optionOp, hx, hy] at hspec
        rw [hcyfval']
        have hspec2 := Option.some.inj hspec
        simp only [hcxval, hx, CMRA.core, CMRA.pcore, optionCore, Option.bind, Option.getD]
          at hspec2
        simp only [CMRA.core, CMRA.pcore, hcxval, hx, optionCore, Option.bind, Option.getD,
          CMRA.op, optionOp, hy]
        exact hspec2
    exact hgoal k
  extend {n x y1 y2} := by
    intro Hv H
    have eb := extend_bound β Hv H
    let F k := CMRA.extend (Hv k) (H k)
    refine ⟨⟨fun k => (F k).1, eb.1⟩, ⟨fun k => (F k).2.1, eb.2⟩, ?_,
      fun k => (F k).2.2.2.1, fun k => (F k).2.2.2.2⟩
    apply GenMap.ext; funext k; exact (F k).2.2.1

instance instUCMRA_GenMap : UCMRA (GenMap β) where
  toCMRA := instCMRA_GenMap β
  unit := GenMap.empty
  unit_valid := by simp [Valid, empty]
  unit_left_id {x} := by
    apply GenMap.ext; funext k
    simp only [CMRA.op, optionOp, empty]
  pcore_unit := by
    simp only [pcore_genmap, empty, CMRA.core, CMRA.pcore, optionCore,
      Option.bind, Option.getD]

instance : IsTotal (GenMap β) := @unit_total _ (instUCMRA_GenMap β)

theorem GenMap.alter_valid {g : GenMap β} (Hb : ✓{n} b) (Hg : ✓{n} g) :
    ✓{n} g.alter a b := by
  intro k
  simp only [GenMap.alter, Iris.alter]
  split
  · exact Hb
  · exact Hg k

theorem GenMap.valid_exists_fresh {g : GenMap β} (_Hv : ✓{n} g) : ∃ a : Nat, g.car a = none :=
  g.exists_fresh

theorem GenMap.singleton_map_op (x : Nat) (y1 y2 : β) :
    (singleton x y1 : GenMap β) • singleton x y2 = singleton x (y1 • y2) := by
  apply GenMap.ext
  funext γ
  simp only [CMRA.op, optionOp]
  by_cases h : γ = x
  · subst h; simp [singleton, empty, alter, Iris.alter]
  · simp only [singleton, empty, alter, Iris.alter]
    have : x ≠ γ := Ne.symm h
    simp [if_neg this]

theorem GenMap.singleton_map_pcore (x : Nat) (y : β) (γ : Nat) :
    ((singleton x y : GenMap β).car γ).bind pcore =
    if γ = x then pcore y else none := by
  by_cases h : γ = x
  · subst h
    simp [singleton_map_in]
  · simp_all [singleton_map_none h]

theorem GenMap.validN_singleton_map_in (x : Nat) (y : β) (n : Nat) :
    ✓{n} (singleton x y).car x → ✓{n} y := by
  rw [singleton_map_in]
  simp [ValidN, optionValidN]

theorem GenMap.op_singleton_comm {mf : GenMap β} {x : Nat} (y : β)
    (H_free : IsFree mf.car x) :
    GenMap.singleton x y • mf = mf.alter x (some y) := by
  apply GenMap.ext; funext k
  simp only [IsFree] at H_free
  by_cases heq : k = x
  · subst heq
    simp only [CMRA.op, optionOp, alter, Iris.alter, singleton, empty, ↓reduceIte]
    rw [H_free]
  · simp only [CMRA.op, optionOp, alter, Iris.alter, singleton, empty]
    have : x ≠ k := Ne.symm heq
    rw [if_neg this, if_neg this]

theorem GenMap.validN_op_comm {m mf : GenMap β} (x : Nat) (y : β) (H : IsFree mf.car x) :
    ✓{n} m.alter x (some y) • mf ↔ ✓{n} (m • mf).alter x (some y) := by
  apply Dist.validN
  intro k
  simp only [IsFree] at H
  by_cases heq : k = x
  · subst heq
    simp only [CMRA.op, alter, Iris.alter, ↓reduceIte, optionOp]
    rw [H]
  · simp only [CMRA.op, alter, Iris.alter]
    have : x ≠ k := Ne.symm heq
    rw [if_neg this, if_neg this]

end CMRA

/-! ## OFunctors -/

section OFunctors
open COFE CMRA

abbrev GenMapOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => GenMap (F A B)

abbrev GenMap.lift [OFE α] [OFE β] (f : α -n> β) : GenMap α -n> GenMap β where
  f g := ⟨fun t => Option.map f (g.car t), by
    obtain ⟨N, hN⟩ := g.bound
    exact ⟨N, fun k hk => by simp [Option.map, hN k hk]⟩⟩
  ne.ne {n x1 x2} H γ := by
    specialize H γ
    simp [Option.map]
    split <;> split <;> simp_all
    exact NonExpansive.ne H

instance instOFunctor_GenMapOF (F : OFunctorPre) [OFunctor F] :
    OFunctor (GenMapOF F) where
  cofe {A B _ _} := instOFE_GenMap (F A B)
  map f₁ f₂ := GenMap.lift <| OFunctor.map (F := F) f₁ f₂
  map_ne.ne {n x1 x2} Hx {y1 y2} Hy k γ := by
    simp only [OFE.Dist, Option.Forall₂, Option.map]
    cases _ : k.car γ <;> simp
    exact OFunctor.map_ne.ne Hx Hy _
  map_id {α β _ _} x := by
    apply GenMap.ext; funext γ
    simp only [Option.map]
    cases _ : x.car γ with | none => rfl | some v => exact congrArg some (OFunctor.map_id v)
  map_comp _ _ _ _ x := by
    apply GenMap.ext; funext γ
    simp only [Option.map]
    cases _ : x.car γ with | none => rfl | some v => exact congrArg some (OFunctor.map_comp _ _ _ _ v)

instance instURFunctor_GenMapOF (F : COFE.OFunctorPre) [RFunctor F] :
    URFunctor (GenMapOF F) where
  map f g := {
    toHom := GenMap.lift <| OFunctor.map f g
    validN {n x} hv z := by
      cases h : x.car z with
      | none => simp [Option.map, h, CMRA.ValidN, optionValidN]
      | some v =>
        simp only [Option.map, CMRA.ValidN, optionValidN, h]
        have Hvalid := @(URFunctor.map (F := OptionOF F) f g).validN n v
        simp only [CMRA.ValidN, optionValidN, URFunctor.map] at Hvalid
        have hv' := hv z
        simp only [h, CMRA.ValidN, optionValidN] at hv'
        exact Hvalid hv'
    pcore x := by
      simp only [CMRA.pcore, pcore_genmap, Option.map]
      apply congrArg; apply GenMap.ext; funext γ
      have Hcore := @(URFunctor.map (F := OptionOF F) f g).pcore (x.car γ)
      simp only [CMRA.pcore, optionCore, Option.bind, Option.map, URFunctor.map,
                 OFunctor.map, optionMap, CMRA.core, Option.getD] at Hcore ⊢
      cases h : x.car γ with
      | none => simp
      | some v =>
        revert Hcore
        cases h' : pcore v <;> cases h'' : pcore ((OFunctor.map f g).f v) <;> simp_all
    op z x := by
      apply GenMap.ext; funext γ
      have Hop := @(URFunctor.map (F := OptionOF F) f g).op (z.car γ) (x.car γ)
      simp only [Option.map, CMRA.op, optionOp, URFunctor.map] at Hop ⊢
      cases h : z.car γ <;> cases h' : x.car γ <;>
        simp_all [OFunctor.map, optionMap, Option.Forall₂]
  }
  map_ne.ne := OFunctor.map_ne.ne
  map_id := OFunctor.map_id
  map_comp := OFunctor.map_comp

instance instURFunctorContractive_GenMapOF (F : COFE.OFunctorPre) [RFunctorContractive F] :
    URFunctorContractive (GenMapOF F) where
  map_contractive.1 h := by
    next n x' y' =>
    intro x γ
    have Heqv := @(URFunctorContractive.map_contractive (F := OptionOF F)).1 _ x' y' h (x.car γ)
    simp only [Function.uncurry, URFunctor.map, Option.map] at Heqv ⊢
    cases hc : x.car γ <;> simp [OFE.Dist, Option.Forall₂]
    rw [hc] at Heqv
    exact Heqv

end OFunctors

end GenMap

end Iris
