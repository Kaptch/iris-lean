/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Std.Set
public import Iris.Std.PartialMap

@[expose] public section

open Iris Std

section OFE

open OFE

namespace PartialMap

instance instOFE [LawfulPartialMap M K] [OFE V] : OFE (M V) where
  Dist n s0 s1 := get? s0 ≡{n}≡ get? s1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  dist_lt      := dist_lt
  eq_of_dist h := LawfulPartialMap.equiv_iff_eq.mp (fun k => OFE.eq_of_dist (fun n => h n k))

@[simp] def toMap [LawfulPartialMap M K] [OFE V] : (M V) -n> (K → Option V) where
  f x := get? x
  ne.1 {_ _ _} H k := H k

@[simp] def ofMap [LawfulPartialMap M K] [R : RepFunMap M K] [OFE V] :  (K → Option V) -n> (M V) where
  f x := of_fun x
  ne.1 {_ _ _} H k := by simp only [get_of_fun, H k]

instance get?_ne [LawfulPartialMap M K] [OFE V] (k : K) : NonExpansive (get? · k : M V → Option V) where
  ne {_ _ _} Ht := Ht k

instance [LawfulPartialMap M K] [OFE V] (k : K) : NonExpansive₂ (insert · k · : M V → V → M V) where
  ne {_ _ _} Hv {_ _} Ht k' := by
    by_cases h : k = k'
    · simp [get?_insert_eq h, Ht]
    · simp [get?_insert_ne h, Hv k']

theorem eqv_of_Equiv [LawfulPartialMap M K] [OFE V] {t1 t2 : M V} (H : PartialMap.equiv t1 t2) : t1 = t2 :=
  LawfulPartialMap.equiv_iff_eq.mp H

instance [LawfulPartialMap M K] [OFE V] (op : K → V → V → V) [∀ k, NonExpansive₂ (op k)] :
    NonExpansive₂ (merge (M := M) op) where
  ne _ {_ _} Ht {_ _} Hs k := by simp only [get?_merge]; exact NonExpansive₂.ne (Ht k) (Hs k)

/-- Project a chain of stores through its kth coordinate to a chain of values. -/
def chain [LawfulPartialMap M K] [OFE V] (k : K) (c : Chain (M V)) : Chain (Option V) where
  chain i := get? (c i) k
  cauchy Hni := c.cauchy Hni k

theorem chain_get [LawfulPartialMap M K] [OFE V] (k : K) (c : Chain (M V)) :
    (chain k c) i = get? (c i) k := by simp [chain]

end PartialMap

instance Heap.instCOFE [LawfulPartialMap M K] [COFE V] : COFE (M V) where
  compl c := bindAlter (fun _ => COFE.compl <| c.map ⟨_, PartialMap.get?_ne ·⟩) (c 0)
  conv_compl {_ c} k := by
    rw [get?_bindAlter]
    rcases H : get? (c.chain 0) k
    · simp [← PartialMap.chain_get, chain_none_const (c := PartialMap.chain k c) (n := 0) (H▸rfl)]
    · exact IsCOFE.conv_compl

instance instDiscreteHeap [LawfulPartialMap M K] [OFE V] [Discrete V] : Discrete (M V) where
  discrete_0 h := equiv_iff_eq.mp (fun k => OFE.Discrete.discrete_0 (h k))

instance instDiscreteESingleton [LawfulPartialMap M K] [DecidableEq K] [OFE V] {v : V}
    [ha : DiscreteE v] {k : K} : DiscreteE (PartialMap.singleton (M := M) k v) where
  discrete {y} h := equiv_iff_eq.mp fun k' => by
    have hk' := h k'
    by_cases hh : k = k'
    · rw [LawfulPartialMap.get?_singleton_eq hh] at hk' ⊢
      exact Option.some_is_discrete.discrete hk'
    · rw [LawfulPartialMap.get?_singleton_ne hh] at hk' ⊢
      exact Option.none_is_discrete.discrete hk'

instance instDiscreteEEmpty [LawfulPartialMap M K] [OFE V] : DiscreteE (∅ : M V) where
  discrete {y} h := equiv_iff_eq.mp fun k => by
    rw [get?_empty]
    exact Option.none_is_discrete.discrete (get?_empty (M := M) k ▸ h k)

theorem singleton_dist [LawfulPartialMap M K] [DecidableEq K] [OFE V] {n : Nat} {x y : V}
    (h : x ≡{n}≡ y) (k : K) : PartialMap.singleton (M := M) k x ≡{n}≡ PartialMap.singleton k y := by
  intro k'
  simp only [LawfulPartialMap.get?_singleton]
  split <;> simp [h]

theorem singleton_equiv [LawfulPartialMap M K] [DecidableEq K] [OFE V] {x y : V} (h : x = y) (k : K) :
    PartialMap.singleton (M := M) k x = PartialMap.singleton k y :=
  congrArg (PartialMap.singleton k) h

end OFE

section CMRA
open CMRA

/- ## A CMRA on Heaps -/

namespace Heap

open PartialMap

variable [LawfulPartialMap M K] [CMRA V]

@[simp] def op (s1 s2 : M V) : M V := merge (fun _ => CMRA.op) s1 s2
@[simp] def unit : M V := ∅
@[simp] def pcore (s : M V) : Option (M V) := some <| bindAlter (fun _ => CMRA.pcore) s
@[simp] def valid (s : M V) : Prop := ∀ k, ✓ get? s k
@[simp] def validN (n : Nat) (s : M V) : Prop := ∀ k, ✓{n} get? s k

theorem lookup_incN {n} {m1 m2 : M V} :
    (∃ (z : M V), m2 ≡{n}≡ op m1 z) ↔
    ∀ i, (∃ z, (get? m2 i) ≡{n}≡ (get? m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get? z i, ?_⟩
    refine .trans (get?_ne i |>.ne Hz) ?_
    simp only [op, CMRA.op, get?_merge]
    cases get? m1 i <;> cases get? z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists bindAlter (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, get?_merge, get?_bindAlter]
    cases get? m2 i <;> cases get? m1 i <;> cases f i <;> simp

theorem lookup_inc {m1 m2 : M V} :
    (∃ (z : M V), m2 = op m1 z) ↔
    ∀ i, (∃ z, (get? m2 i) = (get? m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get? z i, ?_⟩
    have Hzi : get? m2 i = get? (op m1 z) i := congrFun (congrArg get? Hz) i
    refine .trans Hzi ?_
    simp only [CMRA.op, op, get?_merge]
    cases get? m1 i <;> cases get? z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists bindAlter (fun k _ => f k) m2
    apply equiv_iff_eq.mp; intro i
    refine (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [CMRA.op, optionOp, get?_merge, get?_bindAlter]
    cases get? m2 i <;> cases get? m1 i <;> cases f i <;> simp

open OFE in
instance instStoreCMRA : CMRA (M V) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne.ne _ x1 x2 H i := by
    rename_i x _
    specialize H i; revert H
    simp [get?_merge]
    cases get? x1 i <;> cases get? x2 i <;> cases get? x i <;> simp
    apply op_right_dist
  pcore_ne {n x y _} H := by
    simp only [pcore, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_); specialize H k; revert H
    rw [get?_bindAlter, get?_bindAlter]
    cases get? x k <;> cases get? y k <;> simp
    exact (NonExpansive.ne ·)
  validN_ne Hx H k :=
    validN_ne (NonExpansive.ne (f := (get? · k : M V → Option V)) Hx) (H k)
  valid_iff_validN :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n,
     fun H k => valid_iff_validN.mpr (H · k)⟩
  validN_succ H k := validN_succ (H k)
  validN_op_left {n x1 x2} H k := by
    refine validN_op_left (y := get? x2 k) ?_
    specialize H k; revert H
    simp only [op, get?_merge, Option.merge]
    cases get? x1 k <;> cases get? x2 k <;> simp [optionOp, CMRA.op]
  assoc {x y z} := (equiv_iff_eq (M := M) (K := K)).mp fun k => by
    simp only [op, get?_merge]
    cases get? x k <;> cases get? y k <;> cases get? z k <;> simp
    exact assoc
  comm {x y} := (equiv_iff_eq (M := M) (K := K)).mp fun k => by
    simp [op, get?_merge]
    cases get? x k <;> cases get? y k <;> simp
    exact comm
  pcore_op_left {x cx} H := (equiv_iff_eq (M := M) (K := K)).mp fun k => by
    simp only [← Option.getD_some (a := cx) (b := cx), op, get?_merge]
    cases Hcx : get? cx k <;> cases hx : get? x k <;>
      simp <;>
      simp only [pcore, Option.some.injEq] at H
    · rw [← H, get?_bindAlter, hx] at Hcx
      cases Hcx
    · apply pcore_op_left
      simp [← Hcx, ← H, get?_bindAlter, hx]
  pcore_idem {x cx} H := congrArg some <| (equiv_iff_eq (M := M) (K := K)).mp fun k => by
    simp only [pcore, Option.some.injEq] at H
    simp only [get?_bindAlter, ← H, get?_bindAlter]
    rcases get? x k with (_|v) <;> simp
    cases HY : CMRA.pcore v <;> simp
    exact pcore_idem HY
  pcore_op_mono := by
    apply pcore_op_mono_of_core_op_mono
    rintro x cx y ⟨z, Hz⟩
    suffices ∃ z, (pcore y |>.getD y) = op (pcore x |>.getD x) z by
      rintro Hx
      simp only [pcore, Option.some.injEq, op, exists_eq_left']
      rcases this with ⟨z', Hz'⟩
      refine ⟨z', ?_⟩
      simp only [pcore, Option.getD_some, op] at Hz'
      have hcx : bindAlter (fun x => CMRA.pcore) x = cx := Option.some.inj Hx
      rw [hcx] at Hz'
      exact Hz'
    refine lookup_inc.mpr (fun i => ?_)
    obtain ⟨v', Hv'⟩ : (core (get? x i)) ≼ (core (get? y i)) := by
      apply core_mono
      exists get? z i
      have Hzi : get? y i = get? (op x z) i :=
        congrFun (congrArg get? (Hz : y = op x z)) i
      simp only [op, get?_merge] at Hzi
      rw [Hzi]
      simp [CMRA.op, optionOp, Option.merge]
      cases get? x i <;> cases get? z i <;> simp
    exists v'
    simp_all [CMRA.core, CMRA.pcore, optionCore, get?_bindAlter]
  extend {n x y1 y2} Hm Heq := by
    have Hslice i : get? x i ≡{n}≡ get? y1 i • get? y2 i := by
      refine (get?_ne i |>.ne Heq).trans ?_
      simp [CMRA.op, get?_merge, optionOp]
      cases get? y1 i <;> cases get? y2 i <;> simp
    let extendF (i : K) := CMRA.extend (Hm i) (Hslice i)
    exists bindAlter (fun k (_ : V) => extendF k |>.fst) y1
    exists bindAlter (fun k (_ : V) => extendF k |>.snd.fst) y2
    simp only [op]
    refine ⟨(equiv_iff_eq (M := M) (K := K)).mp fun i => ?_, fun i => ?_, fun i => ?_⟩
    · -- goal: get? x i = get? (merge ... (bindAlter z1 y1) (bindAlter z2 y2)) i
      rcases hF : extendF i with ⟨z1, z2, Hmx, Hz1, Hz2⟩
      have hfst_i : get? (bindAlter (fun k (_ : V) => extendF k |>.fst) y1) i =
          (get? y1 i).bind (fun _ => z1) := by simp [get?_bindAlter, hF]
      have hsnd_i : get? (bindAlter (fun k (_ : V) => extendF k |>.snd.fst) y2) i =
          (get? y2 i).bind (fun _ => z2) := by simp [get?_bindAlter]; rw [hF]
      simp only [hfst_i, hsnd_i, get?_merge]
      simp only [CMRA.op, optionOp] at Hmx
      cases h1 : get? y1 i <;> cases h2 : get? y2 i <;>
        simp only [Option.bind, h1, h2] at Hz1 Hz2 ⊢ <;>
        cases z1 <;> cases z2 <;>
        simp only [show (match (none : Option V), (none : Option V) with
              | some x, some y => some (x • y) | none, x => x | x, none => x) = none from rfl,
            show ∀ v : V, (match (none : Option V), (some v) with
              | some x, some y => some (x • y) | none, x => some v | x, none => none) = some v
              from fun _ => rfl,
            show ∀ v : V, (match (some v), (none : Option V) with
              | some x, some y => some (x • y) | none, x => none | x, none => some v) = some v
              from fun _ => rfl,
            show ∀ v w : V, (match (some v), (some w) with
              | some x, some y => some (x • y) | none, x => some w | x, none => some v)
              = some (v • w) from fun _ _ => rfl] at Hmx ⊢ <;>
        first | exact Hmx | simp_all
    · -- goal: get? (bindAlter z1 y1) i ≡{n}≡ get? y1 i
      rcases hF : extendF i with ⟨z1, z2, Hmx, Hz1, Hz2⟩
      have hfst_i : get? (bindAlter (fun k (_ : V) => extendF k |>.fst) y1) i =
          (get? y1 i).bind (fun _ => z1) := by simp [get?_bindAlter, hF]
      rw [hfst_i]
      cases h1 : get? y1 i with
      | none =>
        simp only [Option.bind]
        cases z1 with
        | none => exact Dist.of_eq rfl
        | some v => simp only [h1] at Hz1; exact absurd Hz1 (by simp)
      | some v1 =>
        simp only [Option.bind]
        exact Hz1.trans (.of_eq h1)
    · -- goal: get? (bindAlter z2 y2) i ≡{n}≡ get? y2 i
      rcases hF : extendF i with ⟨z1, z2, Hmx, Hz1, Hz2⟩
      have hsnd_i : get? (bindAlter (fun k (_ : V) => extendF k |>.snd.fst) y2) i =
          (get? y2 i).bind (fun _ => z2) := by simp [get?_bindAlter]; rw [hF]
      rw [hsnd_i]
      cases h2 : get? y2 i with
      | none =>
        simp only [Option.bind]
        cases z2 with
        | none => exact Dist.of_eq rfl
        | some v => simp only [h2] at Hz2; exact absurd Hz2 (by simp)
      | some v2 =>
        simp only [Option.bind]
        exact Hz2.trans (.of_eq h2)

instance instStoreUCMRA : UCMRA (M V) where
  unit := unit
  unit_valid k := by simp only [valid, unit, get?_empty]; trivial
  unit_left_id := by
    intro x; apply equiv_iff_eq.mp; intro k
    simp [CMRA.op, op, unit, get?_merge, get?_empty]
  pcore_unit := by
    simp only [CMRA.pcore, pcore]; congr 1
    apply equiv_iff_eq.mp; intro k
    simp [get?_bindAlter, get?_empty]

instance instIsTotalHeap : IsTotal (M V) where
  total x := ⟨bindAlter (fun _ => CMRA.pcore) x, rfl⟩

end Heap
end CMRA

namespace Heap

open PartialMap LawfulPartialMap

variable {K V : Type _} [LawfulPartialMap M K] [CMRA V]

open CMRA

theorem get?_op (x y : M V) : get? (x • y) i = get? x i • get? y i := by
  simp only [CMRA.op, op, get?_merge, Option.merge, optionOp]
  grind

theorem valid_empty : ✓ (∅ : M V) :=
  fun k => by simp [Valid, show get? ∅ k = none from get?_empty (M := M) k]

theorem validN_get?_validN {m : M V} (Hv : ✓{n} m) (He : get? m i ≡{n}≡ some x) : ✓{n} x := by
  specialize Hv i; revert Hv
  rcases h : get? m i <;> simp [h] at He
  exact OFE.Dist.validN He |>.mp

theorem validN_get? {m : M V} (v : ✓{n} m) : ✓{n} get? m i :=
  match hh : get? m i with
  | none => ⟨⟩
  | some z => show ✓{n} z from validN_get?_validN v (OFE.Dist.of_eq hh)

theorem valid_get?_valid {m : M V} (Hv : ✓ m) (He : get? m i = some x) : ✓ x :=
  valid_iff_validN.mpr (fun _ => validN_get?_validN Hv.validN He.dist)

theorem valid_get? {m : M V} (v : ✓ m) : ✓ get? m i :=
  valid_iff_validN.mpr (fun _ => Valid.validN (v i))

open Classical in
theorem insert_validN {m : M V} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (insert m i x) := by
  intro k
  rw [get?_insert]; split
  · exact Hx
  · apply Hm

theorem insert_valid {m : M V} (Hx : ✓ x) (Hm : ✓ m) : ✓ (insert m i x) :=
  valid_iff_validN.mpr (fun _ => insert_validN Hx.validN Hm.validN)

open Classical in
theorem singleton_valid_iff : ✓ (singleton i x : M V) ↔ ✓ x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [get?_singleton_eq rfl] at H; trivial
  · rw [get?_singleton]; split <;> trivial

open Classical in
theorem singleton_validN_iff : ✓{n} (singleton i x : M V) ↔ ✓{n} x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [get?_singleton_eq rfl] at H; trivial
  · rw [get?_singleton]; split <;> trivial

open Classical in
theorem delete_validN {m : M V} (Hv : ✓{n} m) : ✓{n} (delete m i) := by
  intro k
  rw [get?_delete]; split
  · trivial
  · exact Hv k

theorem delete_valid {m : M V} (Hv : ✓ m) : ✓ (delete m i) :=
  valid_iff_validN.mpr (fun _ => delete_validN Hv.validN)

open Classical in
theorem insert_equiv_singleton_op_singleton {m : M V} (Hemp : get? m i = none) :
    equiv (insert m i x) (singleton i x • m) := by
  refine (fun k => ?_)
  simp [CMRA.op, Heap.op, get?_merge, Option.merge, get?_singleton, get?_insert]
  split <;> rename_i He
  · rw [← He, Hemp]
  · cases (get? m k) <;> rfl

theorem insert_eq_singleton_op_singleton [IsoFunMap M K] {m : M V} (Hemp : get? m i = none) :
    insert m i x = singleton i x • m :=
  IsoFunMap.ext (insert_equiv_singleton_op_singleton Hemp)

theorem core_empty : core (∅ : M V) = ∅ := by
  apply equiv_iff_eq.mp; intro k
  simp [core, CMRA.pcore, get?_empty, get?_bindAlter]

open Classical in
theorem core_singleton_equiv {i : K} {x : V} {cx : V} (Hpcore : CMRA.pcore x = some cx) :
    equiv (core <| singleton i x : M V) (singleton i cx) := by
  refine fun k => ?_
  simp [← Hpcore, core, CMRA.pcore, get?_singleton, get?_bindAlter]
  split <;> rfl

theorem singleton_core_eq [IsoFunMap M K] {i : K} {x : V} {cx} (Hpcore : CMRA.pcore x = some cx) :
    core (singleton i x : M V) = singleton i cx  :=
  IsoFunMap.ext (core_singleton_equiv Hpcore)

open Classical in
theorem singleton_core_eqv {i : K} {x : V} {cx} (Hpcore : CMRA.pcore x = some cx) :
    core (singleton i x : M V) = singleton i cx := by
  apply equiv_iff_eq.mp; intro k
  simp [core, CMRA.pcore, get?_singleton, get?_bindAlter]
  split <;> trivial

theorem singleton_core_total [IsTotal V] {i : K} {x : V} :
    equiv (core <| singleton i x : M V) ((singleton i (core x))) :=
  core_singleton_equiv (pcore_eq_core x)

theorem singleton_core_total_eq [IsTotal V] [IsoFunMap M K] {i : K} {x : V} :
    core (singleton i x : M V) = singleton i (core x) :=
  IsoFunMap.ext singleton_core_total

open Classical in
theorem singleton_op_singleton {i : K} {x y : V} :
    equiv ((singleton i x : M V) • (singleton i y)) (singleton i (x • y)) := by
  refine fun k => ?_
  simp only [CMRA.op, Heap.op, get?_merge, get?_singleton]
  split <;> simp [Option.merge]

theorem singleton_op_singleton_eq [IsoFunMap M K] {i : K} {x y : V} :
    (singleton i x : M V) • (singleton i y) = (singleton i (x • y)) :=
  IsoFunMap.ext singleton_op_singleton

instance {m : M V} [I : ∀ x : V, CoreId x] : CoreId m where
  core_id := by
    simp only [CMRA.pcore, pcore]; congr 1
    apply equiv_iff_eq.mp; intro k
    simp [get?_bindAlter]; cases get? m k <;> simp; exact core_id

open Classical in
instance [CoreId (x : V)] : CoreId (singleton i x : M V) where
  core_id := by
    simp only [CMRA.pcore, pcore]; congr 1
    apply equiv_iff_eq.mp; intro k
    simp [get?_bindAlter, get?_singleton]; split <;> simp; exact core_id

open Classical in
theorem singleton_incN_iff {m : M V} :
    (singleton i x) ≼{n} m ↔ ∃ y, (get? m i ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i; revert Hz
    simp only [CMRA.op, Heap.op, get?_merge, get?_singleton_eq rfl]
    rcases get? z i with (_|v)
    · intro _
      exists x
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · cases z
    · exists (PartialMap.delete m i)
      intros j
      simp [CMRA.op, get?_merge, get?_singleton, get?_delete]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [CMRA.op]
      · simp
    · rename_i z
      exists (PartialMap.insert m i z)
      intros j
      simp [CMRA.op, get?_merge, get?_singleton, get?_insert]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [CMRA.op]
      · simp

open Classical in
theorem singleton_inc_iff {m : M V} :
    (singleton i x) ≼ m ↔ ∃ y, (get? m i = some y) ∧ some x ≼ some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · rw [Hz]
    simp only [CMRA.op, Heap.op, get?_merge, get?_singleton_eq rfl]
    rcases get? z i with (_|v)
    · exact ⟨x, rfl, none, rfl⟩
    · exact ⟨x • v, rfl, v, rfl⟩
  · cases z
    · exists (PartialMap.delete m i)
      apply equiv_iff_eq.mp; intro j
      simp [CMRA.op, get?_merge, get?_singleton, get?_delete]
      split
      · rename_i h; simp
        refine (h ▸ Hy).trans <| Hz.trans ?_; simp [CMRA.op]
      · simp
    · rename_i z
      exists (PartialMap.insert m i z)
      apply equiv_iff_eq.mp; intro j
      simp [CMRA.op, get?_merge, get?_singleton, get?_insert]
      split
      · rename_i h; simp
        refine (h ▸ Hy).trans <| Hz.trans ?_; simp [CMRA.op]
      · simp

theorem exclusive_singleton_inc_iff {m : M V} (He : Exclusive x) (Hv : ✓ m) :
    (singleton i x) ≼ m ↔ (get? m i = some x) := by
  refine singleton_inc_iff.trans ⟨fun ⟨y, Hy, Hxy⟩ => ?_, fun _ => ?_⟩
  · suffices h : x = y by exact Hy.trans (OFE.some_eqv_some.mpr h.symm)
    exact Option.eqv_of_inc_exclusive Hxy <| valid_get?_valid Hv Hy
  · exists x

theorem singleton_inc_singleton_iff : (singleton i x : M V) ≼ (singleton i y : M V) ↔ some x ≼ some y := by
  refine singleton_inc_iff.trans ⟨fun ⟨z, Hz, Hxz⟩ => ?_, fun H => ?_⟩
  · refine inc_of_inc_of_eqv Hxz ?_
    refine .trans Hz.symm ?_
    exact get?_singleton_eq rfl
  · refine ⟨y, ?_, H⟩
    exact get?_singleton_eq rfl

theorem total_singleton_inc_singleton_iff [IsTotal V] :
    (singleton i x : M V) ≼ (singleton i y) ↔ x ≼ y :=
  singleton_inc_singleton_iff.trans <| Option.some_inc_some_iff_is_total

theorem singleton_inc_singleton_mono (Hinc : x ≼ y) :
    (singleton i x : M V) ≼ (singleton i y) :=
  singleton_inc_singleton_iff.mpr <| Option.some_inc_some_iff.mpr <| .inr Hinc

open Classical in
instance [H : Cancelable (some x)] : Cancelable (singleton i x : M V) where
  cancelableN {n m1 m2} Hv He j := by
    specialize Hv j; revert Hv
    specialize He j; revert He
    simp only [CMRA.op, Heap.op, get?_merge, Option.merge, get?_singleton]
    by_cases He : i = j
    · simp_all only [↓reduceIte]
      intro Hv He
      cases _ : get? m1 j <;> cases _ : get? m2 j
      all_goals apply H.cancelableN
      all_goals simp_all [CMRA.op, optionOp]
    · cases get? m1 j <;> cases get? m2 j <;> simp_all

instance {m : M V} [Hid : ∀ x : V, IdFree x] [Hc : ∀ x : V, Cancelable x] : Cancelable m where
  cancelableN {n m1 m2} Hv He i := by
    apply cancelableN (x := get? m i)
    · specialize Hv i; revert Hv
      simp [CMRA.op, Heap.op, get?_merge, optionOp]
      cases _ : get? m i <;> cases _ : get? m1 i <;> simp_all
    · specialize He i; revert He
      simp [get?_merge, CMRA.op, Heap.op, optionOp]
      cases get? m i <;> cases get? m1 i <;> cases get? m2 i <;> simp_all

theorem insert_op_equiv {m1 m2 : M V} :
    equiv ((insert (m1 • m2) i (x • y))) (insert m1 i x • insert m2 i y) := by
  refine fun j => ?_
  by_cases He : i = j
  · simp [CMRA.op, get?_insert_eq He, get?_merge]
  · simp [CMRA.op, get?_insert_ne He, get?_merge]

theorem insert_op_eq [IsoFunMap M K] {m1 m2 : M (Option V)} :
    (insert (m1 • m2) i (x • y)) = (insert m1 i x • insert m2 i y) :=
  IsoFunMap.ext insert_op_equiv

theorem disjoint_op_equiv_union {m1 m2 : M V} (Hd : Set.Disjoint (dom m1) (dom m2)) :
    equiv (m1 • m2) (union m1 m2) := by
  refine fun j => ?_
  simp [CMRA.op, Heap.op, get?_merge]
  rcases _ : get? m1 j <;> cases _ : get? m2 j <;> simp_all
  refine (Hd j ?_).elim
  simp_all [dom]

theorem disjoint_op_eq_union [IsoFunMap M K] {m1 m2 : M V} (H : Set.Disjoint (dom m1) (dom m2)) :
    m1 • m2 = union m1 m2 :=
  IsoFunMap.ext (disjoint_op_equiv_union H)

theorem valid0_disjoint_dom {m1 m2 : M V} (Hv : ✓{0} (m1 • m2)) (H : ∀ {k x}, get? m1 k = some x → Exclusive x) :
    Set.Disjoint (dom m1) (dom m2) := by
  rintro k
  simp only [dom, Option.isSome]
  rcases HX : get? m1 k with (_|x) <;> simp
  rcases HY : get? m2 k with (_|y) <;> simp
  apply (H HX).1 y
  simp [CMRA.op, CMRA.ValidN] at Hv; specialize Hv k; revert Hv
  simp [get?_merge, HX, HY]

theorem valid_disjoint_dom {m1 m2 : M V} (Hv : ✓ (m1 • m2)) (H : ∀ {k x}, get? m1 k = some x → Exclusive x) :
    Set.Disjoint (dom m1) (dom m2) :=
  valid0_disjoint_dom (Valid.validN Hv) H

theorem dom_op_union (m1 m2 : M V) : dom (m1 • m2) = Set.Union (dom m1) (dom m2) := by
  refine funext fun k => ?_
  cases get? m1 k <;> cases get? m2 k <;> simp_all [CMRA.op, dom, Set.Union, get?_merge]

theorem inc_dom_inc {m1 m2 : M V} (Hinc : m1 ≼ m2) : Set.Included (dom m1) (dom m2) := by
  intro i
  unfold dom
  rcases lookup_inc.mp Hinc i with ⟨z, Hz⟩
  revert Hz
  cases get? m1 i <;> cases get? m2 i <;> cases z <;> simp [CMRA.op, optionOp]

nonrec instance [HD : CMRA.Discrete V] [PartialMap M K] : Discrete (M V) where
  discrete_0 {_ _} H := by apply equiv_iff_eq.mp; intro k; exact OFE.Discrete.discrete_0 (H k)
  discrete_valid {_} := (CMRA.Discrete.discrete_valid <| · ·)

end Heap

section HeapFunctor

variable {K} (H : Type _ → Type _) [LawfulPartialMap H K]

namespace PartialMap

def map (f : α → β) : H α → H β := PartialMap.bindAlter (fun _ a => some <| f a)

instance [OFE α] [OFE β] {f : α → β} [hne : OFE.NonExpansive f] : OFE.NonExpansive (map H f) where
  ne := by
    simp only [OFE.Dist, Option.Forall₂, map, get?_bindAlter, Option.bind]
    refine fun n m1 m2 => forall_imp fun k => ?_
    cases get? m1 k <;> cases get? m2 k <;> simp
    apply OFE.NonExpansive.ne

def map_id [OFE α] (a : H α):
    PartialMap.map H id a = a := by
  apply equiv_iff_eq.mp; intro x
  simp [PartialMap.map, get?_bindAlter, Option.bind]
  rcases get? a x <;> simp

def mapO [OFE α] [OFE β] (f : α -n> β) : OFE.Hom (H α) (H β) where
  f := map H f
  ne := inferInstance

def map_ext [OFE α] [OFE β] {f g : α -> β} (heq : f = g) : map H f m = map H g m := by
  apply equiv_iff_eq.mp; intro k
  simp [map, get?_bindAlter, Option.bind]
  cases get? m k <;> simp
  exact congrFun heq _

def map_ne [OFE α] [OFE β] (f g : α -> β) {heq : f ≡{n}≡ g} : map H f m ≡{n}≡ map H g m := by
  simp [OFE.Dist, Option.Forall₂, map, get?_bindAlter]
  intro k
  cases get? m k <;> simp
  exact heq _

def map_compose [OFE α] [OFE β] [OFE γ] (f : α -> β) (g : β -> γ) m :
    map H (g.comp f) m = map H g (map H f m) := by
  apply equiv_iff_eq.mp; intro k
  simp [map, get?_bindAlter]
  cases get? m k <;> simp

def mapC [CMRA α] [CMRA β] (f : α -C> β) : CMRA.Hom (H α) (H β) where
  f := PartialMap.map H f
  ne := inferInstance
  validN {n x} := by
    simp only [map, CMRA.ValidN, Heap.validN, optionValidN]
    apply forall_imp
    intro k
    rw [get?_bindAlter]
    cases (get? x k) <;> simp
    apply CMRA.Hom.validN
  pcore m := by
    simp only [CMRA.pcore, Heap.pcore, Option.map]
    exact OFE.some_eqv_some.mpr <| by
      apply equiv_iff_eq.mp; intro k
      simp [map, get?_bindAlter]
      rcases get? m k with _|v <;> simp
      have h : (CMRA.pcore v).bind (fun a => some (f a)) = (CMRA.pcore v).map f := by
        rw [Option.map_eq_bind]; rfl
      rw [h]; exact CMRA.Hom.pcore f v
  op x y := by
    apply equiv_iff_eq.mp; intro k
    simp [CMRA.op, map, get?_bindAlter, get?_merge, Option.merge]
    cases get? x k <;> cases get? y k <;> simp
    apply CMRA.Hom.op

abbrev PartialMapOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => H (F A B)

instance {F} [COFE.OFunctor F] : COFE.OFunctor (PartialMapOF H F) where
  cofe := inferInstance
  map f g := mapO H (COFE.OFunctor.map f g)
  map_ne {_} _ _ _ _ _ _ _ := by
    constructor
    intros _ _ _ _ _ _ _ _
    apply map_ne
    apply COFE.OFunctor.map_ne.ne <;> simp_all
  map_id x := by
    refine .trans ?_ (map_id H x)
    apply map_ext
    exact funext (fun a => COFE.OFunctor.map_id a)
  map_comp f g f' g' m := by
    apply equiv_iff_eq.mp; intro x
    simp [mapO, map, get?_bindAlter]
    cases get? m x <;> simp
    exact COFE.OFunctor.map_comp f g f' g' _

instance {F} [RFunctor F] : URFunctor (PartialMapOF H F) where
  map f g := mapC H (RFunctor.map f g)
  map_ne {_} _ _ _ _ _ _ _ := by
    constructor
    intros _ _ _ _ _ _ _ _
    apply map_ne
    apply RFunctor.map_ne.ne <;> simp_all
  map_id x := by
    refine .trans ?_ (map_id H x)
    apply map_ext
    exact funext (fun a => RFunctor.map_id a)
  map_comp f g f' g' m := by
    apply equiv_iff_eq.mp; intro x
    simp [mapC, map, get?_bindAlter]
    cases get? m x <;> simp
    exact (RFunctor.map_comp ..)

instance {F} [RFunctorContractive F] : URFunctorContractive (PartialMapOF H F) where
  map_contractive.1 H m := by
    apply map_ne _ _
    exact (RFunctorContractive.map_contractive.1 H)

end PartialMap
