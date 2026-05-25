module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Lifting
public import Iris.Algebra.HeapView
public import Iris.Algebra.Auth
public import Iris.ProofMode
public import Std.Data.ExtTreeMap

@[expose] public section
namespace Iris.HeapLang

open Iris Auth ProgramLogic Language.Notation Std HeapView

instance : OFE Val := OFE.ofDiscrete _ Eq_Equivalence

instance {F : Type _} [UFraction F] [UCMRA A] {α : A} [IsUnit α] : IsUnit (Auth.frag (F := F) (A := A) α) where
  unit_valid := Auth.frag_valid.mpr IsUnit.unit_valid
  unit_left_id := ⟨UCMRA.unit_left_id, IsUnit.unit_left_id⟩
  pcore_unit := ⟨.rfl, (OFE.Option.ne_match id inferInstance _).eqv IsUnit.pcore_unit⟩

section HeapLangGS

abbrev GenHeapF : COFE.OFunctorPre :=
  HeapViewURF (F := PNat) (H := fun V => Std.ExtTreeMap Loc V compare)
  (constOF (DFrac PNat × Excl Val))

class HeapLangGpreS (hlc : outParam Bool) (GF : BundledGFunctors) extends IrisGS_gen hlc Exp GF where
  heap : ElemG GF GenHeapF

attribute [reducible, instance] HeapLangGpreS.heap

class HeapLangGS (hlc : outParam Bool) (GF : BundledGFunctors) extends HeapLangGpreS hlc GF where
  heap_name : GName

end HeapLangGS

section Predicates

variable {GF : BundledGFunctors} {hlc : Bool} [H : HeapLangGS hlc GF]

def pointsto (l : Loc) (dq : DFrac PNat) (v : Val) : IProp GF :=
  iOwn (E := H.heap) H.heap_name
    (HeapView.Frag (K := Loc) (V := (DFrac PNat × Excl Val)) l dq (dq, Excl.excl v))

end Predicates

notation:20 l " ↦{" dq "} " v => (pointsto (hlc := _) l dq v)
notation:20 l " ↦ " v => (pointsto (hlc := _) l (DFrac.own 1) v)

section Lifting

variable {GF : BundledGFunctors} {hlc : Bool}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

theorem wp_alloc (v : Val) :
  ⊢ (WP (hl(ref(v(v)))) @ s; E {{ l, ∃ l' : Loc, ⌜l = .lit (.loc l')⌝ ∗ (l' ↦ v)}} : IProp GF) := by
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_free (l : Loc) (v : Val) :
  ▷ (l ↦ v) ⊢ (WP (hl(free(#(.loc l)))) @ s; E {{ w, ⌜w = .lit .unit⌝}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_load (l : Loc) (dq : DFrac PNat) (v : Val) :
  ▷ (l ↦{dq} v) ⊢ (WP (hl(!#(.loc l))) @ s; E {{ w, ⌜w = v⌝ ∗ (l ↦{dq} v)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_store (l : Loc) (v v' : Val) :
  ▷ (l ↦ v') ⊢ (WP (hl(#(.loc l) ← v(v))) @ s; E {{ w, ⌜w = .lit .unit⌝ ∗ (l ↦ v)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_xchg (l : Loc) (v v' : Val) :
  ▷ (l ↦ v') ⊢ (WP (hl(xchg(#(.loc l), v(v)))) @ s; E {{ w, ⌜w = v'⌝ ∗ (l ↦ v)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_cmpxchg_fail (l : Loc) (v1 v2 v' : Val)
    (hneq : v' ≠ v1) (hsafe : v'.compareSafe v1) :
  ▷ (l ↦ v') ⊢ (WP (hl(cmpXchg(#(.loc l), v(v1), v(v2)))) @ s; E {{ w, ⌜w = .pair v' (.lit (.bool false))⌝ ∗ (l ↦ v')}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_cmpxchg_suc (l : Loc) (v1 v2 v' : Val)
    (heq : v' = v1) (hsafe : v'.compareSafe v1) :
  ▷ (l ↦ v') ⊢ (WP (hl(cmpXchg(#(.loc l), v(v1), v(v2)))) @ s; E {{ w, ⌜w = .pair v' (.lit (.bool true))⌝ ∗ (l ↦ v2)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_faa (l : Loc) (i1 i2 : Int) :
  ▷ (l ↦ (.lit (.int i1))) ⊢
    (WP (hl(faa(#(.loc l), #(.int i2)))) @ s; E {{ v, ⌜v = .lit (.int i1)⌝ ∗ (l ↦ (.lit (.int (i1 + i2))))}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_fork {GF : BundledGFunctors} {hlc : Bool} (s : Stuckness) (E : CoPset)
    (e : Exp) (Φ : Val → IProp GF) [HeapLangGS hlc GF] :
  (▷ WP e @ s; ⊤ {{ _v, emp }}) -∗
  (▷ (Φ (Val.lit BaseLit.unit))) -∗
  (WP (hl(fork(e))) @ s; E {{ Φ }}) := by
  iintro Hwp HΦ
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

end Lifting

end Iris.HeapLang
