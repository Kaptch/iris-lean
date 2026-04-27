module

public import Iris.Algebra.OFE

@[expose] public section

namespace Iris

section completion

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

end completion

section powerset

variable {α : Type u}

-- high-level idea: use compact subspaces with hausdorff metric
-- probably will end up as a completion of agree
structure Powerset (α : Type u) [OFE α] [IsCOFE α] where
  pred : α → Prop
  nonempty : ∃ x, pred x
  -- bounded : ∃ y, ∀ x, pred x → x ≡{0}≡ y -- should be totally bounded
  closed : ∀ (c : Chain α), (∀ n, pred (c n)) → pred (IsCOFE.compl c)
  resp_equiv : ∀ x y, x ≡ y → pred x → pred y -- probably should be derived from totally bounded

instance [OFE α] [IsCOFE α] : Membership α (Powerset α) := ⟨fun s a => s.pred a⟩

def Powerset.singleton [OFE α] [IsCOFE α] (a : α) : Powerset α where
  pred := fun x => x ≡ a
  nonempty := ⟨a, OFE.Equiv.rfl⟩
  -- bounded := ⟨a, fun _ H => H.dist⟩
  closed _ hc := OFE.equiv_dist.mpr (fun n => (IsCOFE.conv_compl).trans (hc n).dist)
  resp_equiv := fun _ _ heq hpx => heq.symm.trans hpx

def Powerset.union [OFE α] [IsCOFE α] (a b : Powerset α) : Powerset α where
  pred := fun x => a.pred x ∨ b.pred x
  nonempty := ⟨a.nonempty.choose, Or.inl a.nonempty.choose_spec⟩
  -- bounded := by
  --   obtain ⟨y₁, h₁⟩ := a.bounded
  --   obtain ⟨y₂, h₂⟩ := b.bounded
  closed c hc := by
    by_cases h : ∀ N, ∃ n ≥ N, a.pred (c n)
    · left
      let f : Nat → Nat := fun k => Classical.choose (h k)
      have hf : ∀ k, f k ≥ k ∧ a.pred (c (f k)) := fun k => Classical.choose_spec (h k)
      let c' : Chain α := {
        chain := fun k => c (f k)
        cauchy := fun {n i} hni => (((c.cauchy (ge_iff_le.mp (hf i).1)).le hni).trans (c.cauchy hni)).trans (c.cauchy (ge_iff_le.mp (hf n).1)).symm
      }
      have all_in_a : ∀ k, a.pred (c' k) := fun k => (hf k).2
      have lim_in_a : a.pred (IsCOFE.compl c') := a.closed c' all_in_a
      have eq_lim : IsCOFE.compl c' ≡ IsCOFE.compl c := by
        apply OFE.equiv_dist.mpr
        intro n
        calc IsCOFE.compl c' ≡{n}≡ c' n := IsCOFE.conv_compl
           _ ≡{n}≡ c (f n) := OFE.Dist.rfl
           _ ≡{n}≡ c n := c.cauchy (hf n).1
           _ ≡{n}≡ IsCOFE.compl c := IsCOFE.conv_compl.symm
      exact a.resp_equiv _ _ eq_lim lim_in_a
    · right
      obtain ⟨N, hN⟩ : ∃ N, ∀ n, n ≥ N → ¬a.pred (c n) := by
        apply Classical.byContradiction
        intro hneg
        have : ∀ N, ∃ n, n ≥ N ∧ a.pred (c n) := by
          intro N
          apply Classical.byContradiction
          intro hnot
          have hforall : ∀ n, n ≥ N → ¬a.pred (c n) := by grind only
          apply hneg
          exists N
        exact h this
      have all_in_b : ∀ n ≥ N, b.pred (c n) := by
        intro n hn
        cases hc n with
        | inl ha => exact absurd ha (hN n hn)
        | inr hb => exact hb
      let c' : Chain α := {
        chain := fun n => c (n + N)
        cauchy := fun {n i} hni => (c.cauchy (Nat.add_le_add_right hni N)).le (by omega)
      }
      have eq_lim : IsCOFE.compl c' ≡ IsCOFE.compl c := by
        apply OFE.equiv_dist.mpr
        intro n
        calc IsCOFE.compl c' ≡{n}≡ c' n := IsCOFE.conv_compl
           _ ≡{n}≡ c (n + N) := OFE.Dist.rfl
           _ ≡{n}≡ c n := c.cauchy (Nat.le_add_right n N)
           _ ≡{n}≡ IsCOFE.compl c := IsCOFE.conv_compl.symm
      exact b.resp_equiv _ _ eq_lim (b.closed c' (fun n => all_in_b (n + N) (Nat.le_add_left N n)))
  resp_equiv := fun x y heq hpxy =>
    hpxy.elim (fun ha => Or.inl (a.resp_equiv x y heq ha))
              (fun hb => Or.inr (b.resp_equiv x y heq hb))

def Powerset.inter [OFE α] [IsCOFE α] (a b : Powerset α) : Powerset α where
  pred := fun x => a.pred x ∧ b.pred x
  nonempty := sorry
  closed c hc := sorry
  resp_equiv := sorry

variable [OFE α] [IsCOFE α]

def Powerset.dist (n : Nat) (x y : Powerset α) : Prop :=
  (∀ a, x.pred a → ∃ b, y.pred b ∧ a ≡{n}≡ b) ∧
  (∀ b, y.pred b → ∃ a, x.pred a ∧ a ≡{n}≡ b)

theorem Powerset.dist_equiv : Equivalence (dist (α := α) n) := by
  constructor
  · intro x
    constructor
    · intro a ha
      exact ⟨a, ha, OFE.Dist.rfl⟩
    · intro b hb
      exact ⟨b, hb, OFE.Dist.rfl⟩
  · intro x y ⟨h₁, h₂⟩
    constructor
    · intro a ha
      obtain ⟨b, hb, hd⟩ := h₂ a ha
      exact ⟨b, hb, hd.symm⟩
    · intro b hb
      obtain ⟨a, ha, hd⟩ := h₁ b hb
      exact ⟨a, ha, hd.symm⟩
  · intro x y z ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    constructor
    · intro a ha
      obtain ⟨b, hb, hd₁⟩ := h₁ a ha
      obtain ⟨c, hc, hd₂⟩ := h₂ b hb
      exact ⟨c, hc, hd₁.trans hd₂⟩
    · intro c hc
      obtain ⟨b, hb, hd₁⟩ := h₂' c hc
      obtain ⟨a, ha, hd₂⟩ := h₁' b hb
      exact ⟨a, ha, hd₂.trans hd₁⟩

instance : OFE (Powerset α) where
  Equiv x y := ∀ n, Powerset.dist n x y
  Dist := Powerset.dist
  dist_eqv := Powerset.dist_equiv
  equiv_dist := by simp
  dist_lt {n x y m} := fun ⟨h₁, h₂⟩ hlt => by
    constructor
    · intro a ha
      obtain ⟨b, hb, hd⟩ := h₁ a ha
      exact ⟨b, hb, OFE.Dist.lt hd hlt⟩
    · intro b hb
      obtain ⟨a, ha, hd⟩ := h₂ b hb
      exact ⟨a, ha, OFE.Dist.lt hd hlt⟩

theorem Powerset.equiv_def {x y : Powerset α} : x ≡ y ↔ ∀ n, Powerset.dist n x y := .rfl
theorem Powerset.dist_def {x y : Powerset α} : x ≡{n}≡ y ↔ Powerset.dist n x y := .rfl

theorem Powerset.singleton_dist_singleton {a b : α} :
    Powerset.singleton a ≡{n}≡ Powerset.singleton b ↔ a ≡{n}≡ b := by
  constructor
  · intro ⟨h₁, h₂⟩
    have ha : (Powerset.singleton a).pred a := OFE.Equiv.rfl
    obtain ⟨b', hb', hab⟩ := h₁ a ha
    exact hab.trans hb'.dist
  · intro h
    constructor
    · intro x hx
      exists b
      constructor
      · exact OFE.Equiv.rfl
      · exact hx.dist.trans h
    · intro x hx
      exists a
      constructor
      · exact OFE.Equiv.rfl
      · calc a ≡{n}≡ b := h
             _ ≡{n}≡ x := hx.dist.symm

instance Powerset.singleton_ne : OFE.NonExpansive (Powerset.singleton : α → Powerset α) where
  ne _ _ _ h := Powerset.singleton_dist_singleton.mpr h

end powerset

section powerset_cofe

variable {α : Type u} [OFE α] [IsCOFE α]

instance Powerset.isCOFE : IsCOFE (Powerset α) where
  compl c := {
    pred := fun x => ∃ (chain_α : Chain α), (∀ n, (c n).pred (chain_α n)) ∧ IsCOFE.compl chain_α ≡ x
    nonempty := by
      obtain ⟨x₀, hx₀⟩ := (c 0).nonempty
      exists x₀

      sorry
    -- bounded := by
    --   sorry
    closed c' hc' := by
      exists c'
      refine ⟨?_, .rfl⟩
      intro n
      obtain ⟨c'', H1, H2⟩ := hc' n

      refine resp_equiv _ _ _ H2 ?_
      specialize H1 n

      have T := COFE.conv_compl (c := c'') (n := n)

      -- intro c''
      -- constructor
      -- · intro n
      --   exact (hc' n c'').left n
      -- · apply OFE.equiv_dist.mpr
      --   intro n
      --   exact ((hc' n c'').right.dist (n := n)).trans IsCOFE.conv_compl.symm
      sorry
    resp_equiv := by

      sorry
  }
  conv_compl {n c} := by
    -- constructor
    -- · intro a ha
    --   dsimp at ha
    --   exists a
    --   sorry
    -- · intro b hb
    --   sorry
    sorry

end powerset_cofe

section powerset_ofunctor

open COFE

variable (F : OFunctorPre)

-- def Powerset.mapWith [OFE α] [IsCOFE α] [OFE β] [IsCOFE β] (f : α -n> β) : Powerset α -n> Powerset β where
--   f s := {
--     pred := fun b => ∃ a, s.pred a ∧ f.f a ≡ b
--     nonempty := by
--       obtain ⟨a, ha⟩ := s.nonempty
--       exact ⟨f.f a, a, ha, OFE.Equiv.rfl⟩
--     -- bounded := by
--     --   obtain ⟨y, n, hbound⟩ := s.bounded
--     --   exists f.f y, n
--     --   intro b ⟨a, ha, hfa⟩
--     --   have h1 : a ≡{n}≡ y := hbound a ha
--     --   have h2 : f.f a ≡{n}≡ f.f y := f.ne.ne h1
--     --   exact hfa.symm.dist.trans h2
--     closed := by
--       intro c hc
--       sorry
--   }
--   ne := by
--     constructor
--     intro n x y h
--     constructor
--     · intro b ⟨a, ha, hfa⟩
--       -- ha : x.pred a, hfa : f a ≡ b
--       obtain ⟨a', ha', hdist⟩ := h.1 a ha
--       exists f.f a'
--       refine ⟨⟨a', ha', OFE.Equiv.rfl⟩, ?_⟩
--       calc b ≡{n}≡ f.f a := hfa.dist.symm
--            _ ≡{n}≡ f.f a' := f.ne.ne hdist
--     · intro b ⟨a, ha, hfa⟩
--       -- ha : y.pred a, hfa : f a ≡ b
--       obtain ⟨a', ha', hdist⟩ := h.2 a ha
--       exists f.f a'
--       refine ⟨⟨a', ha', OFE.Equiv.rfl⟩, ?_⟩
--       have h1 : f.f a' ≡{n}≡ f.f a := f.ne.ne hdist
--       have h2 : f.f a ≡{n}≡ b := hfa.dist
--       exact h1.trans h2

-- def PowersetOF (F : OFunctorPre) [OFunctor F] : OFunctorPre :=
--   fun A B inst_A inst_B =>
--     sorry

-- variable [OFunctor F]

-- instance oFunctorPowerset : OFunctor (PowersetOF F) where
--   cofe := sorry
--   map {α₁ α₂ β₁ β₂ _ _ _ _} f g := sorry
--   map_ne := sorry
--   map_id := sorry
--   map_comp := sorry

-- instance [OFunctorContractive F] : OFunctorContractive (PowersetOF F) where
--   map_contractive := sorry

end powerset_ofunctor

end Iris

end
