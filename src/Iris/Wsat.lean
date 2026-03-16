#### Type Classes

```lean
-- Preghost state: the three ghost state components
class WsatGpreS (Σ : GhostStateΣ) where
  wsatGpreS_inv : GmapViewGhost ℕ+ (Agree (Later iProp))
  wsatGpreS_enabled : DisjointCoPsetGhost
  wsatGpreS_disabled : DisjointGsetGhost

-- Full ghost state with names
structure WsatGS (Σ : GhostStateΣ) extends WsatGpreS Σ where
  invariant_name : GhostName
  enabled_name : GhostName
  disabled_name : GhostName
```

#### Core Definitions

```lean
-- Functor composition for the three components
def wsatΣ : GhostStateΣ :=
  GmapViewΣ ℕ+ (AgreeRF (LaterOF idOF)) ⊕
  DisjointCoPsetΣ ⊕
  DisjointGsetΣ

-- Wrapper for later
def invariant_unfold (P : iProp) : Agree (Later iProp) :=
  toAgree (Next P)

-- Own invariant i with proposition P
def ownI (i : ℕ+) (P : iProp) : iProp :=
  own invariant_name (◯M{i} (invariant_unfold P))

-- Own enabled set E
def ownE (E : CoPset) : iProp :=
  own enabled_name (disjoint E)

-- Own disabled set D
def ownD (D : Gset ℕ+) : iProp :=
  own disabled_name (disjoint D)

-- World satisfaction predicate
def wsat : iProp :=
  ∃ I : Gmap ℕ+ (Agree (Later iProp)),
    own invariant_name (●M I) ∗
    ⌜∀ i P, I !! i = Some P → (ownI i P ∨ i ∈ disabled)⌝
```

#### Key Lemmas

```lean
-- Enabled set operations
theorem ownE_op (E1 E2 : CoPset) (H : E1 ## E2) :
  ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2

theorem ownE_disjoint (E1 E2 : CoPset) :
  ownE E1 ∗ ownE E2 -∗ ⌜E1 ## E2⌝

-- Invariant opening
theorem ownI_open (i : ℕ+) (P : iProp) (E : CoPset) :
  wsat ∗ ownI i P ∗ ownE ({i} ∪ E) ==∗
    wsat ∗ ▷ P ∗ ownE E ∗ ownD {i}

-- Invariant closing
theorem ownI_close (i : ℕ+) (P : iProp) (E : CoPset) :
  wsat ∗ ▷ P ∗ ownE E ∗ ownD {i} ==∗
    wsat ∗ ownI i P ∗ ownE ({i} ∪ E)

-- Invariant allocation
theorem ownI_alloc (I : Gset ℕ+) (P : iProp)
  (H : infinite (ℕ+ \ I)) :
  wsat ==∗ ∃ i, ⌜i ∉ I⌝ ∗ wsat ∗ ownI i P ∗ ownE {i}

-- Similar for ownI_alloc_open (allocate but leave open)

-- Initialize world satisfaction
theorem wsat_alloc : ⊢ |==> wsat ∗ ownE ⊤
```
