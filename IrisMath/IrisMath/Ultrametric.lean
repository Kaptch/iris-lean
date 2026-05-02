module

public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Iris

@[expose] public section

noncomputable section

open Iris Metric OFE

namespace UMetCompat

open Classical in
noncomputable def ofe_dist {X : Type _} [OFE X] (x y : X) : ℝ :=
  if x ≡ y then 0 else 1 / 2 ^ sSup {n : ℕ | x ≡{n}≡ y}

variable {X : Type _} [OFE X]

abbrev stepSet (x y : X) : Set ℕ := {n | x ≡{n}≡ y}

lemma stepSet_bddAbove {x y : X} (h : ¬ x ≡ y) : BddAbove (stepSet x y) := by
  rw [OFE.equiv_dist] at h
  push Not at h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => by by_contra hlt; exact hN (Dist.lt hn (by omega))⟩

lemma stepSet_finite {x y : X} (h : ¬ x ≡ y) : (stepSet x y).Finite := by
  obtain ⟨N, hN⟩ := stepSet_bddAbove h
  apply Set.Finite.subset (Finset.finite_toSet (Finset.range (N + 1)))
  intro n hn; simp only [Finset.coe_range, Set.mem_Iio]
  suffices n ≤ N by omega
  exact hN hn

lemma stepSet_sSup_mem {x y : X} (h : ¬ x ≡ y) (hs : (stepSet x y).Nonempty) :
    sSup (stepSet x y) ∈ stepSet x y :=
  hs.csSup_mem (stepSet_finite h)

lemma stepSet_down {x y : X} {m n : ℕ} (hmn : m ≤ n) (hn : n ∈ stepSet x y) :
    m ∈ stepSet x y :=
  Dist.le hn hmn

lemma ofe_dist_nonneg (x y : X) : 0 ≤ ofe_dist x y := by
  simp only [ofe_dist]; split_ifs with h
  · norm_num
  · positivity

lemma ofe_dist_le_one (x y : X) : ofe_dist x y ≤ 1 := by
  simp only [ofe_dist]; split_ifs with h
  · norm_num
  · exact div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_two_pow) (by norm_num)

lemma one_div_pow2_antitone : Antitone (fun n : ℕ => (1 : ℝ) / 2 ^ n) := by
  intro a b hab
  apply one_div_le_one_div_of_le (by positivity)
  rw [show b = a + (b - a) from by omega, pow_add]
  exact le_mul_of_one_le_right (by positivity : (0 : ℝ) < 2 ^ a).le
    (by exact_mod_cast Nat.one_le_two_pow)

lemma ofe_dist_triangle_max (x y z : X) :
    ofe_dist x z ≤ max (ofe_dist x y) (ofe_dist y z) := by
  simp only [ofe_dist]
  by_cases hxz : x ≡ z
  · simp only [if_pos hxz]
    exact le_max_of_le_left (ofe_dist_nonneg x y)
  · by_cases hxy : x ≡ y
    · have hyz : ¬ y ≡ z := fun h => hxz (hxy.trans h)
      have heq : {n : ℕ | x ≡{n}≡ z} = {n | y ≡{n}≡ z} :=
        Set.ext fun n => ⟨fun h => (OFE.Equiv.dist hxy.symm).trans h,
                          fun h => (OFE.Equiv.dist hxy).trans h⟩
      simp [if_neg hxz, if_pos hxy, if_neg hyz, heq]
    · by_cases hyz : y ≡ z
      · have heq : {n : ℕ | x ≡{n}≡ z} = {n | x ≡{n}≡ y} :=
          Set.ext fun n => ⟨fun h => h.trans (OFE.Equiv.dist hyz.symm),
                            fun h => h.trans (OFE.Equiv.dist hyz)⟩
        simp [if_neg hxz, if_neg hxy, if_pos hyz, heq]
      · simp only [if_neg hxz, if_neg hxy, if_neg hyz]
        by_cases hA : (stepSet x y).Nonempty
        · by_cases hB : (stepSet y z).Nonempty
          · have hmem_A := stepSet_sSup_mem hxy hA
            have hmem_B := stepSet_sSup_mem hyz hB
            have hmem_C : min (sSup (stepSet x y)) (sSup (stepSet y z)) ∈ stepSet x z :=
              (stepSet_down (Nat.min_le_left _ _) hmem_A).trans
              (stepSet_down (Nat.min_le_right _ _) hmem_B)
            have hC := le_csSup (stepSet_bddAbove hxz) hmem_C
            calc 1 / 2 ^ sSup (stepSet x z)
                ≤ 1 / 2 ^ min (sSup (stepSet x y)) (sSup (stepSet y z)) :=
                  one_div_pow2_antitone hC
              _ = max (1 / 2 ^ sSup (stepSet x y)) (1 / 2 ^ sSup (stepSet y z)) := by
                  by_cases h : sSup (stepSet x y) ≤ sSup (stepSet y z)
                  · rw [min_eq_left h, max_eq_left (one_div_pow2_antitone h)]
                  · push Not at h
                    rw [min_eq_right h.le, max_eq_right (one_div_pow2_antitone h.le)]
          · have hB0 : sSup (stepSet y z) = 0 := by
              simp [Set.not_nonempty_iff_eq_empty.mp hB, csSup_empty]
            simp only [hB0, pow_zero, div_one]
            exact le_max_of_le_right
              (div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_two_pow) (by norm_num))
        · have hA0 : sSup (stepSet x y) = 0 := by
            simp [Set.not_nonempty_iff_eq_empty.mp hA, csSup_empty]
          simp only [hA0, pow_zero, div_one]
          exact le_max_of_le_left
            (div_le_one_of_le₀ (by exact_mod_cast Nat.one_le_two_pow) (by norm_num))

open Classical in
instance {X : Type _} [OFE X] : PseudoMetricSpace X where
  dist := ofe_dist
  dist_self x := by simp [ofe_dist, Equiv.rfl]
  dist_comm x y := by
    simp only [ofe_dist]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · have : {n : ℕ | x ≡{n}≡ y} = {n | y ≡{n}≡ x} :=
        Set.ext fun n => ⟨OFE.Dist.symm, OFE.Dist.symm⟩
      rw [this]
  dist_triangle x y z :=
    le_trans (ofe_dist_triangle_max x y z)
      (max_le (le_add_of_nonneg_right (ofe_dist_nonneg y z))
              (le_add_of_nonneg_left (ofe_dist_nonneg x y)))

open Classical in
instance {X : Type _} [OFE X] : IsUltrametricDist X where
  dist_triangle_max x y z := ofe_dist_triangle_max x y z

instance IsUltrametricDist.OFE {X : Type _} [PseudoMetricSpace X]
    [IsUltrametricDist X] : OFE X where
  Equiv x y := dist x y = 0
  Dist n x y := dist x y ≤ 1 / (2 ^ n)
  dist_eqv {n} := ⟨by simp, by simp [dist_comm], fun {x y z} H G =>
    (dist_triangle_max x y z).trans (max_le H G)⟩
  equiv_dist := by
    refine ⟨fun heq n => by simp [heq], fun H => ?_⟩
    by_contra HC
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (dist_nonneg.lt_of_ne' HC)
      (by norm_num : (1/2 : ℝ) < 1)
    linarith [H n, show (1/2 : ℝ) ^ n = 1 / 2 ^ n by simp [div_eq_inv_mul, mul_comm]]
  dist_lt {n x y m} H hlt := H.trans (one_div_pow2_antitone hlt.le)


section Nonexpansive

variable {X Y : Type _}

theorem NonExpansive.lipschitzWith [OFE X] [OFE Y] (f : X → Y) [NonExpansive f] :
    LipschitzWith 1 f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ofe_dist (f x) (f y) ≤ 1 * ofe_dist x y
  simp only [one_mul]
  simp only [ofe_dist]
  by_cases hxy : x ≡ y
  · have : f x ≡ f y := NonExpansive.eqv hxy
    simp [if_pos this, if_pos hxy]
  · by_cases hfxy : f x ≡ f y
    · simp [if_pos hfxy, if_neg hxy]
    · simp only [if_neg hxy, if_neg hfxy]
      apply one_div_le_one_div_of_le (by positivity)
      suffices h : sSup {n | x ≡{n}≡ y} ≤ sSup {n | f x ≡{n}≡ f y} by
        have : (2 : ℕ) ^ sSup {n | x ≡{n}≡ y} ≤ 2 ^ sSup {n | f x ≡{n}≡ f y} :=
          Nat.pow_le_pow_right (by norm_num) h
        exact_mod_cast this
      by_cases h_ne : {n | x ≡{n}≡ y}.Nonempty
      · apply csSup_le h_ne
        intro n hn
        apply le_csSup (stepSet_bddAbove hfxy)
        exact NonExpansive.ne hn
      · simp [Set.not_nonempty_iff_eq_empty.mp h_ne, csSup_empty]

instance LipschitzWith.toNonExpansive [PseudoMetricSpace X] [IsUltrametricDist X]
    [PseudoMetricSpace Y] [IsUltrametricDist Y] (f : X → Y)
    (hf : LipschitzWith 1 f) : NonExpansive f where
  ne {n x₁ x₂} (h : dist x₁ x₂ ≤ 1 / 2 ^ n) :=
    calc dist (f x₁) (f x₂)
        ≤ 1 * dist x₁ x₂ := hf.dist_le_mul x₁ x₂
      _ = dist x₁ x₂ := by ring
      _ ≤ 1 / 2 ^ n := h

end Nonexpansive

section Roundtrip

variable {X : Type _} [OFE X]

-- proper ofe's should have x ≡{0}≡ y for all x, y
theorem ofe_roundtrip_dist (n : ℕ) (x y : X) (H : x ≡{0}≡ y) :
    @OFE.Dist _ IsUltrametricDist.OFE n x y ↔ x ≡{n}≡ y := by
  change ofe_dist x y ≤ 1 / 2 ^ n ↔ x ≡{n}≡ y
  constructor
  · intro h
    simp only [ofe_dist] at h
    split_ifs at h with g
    · exact g.dist
    · by_cases hnempty : (stepSet x y).Nonempty
      · have hmem := stepSet_sSup_mem g hnempty
        have hs : n ≤ sSup (stepSet x y) := by
          by_contra hlt
          push Not at hlt
          have : (2 : ℝ) ^ sSup (stepSet x y) < 2 ^ n := by
            exact_mod_cast Nat.pow_lt_pow_right (by norm_num) hlt
          have : (1 : ℝ) / 2 ^ n < 1 / 2 ^ sSup (stepSet x y) :=
            one_div_lt_one_div_of_lt (by positivity) this
          linarith
        exact stepSet_down hs hmem
      · exfalso
        exact hnempty ⟨0, H⟩
  · intro h
    simp only [ofe_dist]
    split_ifs with heq
    · have : (0 : ℝ) < 1 / 2 ^ n := by positivity
      linarith
    · have hs : n ≤ sSup {n | x ≡{n}≡ y} := le_csSup (stepSet_bddAbove heq) h
      have : (2 : ℝ) ^ n ≤ 2 ^ sSup {n | x ≡{n}≡ y} := by
        exact_mod_cast Nat.pow_le_pow_right (by positivity) hs
      exact one_div_le_one_div_of_le (by positivity) this

theorem ofe_roundtrip_equiv (x y : X) :
    @OFE.Equiv _ IsUltrametricDist.OFE x y ↔ x ≡ y := by
  change ofe_dist x y = 0 ↔ x ≡ y
  constructor
  · intro h
    simp only [ofe_dist] at h
    split_ifs at h with heq
    · exact heq
    · exfalso
      have : (0 : ℝ) < 1 / 2 ^ sSup (stepSet x y) := by positivity
      linarith
  · intro h
    simp only [ofe_dist, if_pos h]

end Roundtrip

section MetricRoundtrip

variable {X : Type _} [PseudoMetricSpace X] [IsUltrametricDist X]

theorem metric_roundtrip_ofe_dist (x y : X) (hd : dist x y ≤ 1) (n : ℕ) :
    @ofe_dist _ IsUltrametricDist.OFE x y ≤ 1/2^n ↔ dist x y ≤ 1/2^n := by
  simp only [ofe_dist]
  split_ifs with heq
  · change dist x y = 0 at heq
    constructor <;> intro
    · have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
      linarith
    · have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
      linarith
  · change dist x y ≠ 0 at heq
    let S := {k : ℕ | dist x y ≤ 1 / 2 ^ k}
    have hS_eq : {k : ℕ | @OFE.Dist _ IsUltrametricDist.OFE k x y} = S := by rfl
    constructor
    · intro h
      rw [hS_eq] at h
      have hn_le : n ≤ sSup S := by
        by_contra hlt
        push Not at hlt
        have : (2 : ℝ) ^ sSup S < 2 ^ n := by
          exact_mod_cast Nat.pow_lt_pow_right (by norm_num) hlt
        have : (1 : ℝ) / 2 ^ n < 1 / 2 ^ sSup S :=
          one_div_lt_one_div_of_lt (by positivity) this
        linarith
      have hS_nonempty : S.Nonempty := ⟨0, by
        simp only [S, Set.mem_setOf_eq, pow_zero, div_one]; exact hd⟩
      have hS_finite : S.Finite := by
        have hdist_pos : 0 < dist x y := dist_nonneg.lt_of_ne' heq
        obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hdist_pos (by norm_num : (1/2 : ℝ) < 1)
        apply Set.Finite.subset (Finset.finite_toSet (Finset.range (K + 1)))
        intro k hk
        simp only [Finset.coe_range, Set.mem_Iio, S] at hk ⊢
        by_contra hge
        push Not at hge
        have : (2 : ℝ) ^ K < 2 ^ k := by
          exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (by omega : K < k)
        have : (1 : ℝ) / 2 ^ k < 1 / 2 ^ K :=
          one_div_lt_one_div_of_lt (by positivity) this
        have : dist x y < dist x y :=
          calc dist x y
              ≤ 1 / 2 ^ k := hk
            _ < 1 / 2 ^ K := this
            _ = (1/2) ^ K := by simp [div_eq_inv_mul, mul_comm]
            _ < dist x y := hK
        linarith
      have hmem_sup : sSup S ∈ S := hS_nonempty.csSup_mem hS_finite
      have : (2 : ℝ) ^ n ≤ 2 ^ sSup S := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hn_le
      calc dist x y
          ≤ 1 / 2 ^ sSup S := hmem_sup
        _ ≤ 1 / 2 ^ n := one_div_le_one_div_of_le (by positivity) this
    · intro h
      rw [hS_eq]
      have hn_mem : n ∈ S := h
      have hS_bdd : BddAbove S := by
        have hdist_pos : 0 < dist x y := dist_nonneg.lt_of_ne' heq
        obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hdist_pos (by norm_num : (1/2 : ℝ) < 1)
        use K
        intro k (hk : dist x y ≤ 1 / 2 ^ k)
        by_contra hlt
        have h1 : (2 : ℝ) ^ K < 2 ^ k := by
          exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (by omega : K < k)
        have h2 : (1 : ℝ) / 2 ^ k < 1 / 2 ^ K :=
          one_div_lt_one_div_of_lt (by positivity) h1
        have : dist x y < dist x y :=
          calc dist x y
              ≤ 1 / 2 ^ k := hk
            _ < 1 / 2 ^ K := h2
            _ = (1/2) ^ K := by simp [div_eq_inv_mul, mul_comm]
            _ < dist x y := hK
        linarith
      have hn_le : n ≤ sSup S := le_csSup hS_bdd hn_mem
      have : (2 : ℝ) ^ n ≤ 2 ^ sSup S := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hn_le
      exact one_div_le_one_div_of_le (by positivity) this

end MetricRoundtrip

section Categories

open CategoryTheory

class ProperOFE (X : Type*) extends OFE X where
  zero_dist : ∀ (x y : X), x ≡{0}≡ y

def OFECat := Bundled ProperOFE

namespace OFECat

instance : CoeSort OFECat Type* := Bundled.coeSort

instance (X : OFECat) : ProperOFE X := X.str

instance (X : OFECat) : OFE X := X.str.toOFE

def of (X : Type*) [ProperOFE X] : OFECat := Bundled.of X

def NonExpansiveHom (X Y : OFECat) := { f : X → Y // NonExpansive f }

instance : Category OFECat where
  Hom X Y := NonExpansiveHom X Y
  id X := ⟨id, @id_ne _ (X.str.toOFE)⟩
  comp f g := ⟨g.val ∘ f.val, NonExpansive.comp g.property f.property⟩

end OFECat

structure UMetCat where
  carrier : Type*
  metric : PseudoMetricSpace carrier
  ultra : IsUltrametricDist carrier
  bounded : ∀ (x y : carrier), @dist carrier metric.toDist x y ≤ 1

namespace UMetCat

instance : CoeSort UMetCat Type* := ⟨UMetCat.carrier⟩

instance (X : UMetCat) : PseudoMetricSpace X := X.metric

instance (X : UMetCat) : IsUltrametricDist X := X.ultra

def of (X : Type*) [inst1 : PseudoMetricSpace X] [inst2 : IsUltrametricDist X]
    (h : ∀ x y : X, dist x y ≤ 1) : UMetCat :=
  ⟨X, inst1, inst2, h⟩

def LipschitzOneHom (X Y : UMetCat) := { f : X → Y // LipschitzWith 1 f }

instance : Category UMetCat where
  Hom X Y := LipschitzOneHom X Y
  id X := by
    refine ⟨id, ?_⟩
    letI := X.metric
    exact LipschitzWith.id
  comp f g := by
    refine ⟨g.val ∘ f.val, ?_⟩
    convert g.property.comp f.property using 2
    norm_num

end UMetCat

def ofeToUMet : OFECat ⥤ UMetCat where
  obj X := by
    letI : ProperOFE X := X.str
    letI : OFE X := X.str.toOFE
    exact UMetCat.of X (fun x y => ofe_dist_le_one x y)
  map {X Y} f := by
    letI : ProperOFE X := X.str
    letI : ProperOFE Y := Y.str
    letI : OFE X := X.str.toOFE
    letI : OFE Y := Y.str.toOFE
    exact ⟨f.val, @NonExpansive.lipschitzWith X Y X.str.toOFE Y.str.toOFE f.val f.property⟩

def umetToOFE : UMetCat ⥤ OFECat where
  obj X := by
    letI : PseudoMetricSpace X := X.metric
    letI : IsUltrametricDist X := X.ultra
    letI : ProperOFE X := {
      toOFE := IsUltrametricDist.OFE
      zero_dist := fun x y => by
        change dist x y ≤ 1 / 2 ^ 0
        simp only [pow_zero, div_one]
        exact X.bounded x y
    }
    exact OFECat.of X
  map {X Y} f := by
    letI : PseudoMetricSpace X := X.metric
    letI : IsUltrametricDist X := X.ultra
    letI : PseudoMetricSpace Y := Y.metric
    letI : IsUltrametricDist Y := Y.ultra
    refine ⟨f.val, ?_⟩
    exact LipschitzWith.toNonExpansive f.val f.property

end Categories

end UMetCompat
