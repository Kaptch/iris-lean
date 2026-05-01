module

public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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

@[reducible]
def IsUltrametricDist.OFE {X : Type _} [PseudoMetricSpace X] [IsUltrametricDist X] : OFE X where
  Equiv x y := dist x y = 0
  Dist n x y := dist x y ≤ 1 / (2 ^ n)
  dist_eqv {n} := by
    constructor
    · simp
    · simp [dist_comm]
    · intro x y z H G
      trans
      · exact dist_triangle_max x y z
      · simp only [sup_le_iff]
        exact ⟨H, G⟩
  equiv_dist := by
    intro x y
    norm_num
    constructor
    · rintro heq n; rw [heq]
      positivity
    · intro H
      by_contra HC

      -- have ⟨ε, G⟩ : ∃ ε, ε < dist x y := by
      --   by_contra GC
      --   simp only [not_exists, not_lt] at GC
      --   specialize GC 0

      --   sorry

      sorry
  dist_lt {n x y m} H hlt := by
    trans
    · exact H
    · trans
      · exact one_div_pow2_antitone hlt
      · exact one_div_pow2_antitone (by omega : m ≤ m + 1)

-- TODO: transport

end UMetCompat
