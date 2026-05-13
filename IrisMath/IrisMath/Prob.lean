/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Iris.Algebra.OFE
import Iris.Algebra.Hyperspace

namespace Iris

/-- sum_le_one : ∑' x, prob x ≤ 1 for partiality? -/
structure FiniteProb (α : Type u) where
  prob : α → ℝ
  prob_in_unit : ∀ x, 0 ≤ prob x ∧ prob x ≤ 1
  countable_support : Set.Countable {x | prob x ≠ 0}
  sum_one : ∑' x, prob x = 1

namespace FiniteProb

variable {α : Type u}

theorem hasSum [OFE α] {μ : FiniteProb α} : HasSum μ.prob 1 := by
  have hsum := μ.sum_one
  have hsumm : Summable μ.prob := by
    by_contra h; rw [tsum_eq_zero_of_not_summable h] at hsum; norm_num at hsum
  rw [← hsum]; exact hsumm.hasSum

theorem summable_prob [OFE α] (μ : FiniteProb α) : Summable μ.prob :=
  hasSum.summable

open scoped Classical in
noncomputable def dirac [OFE α] (a : α) : FiniteProb α where
  prob x := if x = a then 1 else 0
  prob_in_unit x := by by_cases h : x = a <;> simp [h]
  countable_support := by
    apply Set.Countable.mono _ (Set.countable_singleton a)
    intro x hx; simp only [Set.mem_setOf_eq] at hx
    by_cases h : x = a
    · exact h ▸ Set.mem_singleton a
    · simp [h] at hx
  sum_one := by
    rw [tsum_eq_single a]
    · simp
    · intro b hba; simp [hba]

noncomputable def convexComb [OFE α] (μ ν : FiniteProb α) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteProb α where
  prob x := p * μ.prob x + (1 - p) * ν.prob x
  prob_in_unit x := by
    refine ⟨add_nonneg (mul_nonneg hp0 (μ.prob_in_unit x).1)
        (mul_nonneg (by linarith) (ν.prob_in_unit x).1), ?_⟩
    calc p * μ.prob x + (1 - p) * ν.prob x
      ≤ p * 1 + (1 - p) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (μ.prob_in_unit x).2 hp0)
          (mul_le_mul_of_nonneg_left (ν.prob_in_unit x).2 (by linarith))
      _ = 1 := by ring
  countable_support := by
    apply Set.Countable.mono _ (μ.countable_support.union ν.countable_support)
    intro x hx
    by_contra h
    simp only [ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or,
      Decidable.not_not] at h
    exact hx (by show p * μ.prob x + (1 - p) * ν.prob x = 0; rw [h.1, h.2]; ring)
  sum_one := by
    calc ∑' x, (p * μ.prob x + (1 - p) * ν.prob x)
        = ∑' x, p * μ.prob x + ∑' x, (1 - p) * ν.prob x :=
          ((summable_prob μ).mul_left p).tsum_add
            ((summable_prob ν).mul_left (1 - p))
        _ = p * ∑' x, μ.prob x + (1 - p) * ∑' x, ν.prob x := by
          rw [tsum_mul_left, tsum_mul_left]
        _ = 1 := by rw [μ.sum_one, ν.sum_one]; ring

/-! ## Distance on FiniteProb -/

open Classical in
def dist_n [OFE α] (n : Nat) (μ ν : FiniteProb α) : Prop :=
  ∀ (g : α → ℝ),
    (∀ x y, x ≡{n}≡ y → g x = g y) →
    (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
    ∑' x, g x * μ.prob x = ∑' x, g x * ν.prob x

section OFEInstance
variable [OFE α]

open Classical in
private lemma summable_test_mul_prob (μ : FiniteProb α) (g : α → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    Summable (fun x => g x * μ.prob x) :=
  Summable.of_nonneg_of_le
    (fun x => mul_nonneg (hg0 x) (μ.prob_in_unit x).1)
    (fun x => mul_le_of_le_one_left (μ.prob_in_unit x).1 (hg1 x))
    (summable_prob μ)

open Classical in
instance : OFE (FiniteProb α) where
  Dist n μ ν := dist_n n μ ν
  Equiv μ ν := ∀ n, dist_n n μ ν
  dist_eqv := ⟨
    fun _ _ _ _ _ => rfl,
    fun {_ _} h g hg hg0 hg1 => (h g hg hg0 hg1).symm,
    fun {_ _ _} h₁ h₂ g hg hg0 hg1 =>
      (h₁ g hg hg0 hg1).trans (h₂ g hg hg0 hg1)⟩
  equiv_dist := ⟨fun h n => h n, fun h n => h n⟩
  dist_lt := fun {_ _ _ _} h hlt g hg hg0 hg1 =>
    h g (fun x y hxy => hg x y (OFE.Dist.lt hxy hlt)) hg0 hg1

open Classical in
theorem dirac_ne (n : Nat) (x y : α) (h : x ≡{n}≡ y) :
    (dirac x) ≡{n}≡ (dirac y) := by
  intro g hg hg0 hg1
  simp only [dirac]
  have key : ∀ a : α, (∑' z, g z * (if z = a then 1 else 0)) = g a := by
    intro a; rw [tsum_eq_single a (fun b hb => by simp [hb])]; simp
  rw [key x, key y]; exact hg x y h

open Classical in
theorem convexComb_ne (n : Nat) (μ₁ μ₂ ν₁ ν₂ : FiniteProb α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hμ : μ₁ ≡{n}≡ μ₂) (hν : ν₁ ≡{n}≡ ν₂) :
    (convexComb μ₁ ν₁ p hp0 hp1) ≡{n}≡ (convexComb μ₂ ν₂ p hp0 hp1) := by
  intro g hg hg0 hg1
  simp only [convexComb]
  have eq1 : ∀ (a1 a2 : FiniteProb α),
      (∑' x, g x * (p * a1.prob x + (1 - p) * a2.prob x)) =
      p * (∑' x, g x * a1.prob x) + (1 - p) * (∑' x, g x * a2.prob x) := by
    intro a1 a2
    conv_lhs => arg 1; ext x; rw [show g x * (p * a1.prob x + (1 - p) * a2.prob x) =
      p * (g x * a1.prob x) + (1 - p) * (g x * a2.prob x) from by ring]
    rw [(summable_test_mul_prob a1 g hg0 hg1 |>.mul_left p).tsum_add
        (summable_test_mul_prob a2 g hg0 hg1 |>.mul_left (1 - p)),
      tsum_mul_left, tsum_mul_left]
  rw [eq1 μ₁ ν₁, eq1 μ₂ ν₂, hμ g hg hg0 hg1, hν g hg hg0 hg1]

end OFEInstance

/-! ## Pushforward (map) -/

private lemma ite_prob_nonneg (μ : FiniteProb α) (P : α → Prop) [DecidablePred P] :
    ∀ x, 0 ≤ (if P x then μ.prob x else 0) :=
  fun x => by split <;> simp [(μ.prob_in_unit x).1]

private lemma ite_prob_le (μ : FiniteProb α) (P : α → Prop) [DecidablePred P] :
    ∀ x, (if P x then μ.prob x else 0) ≤ μ.prob x :=
  fun x => by split <;> simp [(μ.prob_in_unit x).1]

private lemma summable_ite_prob [OFE α] (μ : FiniteProb α) (P : α → Prop) [DecidablePred P] :
    Summable (fun x => if P x then μ.prob x else 0) :=
  Summable.of_nonneg_of_le (ite_prob_nonneg μ P) (ite_prob_le μ P) (summable_prob μ)

open Classical in
private noncomputable def pushforward_prob {β : Type u}
    (f : α → β) (μ : FiniteProb α) : β → ℝ :=
  fun y => ∑' x, if f x = y then μ.prob x else 0

open Classical in
private lemma pushforward_nonneg {β : Type u}
    (f : α → β) (μ : FiniteProb α) (y : β) :
    0 ≤ pushforward_prob f μ y :=
  tsum_nonneg (ite_prob_nonneg μ (f · = y))

open Classical in
private lemma pushforward_countable_support {β : Type u}
    (f : α → β) (μ : FiniteProb α) :
    Set.Countable {y | pushforward_prob f μ y ≠ 0} := by
  apply Set.Countable.mono _ (μ.countable_support.image f)
  intro y hy
  simp only [Set.mem_setOf_eq, pushforward_prob] at hy
  rw [Set.mem_image]
  by_contra hc; push Not at hc; apply hy
  have hall : ∀ x, (if f x = y then μ.prob x else 0) = 0 := by
    intro x
    by_cases hfx : f x = y
    · simp only [hfx, ite_true]; exact by_contra (fun hp => hc x hp hfx)
    · simp [hfx]
  simp [hall]

section Map
variable [OFE α]

open Classical in
private lemma pushforward_le_one {β : Type u}
    (f : α → β) (μ : FiniteProb α) (y : β) :
    pushforward_prob f μ y ≤ 1 := by
  calc pushforward_prob f μ y
      = ∑' x, if f x = y then μ.prob x else 0 := rfl
    _ ≤ ∑' x, μ.prob x :=
        (summable_ite_prob μ (f · = y)).tsum_mono (summable_prob μ)
          (ite_prob_le μ (f · = y))
    _ = 1 := μ.sum_one

open Classical in
private lemma pushforward_sum_one {β : Type u} [OFE β]
    (f : α → β) (μ : FiniteProb α) :
    ∑' y, pushforward_prob f μ y = 1 := by
  simp only [pushforward_prob]
  set F : (Σ (_ : β), α) → ℝ := fun p => if f p.2 = p.1 then μ.prob p.2 else 0
  set ι : α → (Σ (_ : β), α) := fun x => ⟨f x, x⟩
  have hι_inj : Function.Injective ι := fun x₁ x₂ h =>
    eq_of_heq (Sigma.ext_iff.mp h).2
  have hι_range : ∀ p, p ∉ Set.range ι → F p = 0 := by
    intro ⟨y, x⟩ hp; simp only [F]
    split_ifs with hfx
    · exfalso; apply hp; exact ⟨x, Sigma.ext hfx (heq_of_eq rfl)⟩
    · rfl
  have hFι : F ∘ ι = μ.prob := by ext x; simp [F, ι]
  have hF_hasSum : HasSum F 1 := by
    rw [← Function.Injective.hasSum_iff hι_inj hι_range, hFι]; exact hasSum
  have hfib : ∀ y, Summable (fun x => F ⟨y, x⟩) := by
    intro y
    change Summable (fun x => if f x = y then μ.prob x else 0)
    exact summable_ite_prob μ (f · = y)
  exact (hF_hasSum.sigma (fun y => (hfib y).hasSum)).tsum_eq

open Classical in
noncomputable def pushforward {β : Type u} [OFE β]
    (f : α → β) (μ : FiniteProb α) : FiniteProb β where
  prob := pushforward_prob f μ
  prob_in_unit y := ⟨pushforward_nonneg f μ y, pushforward_le_one f μ y⟩
  countable_support := pushforward_countable_support f μ
  sum_one := pushforward_sum_one f μ

open Classical in
private lemma pushforward_ne {β : Type u} [OFE β] (f : α -n> β)
    (n : Nat) (μ₁ μ₂ : FiniteProb α)
    (hd : μ₁ ≡{n}≡ μ₂) :
    (pushforward f μ₁) ≡{n}≡ (pushforward f μ₂) := by
  intro g hg hg0 hg1
  simp only [pushforward, pushforward_prob]
  suffices key : ∀ (m : FiniteProb α),
      (∑' y, g y * ∑' x, if f.f x = y then m.prob x else 0) =
      ∑' x, g (f.f x) * m.prob x by
    rw [key μ₁, key μ₂]
    exact hd (g ∘ f.f) (fun x y hxy => hg _ _ (f.ne.ne hxy))
      (fun x => hg0 _) (fun x => hg1 _)
  intro m
  have step1 : ∀ y, g y * ∑' x, (if f.f x = y then m.prob x else 0) =
      ∑' x, (if f.f x = y then g y * m.prob x else 0) := by
    intro y; rw [← tsum_mul_left]; congr 1; ext x; split <;> simp
  conv_lhs => arg 1; ext y; rw [step1 y]
  set F : (Σ (_ : β), α) → ℝ := fun p =>
    if f.f p.2 = p.1 then g p.1 * m.prob p.2 else 0
  set ι : α → (Σ (_ : β), α) := fun x => ⟨f.f x, x⟩
  have hι_inj : Function.Injective ι := fun x₁ x₂ h =>
    eq_of_heq (Sigma.ext_iff.mp h).2
  have hι_range : ∀ p, p ∉ Set.range ι → F p = 0 := by
    intro ⟨y, x⟩ hp; simp only [F]
    split_ifs with hfx
    · exfalso; apply hp; exact ⟨x, Sigma.ext hfx (heq_of_eq rfl)⟩
    · rfl
  have hFι : F ∘ ι = fun x => g (f.f x) * m.prob x := by ext x; simp [F, ι]
  have hRHS_summable : Summable (fun x => g (f.f x) * m.prob x) :=
    summable_test_mul_prob m (g ∘ f.f) (fun x => hg0 _) (fun x => hg1 _)
  have hF_hasSum : HasSum F (∑' x, g (f.f x) * m.prob x) := by
    rw [← Function.Injective.hasSum_iff hι_inj hι_range, hFι]
    exact hRHS_summable.hasSum
  have hfib : ∀ y, Summable (fun x => F ⟨y, x⟩) := by
    intro y
    change Summable (fun x => if f.f x = y then g y * m.prob x else 0)
    apply Summable.of_nonneg_of_le
    · intro x; split
      · exact mul_nonneg (hg0 _) (m.prob_in_unit x).1
      · exact le_refl 0
    · intro x; split
      · exact mul_le_of_le_one_left (m.prob_in_unit x).1 (hg1 _)
      · exact (m.prob_in_unit x).1
    · exact summable_prob m
  exact (hF_hasSum.sigma (fun y => (hfib y).hasSum)).tsum_eq

open Classical in
noncomputable def map {β : Type u} [OFE β]
    (f : α -n> β) : FiniteProb α -n> FiniteProb β where
  f := pushforward f
  ne := ⟨fun {n _ _} h => pushforward_ne f n _ _ h⟩

end Map

section Bind
variable [OFE α]

open Classical in
private noncomputable def bind_prob {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) : β → ℝ :=
  fun y => ∑' x, μ.prob x * (f x).prob y

open Classical in
omit [OFE α] in
private lemma bind_nonneg {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) (y : β) :
    0 ≤ bind_prob f μ y :=
  tsum_nonneg fun x => mul_nonneg (μ.prob_in_unit x).1 ((f x).prob_in_unit y).1

omit [OFE α] in
private lemma summable_bind_term [OFE α] {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) (y : β) :
    Summable (fun x => μ.prob x * (f x).prob y) :=
  Summable.of_nonneg_of_le
    (fun x => mul_nonneg (μ.prob_in_unit x).1 ((f x).prob_in_unit y).1)
    (fun x => le_trans
      (mul_le_mul_of_nonneg_left ((f x).prob_in_unit y).2 (μ.prob_in_unit x).1)
      (by rw [mul_one]))
    (summable_prob μ)

open Classical in
private lemma bind_le_one {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) (y : β) :
    bind_prob f μ y ≤ 1 := by
  calc bind_prob f μ y = ∑' x, μ.prob x * (f x).prob y := rfl
    _ ≤ ∑' x, μ.prob x :=
        (summable_bind_term f μ y).tsum_mono (summable_prob μ) fun x =>
          le_trans
            (mul_le_mul_of_nonneg_left ((f x).prob_in_unit y).2 (μ.prob_in_unit x).1)
            (by rw [mul_one])
    _ = 1 := μ.sum_one

open Classical in
omit [OFE α] in
private lemma bind_countable_support {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) :
    Set.Countable {y | bind_prob f μ y ≠ 0} := by
  apply Set.Countable.mono _
    (μ.countable_support.biUnion (fun x _ => (f x).countable_support))
  intro y hy
  simp only [bind_prob, Set.mem_setOf_eq] at hy
  rw [Set.mem_iUnion₂]
  by_contra hc; push Not at hc; apply hy
  have hall : ∀ x, μ.prob x * (f x).prob y = 0 := by
    intro x
    by_cases hp : μ.prob x = 0
    · simp [hp]
    · have : (f x).prob y = 0 := by
        have := hc x hp
        simp only [Set.mem_setOf_eq, ne_eq, Decidable.not_not] at this
        exact this
      simp [this]
  simp [hall]

open Classical in
private lemma bind_sigma_summable {β : Type u} [OFE β]
    (fn : α → FiniteProb β) (μ : FiniteProb α) :
    Summable (fun (p : Σ (_ : β), α) => μ.prob p.2 * (fn p.2).prob p.1) := by
  apply summable_of_sum_le
  · intro ⟨y, x⟩; exact mul_nonneg (μ.prob_in_unit x).1 ((fn x).prob_in_unit y).1
  · intro s
    set t := s.image (Sigma.snd (β := fun _ : β => α))
    have hmap : ∀ i ∈ s, i.2 ∈ t := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    calc ∑ x ∈ t, ∑ p ∈ s.filter (fun p => p.2 = x),
            μ.prob p.2 * (fn p.2).prob p.1
        = ∑ x ∈ t, μ.prob x *
            ∑ p ∈ s.filter (fun p => p.2 = x), (fn x).prob p.1 := by
          apply Finset.sum_congr rfl; intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ⟨_, x'⟩ hmem
          have : x' = x := (Finset.mem_filter.mp hmem).2; subst this; rfl
      _ ≤ ∑ x ∈ t, μ.prob x * 1 := by
          apply Finset.sum_le_sum; intro x _
          apply mul_le_mul_of_nonneg_left _ (μ.prob_in_unit x).1
          set sf := s.filter (fun p : Σ (_ : β), α => p.2 = x)
          have hinj : Set.InjOn (Sigma.fst : (Σ (_ : β), α) → β) ↑sf := by
            intro ⟨_, x₁⟩ h₁ ⟨_, x₂⟩ h₂ heq
            simp only [Finset.mem_coe] at h₁ h₂
            have hx₁ : x₁ = x := (Finset.mem_filter.mp h₁).2
            have hx₂ : x₂ = x := (Finset.mem_filter.mp h₂).2
            subst hx₁; subst hx₂; simp_all
          calc ∑ p ∈ sf, (fn x).prob p.1
              = ∑ y ∈ sf.image Sigma.fst, (fn x).prob y :=
                (Finset.sum_image fun a ha b hb =>
                  hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)).symm
            _ ≤ ∑' y, (fn x).prob y :=
                (summable_prob (fn x)).sum_le_tsum _
                  (fun y _ => ((fn x).prob_in_unit y).1)
            _ = 1 := (fn x).sum_one
      _ = ∑ x ∈ t, μ.prob x := by simp
      _ ≤ ∑' x, μ.prob x :=
          (summable_prob μ).sum_le_tsum t (fun i _ => (μ.prob_in_unit i).1)
      _ = 1 := μ.sum_one

open Classical in
private lemma bind_sum_one {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) :
    ∑' y, bind_prob f μ y = 1 := by
  simp only [bind_prob]
  set F_ax : (Σ (_ : α), β) → ℝ := fun p => μ.prob p.1 * (f p.1).prob p.2
  have hfib_x : ∀ x, HasSum (fun y => F_ax ⟨x, y⟩) (μ.prob x) := by
    intro x; simp only [F_ax]
    have h1 : HasSum (fun y => μ.prob x * (f x).prob y) (μ.prob x * 1) :=
      (hasSum (μ := f x)).mul_left (μ.prob x)
    rwa [mul_one] at h1
  set e : (Σ (_ : α), β) ≃ (Σ (_ : β), α) :=
    ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨a, b⟩,
     fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  have hFe : (fun p => μ.prob p.2 * (f p.2).prob p.1) ∘ e = F_ax := by
    ext ⟨a, b⟩; simp [e, F_ax]
  have hF_ax_summable : Summable F_ax := by
    rw [← hFe]; exact (bind_sigma_summable f μ).comp_injective e.injective
  have hF_ax_hasSum : HasSum F_ax 1 :=
    HasSum.sigma_of_hasSum hasSum hfib_x hF_ax_summable
  have hF_bx_hasSum : HasSum (fun (p : Σ (_ : β), α) => μ.prob p.2 * (f p.2).prob p.1) 1 := by
    rw [← Equiv.hasSum_iff e]
    exact hF_ax_hasSum
  have hfib_y : ∀ y, Summable (fun x => μ.prob x * (f x).prob y) :=
    fun y => (bind_sigma_summable f μ).sigma_factor y
  exact (hF_bx_hasSum.sigma (fun y => (hfib_y y).hasSum)).tsum_eq

open Classical in
noncomputable def bindDist {β : Type u} [OFE β]
    (f : α → FiniteProb β) (μ : FiniteProb α) : FiniteProb β where
  prob := bind_prob f μ
  prob_in_unit y := ⟨bind_nonneg f μ y, bind_le_one f μ y⟩
  countable_support := bind_countable_support f μ
  sum_one := bind_sum_one f μ

open Classical in
private lemma bind_test_swap {β : Type u} [OFE β]
    (fn : α → FiniteProb β) (μ : FiniteProb α)
    (g : β → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∑' y, g y * ∑' x, μ.prob x * (fn x).prob y) =
    ∑' x, (∑' y, g y * (fn x).prob y) * μ.prob x := by
  set F : (Σ (_ : β), α) → ℝ :=
    fun p => g p.1 * μ.prob p.2 * (fn p.2).prob p.1
  have hF_summable : Summable F :=
    Summable.of_nonneg_of_le
      (fun ⟨y, x⟩ => mul_nonneg (mul_nonneg (hg0 y) (μ.prob_in_unit x).1)
        ((fn x).prob_in_unit y).1)
      (fun ⟨y, x⟩ => by
        simp only [F]
        calc g y * μ.prob x * (fn x).prob y
            ≤ 1 * μ.prob x * (fn x).prob y := by
              apply mul_le_mul_of_nonneg_right _ ((fn x).prob_in_unit y).1
              exact mul_le_mul_of_nonneg_right (hg1 y) (μ.prob_in_unit x).1
          _ = μ.prob x * (fn x).prob y := by ring)
      (bind_sigma_summable fn μ)
  have lhs_eq : (∑' y, g y * ∑' x, μ.prob x * (fn x).prob y) =
      ∑' y, ∑' x, F ⟨y, x⟩ := by
    congr 1; ext y; rw [← tsum_mul_left]
    congr 1; ext x; simp only [F]; ring
  have rhs_eq : (∑' x, (∑' y, g y * (fn x).prob y) * μ.prob x) =
      ∑' x, ∑' y, F ⟨y, x⟩ := by
    congr 1; ext x; rw [← tsum_mul_right]
    congr 1; ext y; simp only [F]; ring
  rw [lhs_eq, rhs_eq]
  have hfib_y : ∀ y, HasSum (fun x => F ⟨y, x⟩) (∑' x, F ⟨y, x⟩) :=
    fun y => (hF_summable.sigma_factor y).hasSum
  have hfib_x_summable : ∀ (x : α), Summable (fun y => F ⟨y, x⟩) := by
    intro x
    apply Summable.of_nonneg_of_le
    · intro y; exact mul_nonneg (mul_nonneg (hg0 y) (μ.prob_in_unit x).1)
        ((fn x).prob_in_unit y).1
    · intro y; simp only [F]
      calc g y * μ.prob x * (fn x).prob y
          ≤ 1 * 1 * (fn x).prob y := by
            apply mul_le_mul_of_nonneg_right _ ((fn x).prob_in_unit y).1
            exact mul_le_mul (hg1 y) (μ.prob_in_unit x).2
              (μ.prob_in_unit x).1 zero_le_one
        _ = (fn x).prob y := by ring
    · exact summable_prob (fn x)
  have lhs_total := (HasSum.sigma hF_summable.hasSum hfib_y).tsum_eq
  set e : (Σ (_ : α), β) ≃ (Σ (_ : β), α) :=
    ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨a, b⟩,
     fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  set G : (Σ (_ : α), β) → ℝ := F ∘ e with hG_def
  have hG_hasSum : HasSum G (∑' p, F p) := by
    rw [Equiv.hasSum_iff e]; exact hF_summable.hasSum
  have hfib_x_G : ∀ (x : α), HasSum (fun y => G ⟨x, y⟩) (∑' y, G ⟨x, y⟩) := by
    intro x
    have : Summable (fun y => G ⟨x, y⟩) := by
      change Summable (fun y => F ⟨y, x⟩); exact hfib_x_summable x
    exact this.hasSum
  have hG_rhs : ∀ x, ∑' y, G ⟨x, y⟩ = ∑' y, F ⟨y, x⟩ := by
    intro x; rfl
  have rhs_total : (∑' x, ∑' y, F ⟨y, x⟩) = ∑' p, F p := by
    conv_lhs => arg 1; ext x; rw [← hG_rhs x]
    exact (HasSum.sigma hG_hasSum hfib_x_G).tsum_eq
  rw [lhs_total, rhs_total]

open Classical in
private lemma bind_ne {β : Type u} [OFE β] (f : α -n> FiniteProb β)
    (n : Nat) (μ₁ μ₂ : FiniteProb α)
    (hd : μ₁ ≡{n}≡ μ₂) :
    (bindDist f μ₁) ≡{n}≡ (bindDist f μ₂) := by
  intro g hg hg0 hg1
  simp only [bindDist, bind_prob]
  rw [bind_test_swap f.f μ₁ g hg0 hg1, bind_test_swap f.f μ₂ g hg0 hg1]
  apply hd
  · intro x₁ x₂ hx12; exact (f.ne.ne hx12) g hg hg0 hg1
  · intro x; exact tsum_nonneg
      (fun y => mul_nonneg (hg0 y) ((f.f x).prob_in_unit y).1)
  · intro x
    calc ∑' y, g y * (f.f x).prob y
        ≤ ∑' y, 1 * (f.f x).prob y :=
          (summable_test_mul_prob (f.f x) g hg0 hg1).tsum_mono
            ((summable_prob (f.f x)).mul_left 1)
            (fun y => mul_le_mul_of_nonneg_right (hg1 y)
              ((f.f x).prob_in_unit y).1)
      _ = 1 := by simp [(f.f x).sum_one]

open Classical in
noncomputable def bind {β : Type u} [OFE β]
    (f : α -n> FiniteProb β) : FiniteProb α -n> FiniteProb β where
  f := bindDist f
  ne := ⟨fun {n _ _} h => bind_ne f n _ _ h⟩

open Classical in
private lemma bindDist_dist_n_gen {β : Type u} [OFE β]
    (fn fi : α → FiniteProb β) (n : Nat) (μ₁ μ₂ : FiniteProb α)
    (hfn_inv : ∀ x₁ x₂, x₁ ≡{n}≡ x₂ → (fn x₁) ≡{n}≡ (fn x₂))
    (hfi_eq : ∀ x, (fn x) ≡{n}≡ (fi x))
    (hd : μ₁ ≡{n}≡ μ₂) :
    (bindDist fn μ₁) ≡{n}≡ (bindDist fi μ₂) := by
  intro g hg hg0 hg1
  simp only [bindDist, bind_prob]
  rw [bind_test_swap fn μ₁ g hg0 hg1, bind_test_swap fi μ₂ g hg0 hg1]
  have h_eq : ∀ x,
      (∑' y, g y * (fn x).prob y) = (∑' y, g y * (fi x).prob y) :=
    fun x => (hfi_eq x) g hg hg0 hg1
  conv_rhs => arg 1; ext x; rw [← h_eq x]
  apply hd
  · intro x₁ x₂ hx12; exact (hfn_inv x₁ x₂ hx12) g hg hg0 hg1
  · intro x; exact tsum_nonneg
      (fun y => mul_nonneg (hg0 y) ((fn x).prob_in_unit y).1)
  · intro x
    calc ∑' y, g y * (fn x).prob y
        ≤ ∑' y, 1 * (fn x).prob y :=
          (summable_test_mul_prob (fn x) g hg0 hg1).tsum_mono
            ((summable_prob (fn x)).mul_left 1)
            (fun y => mul_le_mul_of_nonneg_right (hg1 y)
              ((fn x).prob_in_unit y).1)
      _ = 1 := by simp [(fn x).sum_one]

end Bind

end FiniteProb

abbrev Prob (α : Type u) [OFE α] := Completion (FiniteProb α)

namespace FiniteProb

section FunctorLaws
variable {α : Type u} {β : Type u} {γ : Type u} [OFE α] [OFE β] [OFE γ]

open Classical in
theorem pushforward_integral
    (f : α -n> β) (μ : FiniteProb α) (g : β → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    ∑' y, g y * (pushforward f μ).prob y = ∑' x, g (f.f x) * μ.prob x := by
  unfold pushforward; simp only
  have h_sum : ∑' y, ∑' x, (if f.f x = y then g y * μ.prob x else 0)
    = ∑' x, g (f.f x) * μ.prob x := by
    rw [← Summable.tsum_comm]
    · exact tsum_congr fun x => by rw [tsum_eq_single ( f.f x )] <;> aesop
    · have h_summable : Summable (fun x => g (f.f x) * μ.prob x) := by
        exact Summable.of_nonneg_of_le (fun x => mul_nonneg (hg0 _ ) (μ.prob_in_unit x |>.1))
          (fun x => mul_le_of_le_one_left (μ.prob_in_unit x |>.1) (hg1 _)) (μ.summable_prob)
      rw [summable_iff_vanishing] at *
      intro e he; obtain ⟨s, hs⟩ := h_summable e he
      use s.image (fun x => (f.f x, x))
      intro t ht; simp_all only [Finset.disjoint_left, Finset.mem_image, not_exists, not_and,
        Prod.forall, Prod.mk.injEq, Function.uncurry]
      convert hs (Finset.image Prod.snd (t.filter fun x => f.f x.2 = x.1)) _ using 1
      · rw [Finset.sum_image]
        · rw [Finset.sum_filter]; congr; ext; aesop
        · intro x hx y hy; aesop
      · grind
  convert h_sum using 3 ; simp only [pushforward_prob]; ring_nf
  rw [← tsum_mul_left]; congr; ext; split_ifs <;> ring

open Classical in
theorem map_id_equiv :
    FiniteProb.map (OFE.Hom.id : α -n> α) ≡ OFE.Hom.id := by
  unfold map
  unfold pushforward
  unfold pushforward_prob; aesop

open Classical in
theorem map_comp_equiv (g : β -n> γ) (f : α -n> β) :
    FiniteProb.map (g.comp f) ≡ (FiniteProb.map g).comp (FiniteProb.map f) := by
  have h_eq : ∀ (μ : FiniteProb α) (h : γ → ℝ) (hh0 : ∀ x, 0 ≤ h x) (hh1 : ∀ x, h x ≤ 1),
    (∑' z, h z * (pushforward (g.comp f) μ).prob z)
      = (∑' z, h z * (pushforward g (pushforward f μ)).prob z) := by
    intro μ h hh0 hh1
    have h_left : ∑' z, h z * (pushforward (g.comp f) μ).prob z
      = ∑' x, h (g.f (f.f x)) * μ.prob x := by
      convert pushforward_integral (g.comp f) μ h hh0 hh1 using 1
    have h_right : ∑' z, h z * (pushforward g (pushforward f μ)).prob z
      = ∑' x, h (g.f (f.f x)) * μ.prob x := by
      rw [FiniteProb.pushforward_integral g (FiniteProb.pushforward f μ) h hh0 hh1
          , FiniteProb.pushforward_integral f μ (fun x => h (g.f x))
              (fun x => hh0 (g.f x)) (fun x => hh1 (g.f x))]
    rw [h_left, h_right]
  exact OFE.equiv_dist.mpr fun n x g a => h_eq x g

end FunctorLaws

section MonadLaws
variable {α : Type u} {β : Type u} {γ : Type u} [OFE α] [OFE β] [OFE γ]

open Classical in
theorem bindDist_dirac (f : α → FiniteProb β) (a : α) (n : Nat) :
    FiniteProb.bindDist f (FiniteProb.dirac a) ≡{n}≡ f a := by
  unfold bindDist
  unfold bind_prob; simp [dirac]

open Classical in
theorem bindDist_dirac_right (μ : FiniteProb α) (n : Nat) :
    FiniteProb.bindDist (FiniteProb.dirac) μ ≡{n}≡ μ := by
  intro g hg0 hg1
  unfold bindDist
  unfold bind_prob; simp only [dirac]
  intro hg2; congr; ext x; rw [tsum_eq_single x] <;> aesop

open Classical in
theorem dirac_dist_iff (a b : α) (n : Nat) :
    FiniteProb.dirac a ≡{n}≡ FiniteProb.dirac b ↔ a ≡{n}≡ b := by
  constructor
  · intro h
    by_contra h_contra
    convert h (fun x => if x ≡{n}≡ a then 1 else 0) ?_ ?_ ?_ <;> simp_all only [ite_mul,
      one_mul, zero_mul, false_iff]
    · simp only [dirac]
      rw [tsum_eq_single a, tsum_eq_single b] <;> simp_all only [OFE.Dist.rfl, ↓reduceIte,
        left_eq_ite_iff, one_ne_zero, imp_false, Decidable.not_not, ne_eq, ite_self, implies_true]
      exact fun h => h_contra <| h.symm
    · intro x y hxy; split_ifs
      · rfl
      · exact (‹¬y ≡{n}≡ a› (hxy.symm.trans ‹x ≡{n}≡ a›)).elim
      · exact (‹¬x ≡{n}≡ a› (hxy.trans ‹_›)).elim
      · rfl
    · exact fun x => by split_ifs <;> norm_num
    · exact fun x => by split_ifs <;> norm_num
  · exact fun a_1 => dirac_ne n a b a_1

end MonadLaws

section Convex
variable {α : Type u} [OFE α]

private theorem equiv_of_prob_eq (μ ν : FiniteProb α)
    (h : ∀ x, μ.prob x = ν.prob x) : μ ≡ ν := by
  intro n g hg hg0 hg1
  congr 1; ext x; rw [h x]

theorem convexComb_one (μ ν : FiniteProb α)
    (hp0 : (0 : ℝ) ≤ 1) (hp1 : (1 : ℝ) ≤ 1) :
    convexComb μ ν 1 hp0 hp1 ≡ μ := by
  apply equiv_of_prob_eq
  intro x; simp [convexComb]

theorem convexComb_zero (μ ν : FiniteProb α)
    (hp0 : (0 : ℝ) ≤ 0) (hp1 : (0 : ℝ) ≤ 1) :
    convexComb μ ν 0 hp0 hp1 ≡ ν := by
  apply equiv_of_prob_eq
  intro x; simp [convexComb]

theorem convexComb_idem (μ : FiniteProb α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexComb μ μ p hp0 hp1 ≡ μ := by
  apply equiv_of_prob_eq
  intro x; simp [convexComb]; ring

theorem convexComb_comm (μ ν : FiniteProb α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ 1 - p) (hq1 : 1 - p ≤ 1) :
    convexComb μ ν p hp0 hp1 ≡ convexComb ν μ (1 - p) hq0 hq1 := by
  apply equiv_of_prob_eq
  intro x; simp [convexComb]; ring

theorem convexComb_assoc (μ ν ρ : FiniteProb α)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpq : p * q < 1)
    (hpq0 : 0 ≤ p * q) (hpq1 : p * q ≤ 1)
    (hr0 : 0 ≤ (1 - p) * q / (1 - p * q)) (hr1 : (1 - p) * q / (1 - p * q) ≤ 1) :
    convexComb (convexComb μ ν p hp0 hp1) ρ q hq0 hq1 ≡
    convexComb μ (convexComb ν ρ ((1 - p) * q / (1 - p * q)) hr0 hr1) (p * q) hpq0 hpq1 := by
  apply equiv_of_prob_eq
  unfold FiniteProb.convexComb;
  grind

end Convex

section Affine

variable {α : Type u} {β : Type u} [OFE α] [OFE β]

open Classical in
theorem pushforward_convexComb (f : α -n> β) (μ ν : FiniteProb α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pushforward f (convexComb μ ν p hp0 hp1) ≡
    convexComb (pushforward f μ) (pushforward f ν) p hp0 hp1 := by
  refine FiniteProb.equiv_of_prob_eq _ _ ?_
  intro y
  simp only [pushforward, convexComb]
  convert (Summable.tsum_add (show Summable fun x =>
    p * (if f.f x = y then μ.prob x else 0) from ?_)
    (show Summable fun x => (1 - p) * (if f.f x = y then ν.prob x else 0) from ?_)) using 1
  · exact tsum_congr fun x => by split_ifs <;> ring
  · rw [tsum_mul_left, tsum_mul_left]
    rfl
  · exact Summable.mul_left _ (FiniteProb.summable_ite_prob μ (fun x => f.f x = y))
  · exact Summable.mul_left _ (FiniteProb.summable_ite_prob ν (fun x => f.f x = y))

theorem bindDist_convexComb (fn : α → FiniteProb β) (μ ν : FiniteProb α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bindDist fn (convexComb μ ν p hp0 hp1) ≡
    convexComb (bindDist fn μ) (bindDist fn ν) p hp0 hp1 := by
  refine equiv_of_prob_eq _ _ fun y => ?_
  nontriviality
  convert congr_arg (fun x : ℝ => x) (tsum_congr fun x => ?_) using 1
  rotate_left
  · exact fun x => p * μ.prob x * (fn x).prob y + (1 - p) * ν.prob x * (fn x).prob y
  · unfold FiniteProb.convexComb; ring
  · simp only [convexComb, bindDist]
    rw [Summable.tsum_add]
    · simp only [mul_assoc, tsum_mul_left]
      congr! 2
    · exact Summable.of_nonneg_of_le
        (fun x => mul_nonneg (mul_nonneg hp0 (μ.prob_in_unit x |>.1))
          ((fn x).prob_in_unit y |>.1))
        (fun x => mul_le_of_le_one_right (mul_nonneg hp0 (μ.prob_in_unit x |>.1))
          ((fn x).prob_in_unit y |>.2))
        ((μ.summable_prob).mul_left p);
    · have h_summable : Summable (fun x => ν.prob x * (fn x).prob y) := by
        exact Summable.of_nonneg_of_le
          (fun x => mul_nonneg (ν.prob_in_unit x |>.1)
            ((fn x).prob_in_unit y |>.1))
          (fun x => mul_le_of_le_one_right (ν.prob_in_unit x |>.1)
            ((fn x).prob_in_unit y |>.2))
          ν.summable_prob
      simpa only [mul_assoc] using h_summable.mul_left _

end Affine

end FiniteProb

namespace Prob

section Def
variable {α : Type u} [OFE α]

noncomputable def dirac (a : α) : Prob α :=
  Completion.unit.f (FiniteProb.dirac a)

instance dirac_ne : OFE.NonExpansive (dirac (α := α)) where
  ne {n x y} h := by
    simp only [dirac]
    apply Completion.unit.ne.ne
    exact FiniteProb.dirac_ne n x y h

noncomputable def map {β : Type u} [OFE β]
    (f : α -n> β) : Prob α -n> Prob β :=
  Completion.map (FiniteProb.map f)

open Classical in
private noncomputable def strength {β : Type u} [OFE β]
    (f : α -n> Prob β) : FiniteProb α -n> Completion (FiniteProb β) where
  f μ :=
    ⟨fun n => FiniteProb.bindDist (fun x => (f x).chain n) μ,
     fun {n i} hle => by
       change FiniteProb.bindDist (fun x => (f x).chain i) μ ≡{n}≡
            FiniteProb.bindDist (fun x => (f x).chain n) μ
       exact FiniteProb.bindDist_dist_n_gen
         (fun x => (f x).chain i) (fun x => (f x).chain n) n μ μ
         (fun x₁ x₂ hx12 => by
           have hf : (f.f x₁).chain n ≡{n}≡ (f.f x₂).chain n :=
             f.ne.ne hx12
           exact ((f.f x₁).cauchy hle).trans (hf.trans ((f.f x₂).cauchy hle).symm))
         (fun x => (f x).cauchy hle)
         (fun g _ _ _ => rfl)⟩
  ne := ⟨fun {n μ₁ μ₂} hμ => by
    change FiniteProb.bindDist (fun x => (f x).chain n) μ₁ ≡{n}≡
         FiniteProb.bindDist (fun x => (f x).chain n) μ₂
    exact FiniteProb.bindDist_dist_n_gen
      (fun x => (f x).chain n) (fun x => (f x).chain n) n μ₁ μ₂
      (fun x₁ x₂ hx12 => (f.ne.ne hx12 : (f.f x₁).chain n ≡{n}≡ (f.f x₂).chain n))
      (fun _ => OFE.Dist.rfl)
      hμ⟩

noncomputable def bind {β : Type u} [OFE β]
    (f : α -n> Prob β) : Prob α -n> Prob β :=
  (Completion.bind (α := FiniteProb α) (β := FiniteProb β)).f (strength f)

end Def

section FunctorLaws
variable {α : Type u} {β : Type u} {γ : Type u} [OFE α] [OFE β] [OFE γ]

theorem map_id_equiv :
    Prob.map (OFE.Hom.id : α -n> α) ≡ OFE.Hom.id := by
  have h_map_id_equiv : FiniteProb.map (OFE.Hom.id : α -n> α) ≡ OFE.Hom.id :=
    FiniteProb.map_id_equiv
  exact OFE.equiv_dist.mpr fun n x => h_map_id_equiv (x.chain n) n

theorem map_comp_equiv (g : β -n> γ) (f : α -n> β) :
    Prob.map (g.comp f) ≡ (Prob.map g).comp (Prob.map f) := by
  have := @FiniteProb.map_comp_equiv
  exact OFE.equiv_dist.mpr fun n x => this g f (x.chain n) n

theorem map_dirac (f : α -n> β) (a : α) :
    (Prob.map f).f (Prob.dirac a) ≡ Prob.dirac (f a) := by
  have h_map_dirac : FiniteProb.map f (FiniteProb.dirac a) ≡ FiniteProb.dirac (f.f a) := by
    unfold FiniteProb.map
    unfold FiniteProb.pushforward FiniteProb.dirac
    unfold FiniteProb.pushforward_prob; simp only
    congr! 1
    ext y; by_cases hy : y = f.f a <;> simp only [hy, ↓reduceIte]
    · rw [tsum_eq_single a] <;> aesop
    · rw [tsum_eq_single a] <;> aesop
  exact OFE.equiv_dist.mpr h_map_dirac

end FunctorLaws

section MonadLaws
variable {α : Type u} {β : Type u} {γ : Type u} [OFE α] [OFE β] [OFE γ]

noncomputable def diracHom : α -n> Prob α where
  f := Prob.dirac
  ne := Prob.dirac_ne

theorem bind_dirac (f : α -n> Prob β) (a : α) :
    (Prob.bind f).f (Prob.dirac a) ≡ f.f a := by
  exact fun n => FiniteProb.bindDist_dirac _ _ _

theorem bind_dirac_right :
    Prob.bind (Prob.diracHom : α -n> Prob α) ≡ OFE.Hom.id := by
  refine fun n x => ?_
  convert FiniteProb.bindDist_dirac_right _ _

theorem bind_bind (f : α -n> Prob β) (g : β -n> Prob γ) :
    (Prob.bind g).comp (Prob.bind f) ≡ Prob.bind ((Prob.bind g).comp f) := by
  by_contra h_contra
  have h_assoc : ∀ (μ : FiniteProb α), (bind g).f ((bind f).f (Completion.unit.f μ))
      ≡ (bind ((bind g).comp f)).f (Completion.unit.f μ) := by
    intro μ
    simp only [bind]
    unfold Completion.bind; simp only [strength, OFE.Hom.comp_apply]
    simp only [IsCOFE.compl, Chain.map]
    congr! 2
    unfold FiniteProb.bindDist; simp only [FiniteProb.mk.injEq]
    ext y; simp only [FiniteProb.bind_prob]
    simp only [← tsum_mul_right, ← tsum_mul_left]
    rw [← Summable.tsum_comm]
    · ring_nf
    · have h_summable : Summable (fun p : Σ (_ : β), α =>
        ((Completion.unit.f μ).chain ‹_›).prob p.2
          * ((f.f p.2).chain ‹_›).prob p.1 * ((g.f p.1).chain ‹_›).prob y) := by
        have h_summable : Summable (fun p : Σ (_ : β), α =>
          ((Completion.unit.f μ).chain ‹_›).prob p.2
          * ((f.f p.2).chain ‹_›).prob p.1) := by
          convert FiniteProb.bind_sigma_summable (fun x => ( f.f x ).chain ‹_›)
            ((Completion.unit.f μ).chain ‹_›) using 1
        refine .of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg ?_ ?_) ?_)
          (fun p => mul_le_of_le_one_right (mul_nonneg ?_ ?_) ?_) h_summable
        all_goals norm_num [FiniteProb.prob_in_unit]
      convert h_summable using 1
      constructor <;> intro h
        <;> rw [← Equiv.summable_iff (Equiv.sigmaEquivProd β α)] at * <;> aesop
  refine h_contra ?_
  refine fun n x y hxy => ?_
  rcases n with ⟨n⟩
  intro hy₀ hy₁; specialize h_assoc (n x); simp_all only [OFE.Hom.comp_apply]
  convert h_assoc x y hxy hy₀ hy₁ using 1

end MonadLaws

section Convex
variable {α : Type u} [OFE α]

noncomputable def convexComb (μ ν : Prob α) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Prob α where
  chain n := FiniteProb.convexComb (μ.chain n) (ν.chain n) p hp0 hp1
  cauchy {n i} hle := FiniteProb.convexComb_ne n
    (μ.chain i) (μ.chain n) (ν.chain i) (ν.chain n) p hp0 hp1
    (μ.cauchy hle) (ν.cauchy hle)

theorem convexComb_ne (n : Nat) (μ₁ μ₂ ν₁ ν₂ : Prob α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hμ : μ₁ ≡{n}≡ μ₂) (hν : ν₁ ≡{n}≡ ν₂) :
    (convexComb μ₁ ν₁ p hp0 hp1) ≡{n}≡ (convexComb μ₂ ν₂ p hp0 hp1) :=
  FiniteProb.convexComb_ne n _ _ _ _ p hp0 hp1 hμ hν

theorem convexComb_one (μ ν : Prob α)
    (hp0 : (0 : ℝ) ≤ 1) (hp1 : (1 : ℝ) ≤ 1) :
    convexComb μ ν 1 hp0 hp1 ≡ μ := fun n =>
  FiniteProb.convexComb_one _ _ hp0 hp1 n

theorem convexComb_zero (μ ν : Prob α)
    (hp0 : (0 : ℝ) ≤ 0) (hp1 : (0 : ℝ) ≤ 1) :
    convexComb μ ν 0 hp0 hp1 ≡ ν := fun n =>
  FiniteProb.convexComb_zero _ _ hp0 hp1 n

theorem convexComb_idem (μ : Prob α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    convexComb μ μ p hp0 hp1 ≡ μ := fun n =>
  FiniteProb.convexComb_idem _ p hp0 hp1 n

theorem convexComb_comm (μ ν : Prob α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ 1 - p) (hq1 : 1 - p ≤ 1) :
    convexComb μ ν p hp0 hp1 ≡ convexComb ν μ (1 - p) hq0 hq1 := fun n =>
  FiniteProb.convexComb_comm _ _ p hp0 hp1 hq0 hq1 n

theorem convexComb_assoc (μ ν ρ : Prob α)
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpq : p * q < 1)
    (hpq0 : 0 ≤ p * q) (hpq1 : p * q ≤ 1)
    (hr0 : 0 ≤ (1 - p) * q / (1 - p * q)) (hr1 : (1 - p) * q / (1 - p * q) ≤ 1) :
    convexComb (convexComb μ ν p hp0 hp1) ρ q hq0 hq1 ≡
    convexComb μ (convexComb ν ρ ((1 - p) * q / (1 - p * q)) hr0 hr1) (p * q) hpq0 hpq1 :=
  fun n => FiniteProb.convexComb_assoc _ _ _ p q hp0 hp1 hq0 hq1 hpq hpq0 hpq1 hr0 hr1 n

theorem map_convexComb {β : Type u} [OFE β] (f : α -n> β)
    (μ ν : Prob α) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Prob.map f).f (convexComb μ ν p hp0 hp1) ≡
    convexComb ((Prob.map f).f μ) ((Prob.map f).f ν) p hp0 hp1 := fun n =>
  FiniteProb.pushforward_convexComb f _ _ p hp0 hp1 n

theorem bind_convexComb {β : Type u} [OFE β] (f : α -n> Prob β)
    (μ ν : Prob α) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Prob.bind f).f (convexComb μ ν p hp0 hp1) ≡
    convexComb ((Prob.bind f).f μ) ((Prob.bind f).f ν) p hp0 hp1 := fun n =>
  FiniteProb.bindDist_convexComb (fun x => (f.f x).chain n) (μ.chain n) (ν.chain n) p hp0 hp1 n

end Convex

end Prob

namespace FiniteProb
variable {α : Type u} [OFE α]

noncomputable def eval (μ : FiniteProb α) (f : α → ℝ) : ℝ :=
  ∑' x, f x * μ.prob x

open Classical in
omit [OFE α] in
theorem eval_nonneg (μ : FiniteProb α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.eval f :=
  tsum_nonneg fun x => mul_nonneg (hf x) (μ.prob_in_unit x).1

open Classical in
theorem eval_le_one (μ : FiniteProb α) (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    μ.eval f ≤ 1 := by
  unfold eval
  calc ∑' x, f x * μ.prob x
      ≤ ∑' x, 1 * μ.prob x := by
        apply (summable_test_mul_prob μ f hf0 hf1).tsum_mono
          ((summable_prob μ).mul_left 1)
        intro x; exact mul_le_mul_of_nonneg_right (hf1 x) (μ.prob_in_unit x).1
    _ = 1 := by simp [μ.sum_one]

open Classical in
theorem eval_dirac (f : α → ℝ) (a : α) : (dirac a).eval f = f a := by
  unfold eval dirac; simp

open Classical in
theorem eval_dist_n (μ ν : FiniteProb α) (n : ℕ)
    (hd : μ ≡{n}≡ ν) (f : α → ℝ)
    (hf_ne : ∀ x y, x ≡{n}≡ y → f x = f y)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    μ.eval f = ν.eval f := by
  unfold eval; exact hd f hf_ne hf0 hf1

open Classical in
theorem eval_convexComb (μ ν : FiniteProb α) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (convexComb μ ν p hp0 hp1).eval f = p * μ.eval f + (1 - p) * ν.eval f := by
  unfold eval convexComb; simp only
  conv_lhs => arg 1; ext x; rw [show f x * (p * μ.prob x + (1 - p) * ν.prob x) =
    p * (f x * μ.prob x) + (1 - p) * (f x * ν.prob x) from by ring]
  rw [(summable_test_mul_prob μ f hf0 hf1 |>.mul_left p).tsum_add
      (summable_test_mul_prob ν f hf0 hf1 |>.mul_left (1 - p)),
    tsum_mul_left, tsum_mul_left]

end FiniteProb

namespace Prob
variable {α : Type u} [OFE α]

noncomputable def evalAt (μ : Prob α) (f : α → ℝ) (n : ℕ) : ℝ :=
  FiniteProb.eval (μ.chain n) f
open Classical in
theorem evalAt_stable (μ : Prob α) (f : α → ℝ) (n m : ℕ)
    (hf_ne : ∀ x y, x ≡{n}≡ y → f x = f y)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hn : n ≤ m) :
    μ.evalAt f m = μ.evalAt f n := by
  unfold evalAt
  exact FiniteProb.eval_dist_n _ _ n (μ.cauchy hn) f hf_ne hf0 hf1

noncomputable def eval (μ : Prob α) (f : α → ℝ)
    (_hf_ne : ∀ n, ∀ x y, x ≡{n}≡ y → f x = f y) : ℝ :=
  μ.evalAt f 0

theorem eval_def (μ : Prob α) (f : α → ℝ)
    (hf_ne : ∀ n, ∀ x y, x ≡{n}≡ y → f x = f y) :
    μ.eval f hf_ne = μ.evalAt f 0 := by rfl

open Classical in
theorem eval_eq_evalAt (μ : Prob α) (f : α → ℝ) (n : ℕ)
    (hf_ne : ∀ m, ∀ x y, x ≡{m}≡ y → f x = f y)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    μ.eval f hf_ne = μ.evalAt f n :=
  (evalAt_stable μ f 0 n (hf_ne 0) hf0 hf1 (Nat.zero_le n)).symm

theorem eval_convexComb (μ ν : Prob α)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : α → ℝ)
    (hf_ne : ∀ m, ∀ x y, x ≡{m}≡ y → f x = f y)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (convexComb μ ν p hp0 hp1).eval f hf_ne =
    p * μ.eval f hf_ne + (1 - p) * ν.eval f hf_ne := by
  simp only [eval, evalAt]
  exact FiniteProb.eval_convexComb _ _ p hp0 hp1 f hf0 hf1

end Prob

end Iris
