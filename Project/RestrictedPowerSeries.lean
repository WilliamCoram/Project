import Mathlib

variable (c : NNReal) (R : Type*) [NormedRing R]

open PowerSeries Filter Metric IsUltrametricDist NNReal
open scoped Topology

def Convergent (f : PowerSeries R) : Prop :=
  Tendsto (fun (i : ℕ) => (norm (coeff R i f)) * c^i) atTop (𝓝 0)

def CRestrictedPowerSeries : Set (PowerSeries R) :=
  {f | Convergent c R f}

----------------------------------------------------------------------------------------------------
namespace CRestrictedPowerSeries

def zero : (0 : PowerSeries R) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_zero, norm_zero,
  zero_mul, tendsto_const_nhds_iff]

def one : (1 : PowerSeries R) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, coeff_one]
  intro ε hε
  simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  use 1
  intro b hb
  have h : ‖((if b = 0 then 1 else 0) : R)‖ * c ^ b = 0 := by
    simp only [mul_eq_zero, norm_eq_zero, ite_eq_right_iff, pow_eq_zero_iff', ne_eq]
    left
    intro h
    contrapose h
    simp_rw [← ne_eq]
    exact Nat.not_eq_zero_of_lt hb
  simp only [h, sub_zero, norm_zero, mul_zero, zero_mul, sub_self]
  exact mem_of_mem_nhds hε

def add (f g : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R)
    (hg : g ∈ CRestrictedPowerSeries c R) : f + g ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_add]
  have h1 : ∀ (t : ℕ), 0 ≤ ‖(coeff R t) f + (coeff R t) g‖ * c ^ t := by
    intro t
    have : 0 ≤ c^t := by
      exact pow_nonneg c.2 t
    exact mul_nonneg (norm_nonneg _) this
  have h2 : ∀ (t : ℕ), ‖(coeff R t) f + (coeff R t) g‖ * c ^ t ≤ ‖coeff R t f‖ * c^t +
      ‖coeff R t g‖ * c^t := by
    intro t
    have := mul_le_mul_of_nonneg_right (norm_add_le (coeff R t f) (coeff R t g))
        (pow_nonneg c.2 t)
    rw [RightDistribClass.right_distrib] at this
    exact this
  have h3 : Tendsto (fun t ↦ ‖(coeff R t) f‖ * c ^ t + ‖(coeff R t) g‖ * c ^ t) atTop (𝓝 0) := by
    have := Tendsto.add hf hg
    simp only [add_zero] at this
    exact this
  exact squeeze_zero h1 h2 h3

def neg (f : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R) :
    (-f) ∈ CRestrictedPowerSeries c R:= by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_neg, norm_neg]
  exact hf

def addsubgroup : AddSubgroup (PowerSeries R) where
  carrier := CRestrictedPowerSeries c R
  zero_mem' := zero c R
  add_mem' := by
    intro f g hf hg
    exact add c R f g hf hg
  neg_mem' := by
    intro f hf
    exact neg c R f hf

noncomputable
instance IsAddSubgroup : AddGroup (CRestrictedPowerSeries c R) :=
    AddSubgroup.toAddGroup (addsubgroup c R)

----------------------------------------------------------------------------------------------------

variable [IsUltrametricDist R]

def bddabove (f : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R) :
    BddAbove {‖coeff R i f‖ * c^i | i : ℕ} := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq,
    NormedAddCommGroup.tendsto_atTop] at hf
  specialize hf 1
  simp only [zero_lt_one, sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, NNReal.abs_eq,
    forall_const, abs_norm] at hf
  obtain ⟨N, hf⟩ := hf
  simp_rw [@bddAbove_def]
  have h : (Finset.image (fun i => ‖coeff R i f‖ * c^i) (Finset.range (N+1))).Nonempty := by
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  use max 1 (Finset.max' (Finset.image (fun i => ‖coeff R i f‖ * c^i) (Finset.range (N+1))) h)
  simp only [Set.mem_setOf_eq, le_sup_iff, forall_exists_index, forall_apply_eq_imp_iff]
  intro a
  have h : a ≤ N ∨ a ≥ N := by exact Nat.le_total a N
  cases' h with h h
  · right
    apply Finset.le_max'
    simp only [Finset.mem_image, Finset.mem_range]
    use a
    constructor
    · exact Order.lt_add_one_iff.mpr h
    · rfl
  · left
    specialize hf a
    apply hf at h
    exact le_of_lt h


def h1 (f : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R) :
    ∃ A : ℝ, A > 0 ∧ ∀ i : ℕ, ‖coeff R i f‖ * c^i ≤ A := by
  have := bddabove c R f hf
  rw [@bddAbove_def] at this
  obtain ⟨x, h⟩ := this
  use x + 1
  constructor
  · have : x ≥ 0 := by
      have : ∀ y ∈ {x | ∃ i, ‖(coeff R i) f‖ * ↑c ^ i = x}, 0 ≤ y := by
        simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
        intro i
        exact (Left.mul_nonneg (norm_nonneg ((coeff R i) f)) (zero_le (c ^ i)))
      simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at h
      simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at this
      specialize h 0
      specialize this 0 -- I could specialize first instead of giving the general steps
      exact le_trans this h
    rw [← add_zero x] at this
    exact lt_of_le_of_lt this ((add_lt_add_iff_left x).mpr (zero_lt_one' ℝ))
  · simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at h
    have : x ≤ x + 1 := by
      nth_rw 1 [← add_zero x]
      exact (add_le_add_iff_left x).mpr (zero_le_one' ℝ)
    intro i
    specialize h i
    exact le_trans h this


----------------------------------------------------------------------------------------------------


--- Generalisations of the results from comm semi groups to now any ring

lemma Finset.Nonempty.norm_add_le_sup'_norm {t : Type*} {s : Finset t} (hs : s.Nonempty) (f : t → R)
    : ‖∑ i ∈ s, f i‖ ≤ s.sup' hs (‖f ·‖) := by
  simp only [Finset.le_sup'_iff]
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.sum_singleton, exists_eq_left, le_refl]
  | cons j t hj _ IH =>
      simp only [Finset.mem_cons, Finset.sum_cons, exists_eq_or_imp]
      refine (le_total ‖∑ i ∈ t, f i‖ ‖f j‖).imp ?_ ?_ <;> intro h
      · exact (norm_add_le_max _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (norm_add_le_max _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

/- These two do not seem to be needed. Should I push a big API update for this?
lemma Finset.nnnorm_add_le_sup_nnnorm {t : Type*} (s : Finset t) (f : t → R) :
    ‖∑ i ∈ s, f i‖₊ ≤ s.sup (‖f ·‖₊) := by
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp only [sum_empty, nnnorm_zero, sup_empty, bot_eq_zero', le_refl]
  · simpa only [← Finset.sup'_eq_sup hs, Finset.le_sup'_iff, coe_le_coe, coe_nnnorm']
      using hs.norm_add_le_sup'_norm f

lemma exists_norm_finset_add_le_of_nonempty {t : Type*} {s : Finset t} (hs : s.Nonempty) (f : t → R)
    : ∃ i : s, ‖∑ i ∈ s, f i‖ ≤ ‖f i‖ := by
  have h1 := hs.norm_add_le_sup'_norm f
  have h2 := s.exists_mem_eq_sup' hs (‖f ·‖)
  obtain ⟨i, h21, h22⟩ := h2
  simp only [Subtype.exists, exists_prop]
  use i
  constructor
  · exact h21
  · simp_rw [h22] at h1
    exact h1
  --- For some reason the copying of code does not work for this one!
  /-
  match s.exists_mem_eq_sup' hs (‖f ·‖) with
  | ⟨j, hj, hj'⟩ => ⟨j, hj, (hs.norm_add_le_sup'_norm f).trans (le_of_eq hj')⟩
  -/
  --- Also note the importance of this for the cNorm part! use ex0sts_mem_eq_sup'!!!!
-/

lemma exists_norm_finset_add_le {t : Type*} (s : Finset t) [Nonempty t] (f : t → R) :
    ∃ i : t, (s.Nonempty → i ∈ s) ∧ ‖∑ i ∈ s, f i‖ ≤ ‖f i‖ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.not_nonempty_empty, Finset.not_mem_empty, imp_self, Finset.sum_empty,
    norm_zero, norm_nonneg, and_self, exists_const]
  · exact exists_norm_finset_sum_le s f


def mul (f g : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R)
    (hg : g ∈ CRestrictedPowerSeries c R) : (f * g) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, @NormedAddCommGroup.tendsto_atTop,
    sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, NNReal.abs_eq, PowerSeries.coeff_mul]
  intro ε hε
  have fBound1 := h1 c R f hf
  have gBound1 := h1 c R g hg
  obtain ⟨a, ha, fBound1⟩ := fBound1
  obtain ⟨b, hb, gBound1⟩ := gBound1
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, @NormedAddCommGroup.tendsto_atTop,
    sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, NNReal.abs_eq] at hf hg
  specialize hf (ε/ (max a b))
  specialize hg (ε/ (max a b))
  have : 0 < ε / (max a b) := by
    have : 0 < max a b := by
      exact lt_sup_of_lt_left ha
    exact div_pos hε this
  have hf := hf this
  have hg := hg this
  obtain ⟨Nf, fBound2⟩ := hf
  obtain ⟨Ng, gBound2⟩ := hg
  use 2 * max Nf Ng
  intro n hn
  have ultrametric := exists_norm_finset_add_le R (Finset.antidiagonal n)
    (fun a => (coeff R a.1) f * (coeff R a.2) g)
  have Nonempty : (Finset.antidiagonal n).Nonempty := by
    use (0,n)
    simp only [Finset.mem_antidiagonal, zero_add]
  obtain ⟨i, hi, ultrametric⟩ := ultrametric
  apply hi at Nonempty
  have hcn : 0 ≤ c^n := by
      exact zero_le (c ^ n)
  have InterimBound1 : ‖∑ i ∈ Finset.antidiagonal n, (coeff R i.1) f * (coeff R i.2) g‖ * ↑c^n ≤
      ‖(coeff R i.1) f * (coeff R i.2) g‖ * ↑c^n := by
    exact mul_le_mul_of_nonneg_right ultrametric hcn
  have InterimBound2 : ‖(coeff R i.1) f * (coeff R i.2) g‖ * ↑c^n ≤
      ‖(coeff R i.1) f‖ * ‖(coeff R i.2) g‖ * ↑c^n := by
    have : ‖(coeff R i.1) f * (coeff R i.2) g‖ ≤ ‖(coeff R i.1) f‖ * ‖(coeff R i.2) g‖ := by
      exact NormedRing.norm_mul ((coeff R i.1) f) ((coeff R i.2) g)
    exact mul_le_mul_of_nonneg_right this hcn
  have : ‖(coeff R i.1) f‖ * ‖(coeff R i.2) g‖ * ↑c^n =
      ‖(coeff R i.1) f‖ * ↑c^i.1 * (‖(coeff R i.2) g‖ * ↑c^i.2) := by
    ring_nf
    simp only [Finset.mem_antidiagonal] at Nonempty
    simp_rw [mul_assoc, ← npow_add, Nonempty]
  rw [this] at InterimBound2
  have : i.1 ≥ max Nf Ng ∨ i.2 ≥ max Nf Ng := by
    simp only [Finset.mem_antidiagonal] at Nonempty
    rw [← Nonempty] at hn
    have : i.1 + i.2 ≤ 2 * max i.1 i.2 := by
      have := Nat.le_total i.1 i.2
      cases' this with h h
      · have := congrArg (HMul.hMul 2) (Nat.max_eq_right h)
        rw [this]
        rw [Nat.two_mul]
        exact Nat.add_le_add_right h i.2
      · have := congrArg (HMul.hMul 2) (Nat.max_eq_left h)
        simp_rw [this]
        rw [Nat.two_mul]
        exact Nat.add_le_add_left h i.1
    have := le_trans hn this
    simp only [Nat.ofNat_pos, mul_le_mul_left] at this
    exact le_sup_iff.mp this
  cases' this with this this
  · have : Nf ≤ i.1 := le_of_max_le_left this
    specialize fBound2 i.1
    apply fBound2 at this
    specialize gBound1 i.2
    have FinalBound1 : ‖(coeff R i.1) f‖ * ↑c ^ i.1 * (‖(coeff R i.2) g‖ * ↑c ^ i.2) < ε / (max a b) * b := by
      apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos this gBound1
        (Left.mul_nonneg (norm_nonneg ((coeff R i.1) f)) (zero_le (c ^ i.1))) hb
    have FinalBound2 : ε / (max a b) * b ≤ ε := by
      cases' (max_choice a b) with h h
      · rw [h]
        ring_nf
        rw [mul_assoc]
        nth_rw 2 [mul_comm]
        rw [← mul_assoc]
        exact (mul_inv_le_iff₀ ha).mpr ((mul_le_mul_iff_of_pos_left hε).mpr (sup_eq_left.mp h))
      · rw [h]
        ring_nf
        rw [mul_assoc]
        have := CommGroupWithZero.mul_inv_cancel b (ne_of_gt hb)
        simp_rw [this, mul_one, le_refl]
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans InterimBound1 InterimBound2) FinalBound1)
      FinalBound2
  · have := le_of_max_le_right this
    specialize gBound2 i.2
    apply gBound2 at this
    specialize fBound1 i.1
    have FinalBound1 : ‖(coeff R i.1) f‖ * ↑c ^ i.1 * (‖(coeff R i.2) g‖ * ↑c ^ i.2) < a * (ε / (max a b)) := by
      apply mul_lt_mul_of_le_of_lt_of_nonneg_of_pos fBound1 this
        (Left.mul_nonneg (norm_nonneg ((coeff R i.2) g)) (zero_le (c ^ i.2))) ha
    apply lt_of_lt_of_le (lt_of_le_of_lt (le_trans InterimBound1 InterimBound2) FinalBound1)
    cases' (max_choice a b) with h h
    · rw [h]
      ring_nf
      rw [mul_comm, ←mul_assoc]
      have := CommGroupWithZero.mul_inv_cancel a (ne_of_gt ha)
      rw [mul_comm] at this
      simp_rw [this]
      simp only [one_mul, le_refl]
    · rw [h]
      ring_nf
      rw [mul_assoc, mul_comm, mul_assoc]
      nth_rw 2 [mul_comm]
      rw [← mul_assoc]
      have h : max b a = b := by
        simp only [sup_eq_left]
        simp only [sup_eq_right] at h
        exact h
      exact (mul_inv_le_iff₀ hb).mpr ((mul_le_mul_iff_of_pos_left hε).mpr (sup_eq_left.mp h))

---- This can be cleaned up soooooooo much

def subring: Subring (PowerSeries R) where
  carrier := CRestrictedPowerSeries c R
  zero_mem' := zero c R
  add_mem' := by
    intro f g hf hg
    exact add c R f g hf hg
  neg_mem' := by
    intro f hf
    exact neg c R f hf
  one_mem' := one c R
  mul_mem' := by
    intro f g hf hg
    exact mul c R f g hf hg

noncomputable
instance IsRing  : Ring (CRestrictedPowerSeries c R) :=
    Subring.toRing (subring c R)
