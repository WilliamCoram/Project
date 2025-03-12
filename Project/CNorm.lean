import Mathlib
import Project.RPSNew

variable (c : NNReal) (R : Type*) [NormedRing R]

open PowerSeries Filter CRestrictedPowerSeries
open scoped Topology

noncomputable
def cNorm : PowerSeries R → ℝ :=
  fun f => sSup {‖coeff R i f‖ * c^i | (i : ℕ)}

namespace cNorm

noncomputable
def CRestricted : CRestrictedPowerSeries c R → ℝ :=
  fun f => cNorm c R f

def bddabove (f : CRestrictedPowerSeries c R) :
    BddAbove {‖coeff R i f‖ * c^i | (i : ℕ)} := by
  -- follows from convergence property
  sorry

lemma existance (f : CRestrictedPowerSeries c R) :
    ∃ (j : ℕ), sSup {‖coeff R i f‖ * c^i | (i : ℕ)} = ‖coeff R j f‖ * c^j := by
  -- follows from convergence property, then reducing to finite set including the maximum
  sorry


-- If c = 0, this becomes helpful
lemma existance_zero (f : CRestrictedPowerSeries c R) (hc : c = 0) :
  sSup {‖coeff R i f‖ * c^i | (i : ℕ)} = ‖coeff R 0 f‖ * c^0 := by
  simp_rw [hc, pow_zero, mul_one]
  -- true trivially (since all terms are 0, except for the 0th term)

  sorry


lemma zero : CRestricted c R 0 = 0 := by
  have := existance c R 0
  obtain ⟨j, hj⟩ := this
  simp_rw [CRestricted, cNorm, hj]
  simp only [mul_eq_zero, norm_eq_zero, pow_eq_zero_iff', NNReal.coe_eq_zero, ne_eq]
  left
  rfl

lemma le_sSup (f : CRestrictedPowerSeries c R) : ∀ i : ℕ,
    ‖coeff R i f‖ * c^i ≤ sSup {‖coeff R i f‖ * c^i | (i : ℕ)} := by
  have (a : ℝ) (ha : a ∈ {‖coeff R i f‖ * c^i | (i : ℕ)}) : a ≤ sSup {‖coeff R i f‖ * c^i | (i : ℕ)}
      := le_csSup (bddabove c R f) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at this
  exact fun i ↦ this i

lemma nonneg : ∀ f : CRestrictedPowerSeries c R, 0 ≤ CRestricted c R f := by
  intro f
  have := existance c R f
  obtain ⟨j, hj⟩ := this
  simp_rw [CRestricted, cNorm, hj]
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (NNReal.coe_nonneg c) j)

/- -- This is needed for RingNorm; and note this requires that c ≠ 0, else it does not hold
lemma eq_zero_of_map_eq_zero : ∀ f : CRestrictedPowerSeries c R, CRestricted c R f = 0 → f = 0 := by
  intro f zero
  have : ∀ i : ℕ, ‖coeff R i f‖ * c^i = 0 := by
    intro i
    have h1 := le_sSup c R f i
    rw [CRestricted, cNorm] at zero
    rw [zero] at h1
    have h2 : 0 ≤ ‖coeff R i f‖ * c^i := mul_nonneg (norm_nonneg _)
        (pow_nonneg (NNReal.coe_nonneg c) i)
    exact le_antisymm h1 h2
  ext i
  have := this i
  have : coeff R i = 0 := by

  -- this
  sorry
-/

/-
-- Need to specify Non-Archimedean property of the norm here
lemma nonArchimedean : ∀ f g : CRestrictedPowerSeries c R,
    CRestricted c R (f + g) ≤ CRestricted c R f + CRestricted c R g := by
  intros f g
  have hf := existance c R f
  have hg := existance c R g
  have hl := existance c R (f + g)
  obtain ⟨j, hj⟩ := hf
  obtain ⟨k, hk⟩ := hg
  obtain ⟨l, hl⟩ := hl
  simp_rw [CRestricted, cNorm, hj, hk, hl]
  have : ‖coeff _ l f.1 + coeff _ l g.1‖ * c^l ≤ ‖coeff _ l f.1‖ * c^l ⊔ ‖coeff _ l g.1‖ * c^l := by
    -- want to do cases of c
    by_cases h : c = 0
    · by_cases h1 : l = 0
      · simp_rw [h1, h, pow_zero, mul_one]
        -- follows from Non-Archimedean property of the norm
        sorry
      ·
        sorry
    ·
     sorry
  sorry
-/

lemma add_le : ∀ f g : CRestrictedPowerSeries c R,
  CRestricted c R (f + g) ≤ CRestricted c R f + CRestricted c R g := by
  intro f g
  simp_rw [CRestricted, cNorm]
  have h1 : sSup {x | ∃ (i : ℕ), ‖(coeff R i) ↑(f + g)‖ * ↑c^i = x} ≤
      sSup {x | ∃ (i : ℕ), (‖(coeff R i) ↑f‖ + ‖(coeff R i) ↑g‖) * ↑c^i = x} := by
    -- follows from norm_add_le

    sorry
  have h2 : sSup {x | ∃ (i : ℕ), (‖(coeff R i) ↑f‖ + ‖(coeff R i) ↑g‖) * ↑c^i = x} ≤
      sSup {x | ∃ (i : ℕ), ‖(coeff R i) ↑f‖ * ↑c^i = x} +
      sSup {x | ∃ (i : ℕ), ‖(coeff R i) ↑g‖ * ↑c^i = x} := by
    -- follows from maximising both parts in an additive way
    sorry
  exact le_trans h1 h2

lemma neg : ∀ f : CRestrictedPowerSeries c R, CRestricted c R (-f) = CRestricted c R f := by
  intro f
  have := existance c R f
  obtain ⟨j, hj⟩ := this
  simp_rw [CRestricted, cNorm, hj]
  have : sSup {x | ∃ i, ‖(coeff R i) ↑(-f)‖ * ↑c ^ i = x} = sSup {x | ∃ i, ‖(coeff R i) ↑f‖ * ↑c ^ i = x} := by
    refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
    intro x h
    simp_rw [Set.mem_setOf_eq]
    use x
    constructor
    · obtain ⟨i, hi⟩ := h
      use i
      have : ‖coeff R i (-f)‖ * c^i = ‖coeff R i f‖ * c^i := by
        have : coeff R i (-f) = -coeff R i f := by
          rfl
        simp_rw [this, norm_neg]
      rw [←this]
      exact hi
    · rfl
  rw [this]
  exact hj

end cNorm

noncomputable
instance : RingSeminorm (CRestrictedPowerSeries c R) where
  toFun := cNorm.CRestricted c R
  map_zero' := cNorm.zero c R
  add_le' := cNorm.add_le c R
  mul_le' := sorry
  neg' := cNorm.neg c R






------ We can also show it is a non-Archimedean absolute value on the field of rational functions
