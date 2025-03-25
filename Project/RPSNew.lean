import Mathlib

variable (c : NNReal) (R : Type*) [NormedRing R]

open PowerSeries Filter
open scoped Topology

def Convergent (f : PowerSeries R) : Prop :=
  Tendsto (fun (i : ℕ) => (norm (coeff R i f)) * c^i) atTop (𝓝 0)

def CRestrictedPowerSeries : Set (PowerSeries R) :=
  {f | Convergent c R f }

lemma C2 : ∀ (f : PowerSeries R), Tendsto (fun i => ∑ j ∈ Finset.range i, coeff R j f * x^j) atTop (𝓝 0) := by
  intro f
  sorry


namespace CRestrictedPowerSeries

def zero : 0 ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_zero, norm_zero,
  zero_mul, tendsto_const_nhds_iff]

def one : 1 ∈ CRestrictedPowerSeries c R := by
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
    (-f) ∈ CRestrictedPowerSeries c R := by
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

-- Multiplication relies on absolute convergence of the sum of the coefficients of one of the series
-- We can guarentee this is the case of an ultrametric norm

variable [IsUltrametricDist R]



-- Thm 3.50 from Principles of Mathematical analysis
lemma ConvergenceOfProdOfSeq (a b c f g : ℕ → ℝ) (hf : f = fun i => ∑ j ∈ Finset.range i, a j)
    (hg : g = fun i => ∑ j ∈ Finset.range i, b j) (hff : Tendsto f atTop (𝓝 A))
    (hfff : Tendsto (fun i => ∑ j ∈ Finset.range i, ‖a j‖) atTop (𝓝 α))
    (hgg : Tendsto g atTop (𝓝 B)) (hc : c = fun i => ∑p ∈ Finset.antidiagonal i, a p.1 * b p.2) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, c i) atTop (𝓝 (A * B)) := by
  have := Tendsto.mul hff hgg
  let e := fun i => g i - B
  let h := fun i => ∑ j ∈ Finset.range i, c j
  have Step1 (n : ℕ) : h n = f n * B + ∑ j ∈ Finset.range n, a j * e (n - j) := by
    simp_rw [h, hf, e, hg, hc]
    have : ∑ x ∈ Finset.range n, a x * (∑ j ∈ Finset.range (n - x), b j - B) =
        ∑ x ∈ Finset.range n, a x * ∑ j ∈ Finset.range (n - x), b j - ∑ x ∈ Finset.range n, a x * B := by
      ring_nf
      simp only [Finset.sum_sub_distrib, h, e]
    rw [this, add_comm]
    have : ∑ x ∈ Finset.range n, a x * B = (∑ j ∈ Finset.range n, a j) * B := by
      rw [Finset.sum_mul]
    rw [this]
    simp only [sub_add_cancel]
    -- Have shown this is true on paper; not sure how to formalise it

    sorry
  let γ := fun i => ∑ j ∈ Finset.range i, (a j * (e (i - j)))
  have Step2 : Tendsto γ atTop (𝓝 0) := by
    -- follow notes
    have : Tendsto e atTop (𝓝 0) := by
      simp_rw [e]
      have := Tendsto.add_const (-B) hgg
      simp only [add_neg_cancel, h, e] at this
      exact this
    apply NormedAddCommGroup.tendsto_nhds_zero.mp at this

    -- need to show some inequality for γn; then show the limsup of γ is ≤ ε
    -- not sure how to do these ε proofs right now
    sorry
  have Step3 : Tendsto (fun i => f i * B) atTop (𝓝 (A * B)) := by
    exact Tendsto.mul_const B hff
  have Step4 (i : ℕ) : h i = f i * B + γ i := by
    simp_rw [Step1, γ]
  have Step5 : Tendsto (fun i => f i * B + γ i) atTop (𝓝 (A * B)) := by
    have := Tendsto.add Step3 Step2
    simp only [add_zero] at this
    exact this
  -- just need to rewrite with h, Step4 and exact Step5
  sorry

lemma help : f ∈ CRestrictedPowerSeries c R →
    Tendsto (fun i => ∑ j ∈ Finset.range i, ‖coeff R j f‖ * c^j) atTop (𝓝 0) := by
  intro hf
  -- this is true via non-archimedean property of the norm
  -- Note we need to change 0 to the maximum of ‖coeff R j f‖ * c^j; which exists by definition of
  -- CRestrictedPowerSeries (see CNorm file for existence of limit)
  sorry

lemma PartialSumConvergent_implies_ZeroSeq (a : ℕ → ℝ) :
    Tendsto (fun i => ∑ j ∈ Finset.range i, a j) atTop (𝓝 n) →
    Tendsto (fun i => a i) atTop (𝓝 0) := by
  intro h
  -- true by definition of limit of partial sums (I think?)

  sorry








def mul (f g : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R)
    (hg : g ∈ CRestrictedPowerSeries c R) : (f * g) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, PowerSeries.coeff_mul]


  /-
  have hc := fun i ↦ pow_nonneg c.2 i
  have h1 : ∀  i : ℕ, 0 ≤ ‖∑ p ∈ Finset.antidiagonal i, (coeff R p.1) f * (coeff R p.2) g‖
      * c^i := by
    intro i
    exact mul_nonneg (norm_nonneg _) (hc i)
  have h2 : ∀ i : ℕ, ‖∑ p ∈ Finset.antidiagonal i, (coeff R p.1) f * (coeff R p.2) g‖ * c^i ≤
      (∑ p ∈ Finset.antidiagonal i, ‖coeff R p.1 f‖ * ‖coeff R p.2 g‖) * c^i := by
    have : ∀ i : ℕ, ‖∑ p ∈ Finset.antidiagonal i, (coeff R p.1) f * (coeff R p.2) g‖ ≤
        ∑ p ∈ Finset.antidiagonal i, ‖coeff R p.1 f‖ * ‖coeff R p.2 g‖ := by
      have h21 :=
          fun i ↦ norm_sum_le (Finset.antidiagonal i) fun i ↦ (coeff R i.1) f * (coeff R i.2) g
      have h22 : ∀ i : ℕ, ∑ p ∈ Finset.antidiagonal i, ‖coeff R p.1 f * coeff R p.2 g‖ ≤
         ∑ p ∈ Finset.antidiagonal i, ‖coeff R p.1 f‖ * ‖coeff R p.2 g‖ := by
        intro i
        refine Finset.sum_le_sum ?_
        simp only [Finset.mem_antidiagonal, Prod.forall]
        intro a b hab
        exact NormedRing.norm_mul ((coeff R a) f) ((coeff R b) g)
      exact fun i ↦
        Preorder.le_trans ‖∑ p ∈ Finset.antidiagonal i, (coeff R p.1) f * (coeff R p.2) g‖
        (∑ p ∈ Finset.antidiagonal i, ‖(coeff R p.1) f * (coeff R p.2) g‖)
        (∑ p ∈ Finset.antidiagonal i, ‖(coeff R p.1) f‖ * ‖(coeff R p.2) g‖) (h21 i) (h22 i)
    intro i
    exact mul_le_mul_of_nonneg_right (this i) (hc i)
  have h3 : Tendsto (fun i ↦ (∑ p ∈ Finset.antidiagonal i, ‖coeff R p.1 f‖ * ‖coeff R p.2 g‖)
      * c ^ i) atTop (𝓝 0) := by

    /-
    have : ∀ i : ℕ, (∑ p ∈ Finset.antidiagonal i, ‖(coeff R p.1) f‖ * ‖(coeff R p.2) g‖) * c ^ i =
        ∑ p ∈ Finset.antidiagonal i, (‖coeff R p.1 f‖ * c^p.1) * (‖coeff R p.2 g‖ * c^p.2) := by
      intro i
      rw [Finset.sum_mul (Finset.antidiagonal i) (fun i ↦ ‖(coeff R i.1) f‖ * ‖(coeff R i.2) g‖)
        (c ^ i)]
      simp_rw [← mul_assoc, mul_comm, ← mul_assoc]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_antidiagonal] at hx
      ring_nf
      have : (c^i : ℝ) = c^x.2 * c^x.1 := by
        rw [add_comm] at hx
        rw [← pow_add, hx]
      rw [this]
    simp_rw [this]
    have := ConvergenceOfProdOfSeq (fun i => ‖coeff R i f‖ * c^i) (fun i => ‖coeff R i g‖ * c^i)
        (fun i => ∑ p ∈ Finset.antidiagonal i, ‖coeff R p.1 f‖ * c^p.1 * (‖coeff R p.2 g‖ * c^p.2))
        (fun i => ∑ j ∈ Finset.range i, ‖coeff R j f‖ * c^j)
        (fun i => ∑ j ∈ Finset.range i, ‖coeff R j g‖ * c^j)
        rfl rfl (help c R hf) sorry (help c R hg) rfl
    apply PartialSumConvergent_implies_ZeroSeq at this
    exact this
    -/

    sorry
  exact squeeze_zero h1 h2 h3
  -/

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

end CRestrictedPowerSeries
