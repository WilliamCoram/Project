import Mathlib

section NonArchAbsValue

open Polynomial

variable (c : ℝ) (p : ℕ)

noncomputable
def cnorm : ℚ[X] → ℝ :=
  fun f => sSup {padicNorm p (coeff f i) * c^i | (i : ℕ) }

def cnorm_existance : ∃ j : ℕ, sSup {padicNorm p (coeff f i) * c^i | (i : ℕ)} =
    padicNorm p (coeff f j) * c^j := by

  sorry

theorem cnorm_mul : ∀ (x y : ℚ[X]), cnorm c p (x * y) = cnorm c p x * cnorm c p y := by
  sorry

theorem cnorm_nonneg (hc : c > 0) : ∀ (x : ℚ[X]), 0 ≤ cnorm c p x := by
  intro f
  rw [cnorm]
  have : ∀ (i : ℕ), 0 ≤ (padicNorm p (coeff f i)) * c ^ i := by
      intro i
      apply mul_nonneg
      · simp only [Rat.cast_nonneg]
        exact padicNorm.nonneg (f.coeff i)
      · apply pow_nonneg
        exact le_of_lt hc
  apply Real.sSup_nonneg'
  simp only [Set.mem_setOf_eq, exists_exists_eq_and]
  exact Exists.intro p (this p)


theorem cnorm_eq_zero (hc : 0 < c) : ∀ (x : ℚ[X]), cnorm c p x = 0 ↔ x = 0 := by
  intro f
  constructor
  · rw [cnorm]
    have : ∀ (i : ℕ), 0 ≤ (padicNorm p (coeff f i)) * c ^ i := by
      intro i
      apply mul_nonneg
      · simp only [Rat.cast_nonneg]
        exact padicNorm.nonneg (f.coeff i)
      · apply pow_nonneg
        exact le_of_lt hc
    intro h
    have h1 : ∀ i : ℕ, ↑(padicNorm p (f.coeff i)) * c ^ i ≤ 0 := by
      have (u : {x | ∃ i, ↑(padicNorm p (f.coeff i)) * c ^ i = x}) : u ≤
          sSup {x | ∃ i, ↑(padicNorm p (f.coeff i)) * c ^ i = x} := by

        sorry
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall, forall_exists_index,
        forall_apply_eq_imp_iff] at this
      rw [h] at this
      exact this
    have h2 : ∀ i : ℕ, ↑(padicNorm p (f.coeff i)) * c ^ i = 0 := by
      intro i
      apply LE.le.eq_of_not_gt
      · exact this i
      · simp only [not_lt]
        exact h1 i
    have : c ≠ 0 := by
      exact Ne.symm (ne_of_lt hc)
    simp only [mul_eq_zero, Rat.cast_eq_zero, pow_eq_zero_iff', ne_eq] at h2
    simp only [this, false_and, or_false] at h2
    have : ∀ i : ℕ, f.coeff i = 0 := by

      sorry
    rw [← leadingCoeff_eq_zero, leadingCoeff]
    use this f.natDegree
  · intro hf
    have : f = 0 → ∀ i, coeff f i = 0 := by
      exact fun a i ↦
        Mathlib.Tactic.ComputeDegree.coeff_congr (congrFun (congrArg coeff hf) i) rfl rfl
    apply this at hf
    simp_rw [cnorm]
    simp_rw [hf]
    simp only [padicNorm.zero, Rat.cast_zero, zero_mul, exists_const, Set.setOf_eq_eq_singleton',
      csSup_singleton]

/-- cnorm is nonarchimidean-/
theorem cnorm_nonarchimidean (hc : 0 < c) (p : ℕ) [hp : Fact (Nat.Prime p)]: ∀ (x y : ℚ[X]),
    cnorm c p (x + y) ≤ max (cnorm c p x) (cnorm c p y) := by
  intro f g
  rw [cnorm]
  have h (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q ⊔ padicNorm p r := by
    exact padicNorm.nonarchimedean
  simp only [coeff_add, le_sup_iff]
  simp_rw [cnorm]
  have h1 : ∀ (i : ℕ), padicNorm p (f.coeff i + g.coeff i) ≤ padicNorm p (f.coeff i) ⊔
      padicNorm p (g.coeff i) := by
    intro i
    exact h (f.coeff i) (g.coeff i)
  have h2 : ∀ i : ℕ, padicNorm p (f.coeff i + g.coeff i) * c^i ≤ padicNorm p (f.coeff i) * c^i ⊔
      padicNorm p (g.coeff i) * c^i := by
    sorry
  sorry


theorem cnorm_add_leq (hc : 0 < c) : ∀ (x y : ℚ[X]), cnorm c p (x + y) ≤ cnorm c p x + cnorm c p y
    := by
  have (x y : ℚ[X]) : max (cnorm c p x) (cnorm c p y) ≤ cnorm c p x + cnorm c p y := by
    simp only [sup_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
    constructor
    · exact cnorm_nonneg c p hc y
    · exact cnorm_nonneg c p hc x
  have h := cnorm_nonarchimidean c hc p
  exact fun x y ↦
    Preorder.le_trans (cnorm c p (x + y)) (cnorm c p x ⊔ cnorm c p y) (cnorm c p x + cnorm c p y)
      (h x y) (this x y)

/-- cnorm is an absolute value-/
noncomputable
def cnorm_AbsVal (hc : c > 0) : AbsoluteValue ℚ[X] ℝ where
  toFun := cnorm c p
  map_mul' := cnorm_mul c p
  nonneg' := cnorm_nonneg c p hc
  eq_zero' := cnorm_eq_zero c p hc
  add_le' := cnorm_add_leq c p hc

/-- cnorm induces the p-adic norm on the degree zero polynomials -/
theorem cnorm_induces_padicNorm (x : ℚ[X]) (hx : degree x = 0): cnorm c p x = padicNorm p (coeff x 0) := by
  sorry

/-- Given a polynomial `f` in `K[X]` and a valid `N` then there exists `g,h` in `K[X]` such that
`f = g h` with some given properties.-/
theorem WeierstrassPrepThm_polynomials (hc : c > 0) (f : ℚ[X]) (hf : degree f = (n : ℕ))
    (hN : ∃ N : ℕ, (0 < N ∧ N < n) ∧ (cnorm c p f = padicNorm p (coeff f N) * c^N) ∧
    (∀ j > N, cnorm c p f > padicNorm p (coeff f j) * c^j)) : ∃ g h : ℚ[X], (degree g = (N : ℕ)) ∧
    (degree h = n - N) ∧ (f = g * h) ∧ (cnorm c p f = cnorm c p g) ∧ (cnorm c p (h - (1 : ℚ[X])) < 1) := by
      sorry
