import Mathlib

section NonArchAbsValue

open Polynomial

variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable
def cnorm : ℚ[X] → ℝ :=
  fun f => sSup {padicNorm p (coeff f i) * c^i | (i : ℕ) }

lemma cnorm_existance (f : ℚ[X]) : ∃ j : ℕ, sSup {padicNorm p (coeff f i) * c^i | (i : ℕ)} =
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

def myset_bddabove (f : ℚ[X]): BddAbove {x | ∃ i, ↑(padicNorm p (f.coeff i)) * c ^ i = x} := by
  sorry

theorem cnorm_eq_zero (hc : 0 < c) : ∀ (x : ℚ[X]), cnorm c p x = 0 ↔ x = 0 := by
  intro f
  rw [cnorm]
  constructor
  · intro h1
    have start (a : ℝ) (ha : a ∈ {x | ∃ i, ↑(padicNorm p (f.coeff i)) * c ^ i = x}) :=
        le_csSup (myset_bddabove c p f) ha
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at start
    have interim : ∀ i : ℕ, padicNorm p (f.coeff i) = 0 := by
      have hh : ∀ (i : ℕ), 0 ≤ (padicNorm p (coeff f i)) * c ^ i := by
        intro i
        apply mul_nonneg
        · simp only [Rat.cast_nonneg]
          exact padicNorm.nonneg (f.coeff i)
        · apply pow_nonneg
          exact le_of_lt hc
      simp_rw [h1] at start
      have : ∀ (i : ℕ), ↑(padicNorm p (f.coeff i)) * c ^ i = 0 := by
        intro i
        apply LE.le.eq_of_not_gt
        · exact hh i
        · simp only [not_lt]
          exact start i
      have hcc : c ≠ 0 := by
        exact Ne.symm (ne_of_lt hc)
      simp only [mul_eq_zero, Rat.cast_eq_zero, pow_eq_zero_iff', hcc, ne_eq, false_and,
        or_false] at this
      exact this
    have final : ∀ i : ℕ, f.coeff i = 0 := by
      intro i
      apply padicNorm.zero_of_padicNorm_eq_zero (interim i)
    exact leadingCoeff_eq_zero.mp (final f.natDegree)
  · have := cnorm_existance c p f
    obtain ⟨j, hj⟩ := this
    simp_rw [hj]
    intro hf
    have : f = 0 → ∀ i, coeff f i = 0 := by
      exact fun a i ↦
        Mathlib.Tactic.ComputeDegree.coeff_congr (congrFun (congrArg coeff hf) i) rfl rfl
    apply this at hf
    simp_rw [hf, padicNorm.zero, Rat.cast_zero, zero_mul]

/-- cnorm is nonarchimidean-/
theorem cnorm_nonarchimidean (hc : 0 < c) (p : ℕ) [hp : Fact (Nat.Prime p)]: ∀ (x y : ℚ[X]),
    cnorm c p (x + y) ≤ max (cnorm c p x) (cnorm c p y) := by
  intro f g
  have := cnorm_existance c p
  obtain ⟨fj, hfj⟩ := this f
  obtain ⟨gj, hgj⟩ := this g
  obtain ⟨l, hl⟩ := this (f + g)
  simp_rw [cnorm]
  simp_rw [hfj, hgj, hl]
  have h' (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q ⊔ padicNorm p r := by
    exact padicNorm.nonarchimedean
  have : ∀ (i : ℕ), padicNorm p (f.coeff i + g.coeff i) ≤ padicNorm p (f.coeff i) ⊔
      padicNorm p (g.coeff i) := by
    intro i
    exact h' (f.coeff i) (g.coeff i)
  have := this l
  have hf (a : ℝ) (ha : a ∈ {x | ∃ i, ↑(padicNorm p (f.coeff i)) * c ^ i = x}) :=
    le_csSup (myset_bddabove c p f) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hf
  have hg (a : ℝ) (ha : a ∈ {x | ∃ i, ↑(padicNorm p (g.coeff i)) * c ^ i = x}) :=
    le_csSup (myset_bddabove c p g) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hg
  simp_rw [hfj] at hf
  simp_rw [hgj] at hg
  have : padicNorm p (f.coeff l + g.coeff l) * c^l ≤
      padicNorm p (f.coeff l) * c^l ⊔ padicNorm p (g.coeff l) * c^l := by
    have hcc : c ≠ 0:= by
      exact Ne.symm (ne_of_lt hc)
    simp only [le_sup_iff, hc, pow_pos, mul_le_mul_right, Rat.cast_le]
    simp only [le_sup_iff] at this
    exact this
  simp only [coeff_add]
  have hf := hf l
  have hg := hg l
  simp only [le_sup_iff] at this
  simp only [le_sup_iff]
  cases this
  · left
    sorry
  · right
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



----------------------------------------------------------------------------------------------------
