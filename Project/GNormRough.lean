
import Mathlib

variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

section Generalising

open PowerSeries

noncomputable
def cnorm1 : (PowerSeries ℚ_[p])  → ℝ :=
  fun (f : PowerSeries ℚ_[p]) => sSup {padicNormE (coeff _ i f) * c^i | (i : ℕ)}


lemma cnorm1_existance (f : PowerSeries ℚ_[p]) : ∃ j : ℕ, sSup {padicNormE (coeff _ i f) * c^i | (i : ℕ)} =
    padicNormE (coeff _ j f) * c^j := by
  sorry



theorem cnorm1_nonneg (hc : 0 < c) : ∀ (x : PowerSeries ℚ_[p]), 0 ≤ cnorm1 c p x := by
  intro f
  rw [cnorm1]
  have := cnorm1_existance c p f
  obtain ⟨j, hj⟩ := this
  simp_rw [hj]
  have : ∀ (i : ℕ), 0 ≤ (padicNormE (coeff _ i f)) * c^i := by
    intro i
    apply mul_nonneg
    · simp only [Rat.cast_nonneg, apply_nonneg]
    · apply pow_nonneg
      exact le_of_lt hc

/- This isnt true anymore, but for the polynomials we want it will be -/
def myset1_bddabove (f : PowerSeries ℚ_[p]): BddAbove {padicNormE (coeff _ i f) * c^i | (i : ℕ)} := by
  sorry

theorem cnorm1_eq_zero (hc : 0 < c) : ∀ (x : PowerSeries ℚ_[p]), cnorm1 c p x = 0 ↔ x = 0 := by
  intro f
  rw [cnorm1]
  constructor
  · intro h1
    have start (a : ℝ) (ha : a ∈ {padicNormE (coeff _ i f) * c^i | (i : ℕ)}) :=
        le_csSup (myset1_bddabove c p f) ha
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at start
    have interim : ∀ i : ℕ, padicNormE (coeff _ i f) = 0 := by
      have hh : ∀ (i : ℕ), 0 ≤ (padicNormE (coeff _ i f)) * c ^ i := by
        intro i
        apply mul_nonneg
        · simp only [Rat.cast_nonneg]
          exact AbsoluteValue.nonneg padicNormE ((PowerSeries.coeff ℚ_[p] i) f)
        · apply pow_nonneg
          exact le_of_lt hc
      simp_rw [h1] at start
      have : ∀ (i : ℕ), ↑(padicNormE (coeff _ i f)) * c ^ i = 0 := by
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
    have final : ∀ i : ℕ, coeff _ i f = 0 := by
      intro i
      exact (AbsoluteValue.eq_zero padicNormE).mp (interim i)
    exact PowerSeries.ext final
  · have := cnorm1_existance c p f
    obtain ⟨j, hj⟩ := this
    simp_rw [hj]
    intro hf
    have : f = 0 → ∀ i, coeff _ i f = 0 := by
      intro hf i
      exact
        (AddSemiconjBy.eq_zero_iff ((PowerSeries.coeff ℚ_[p] i) 0)
              (congrFun
                (congrArg HAdd.hAdd (congrArg (⇑(PowerSeries.coeff ℚ_[p] i)) (id (Eq.symm hf))))
                ((PowerSeries.coeff ℚ_[p] i) 0))).mp
          rfl
    apply this at hf
    simp_rw [hf]
    simp only [AbsoluteValue.map_zero, Rat.cast_zero, zero_mul]

theorem cnorm1_nonarchimidean (hc : 0 < c) (p : ℕ) [hp : Fact (Nat.Prime p)]: ∀ (x y : PowerSeries ℚ_[p]),
    cnorm1 c p (x + y) ≤ max (cnorm1 c p x) (cnorm1 c p y) := by
  intro f g
  have := cnorm1_existance c p
  obtain ⟨fj, hfj⟩ := this f
  obtain ⟨gj, hgj⟩ := this g
  obtain ⟨l, hl⟩ := this (f + g)
  simp_rw [cnorm1]
  simp_rw [hfj, hgj, hl]
  have h' (q r : ℚ_[p]) : padicNormE (q + r) ≤ padicNormE q ⊔ padicNormE r := by
    exact padicNormE.nonarchimedean' q r
  have : ∀ (i : ℕ), padicNormE (coeff _ i f + coeff _ i g) ≤ padicNormE (coeff _ i f) ⊔
      padicNormE (coeff _ i g) := by
    intro i
    exact h' ((coeff ℚ_[p] i) f) ((coeff ℚ_[p] i) g)
  have := this l
  have hf (a : ℝ) (ha : a ∈ {x | ∃ i, ↑(padicNormE (coeff _ i f)) * c ^ i = x}) :=
    le_csSup (myset1_bddabove c p f) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hf
  have hg (a : ℝ) (ha : a ∈ {x | ∃ i, ↑(padicNormE (coeff _ i g)) * c ^ i = x}) :=
    le_csSup (myset1_bddabove c p g) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hg
  simp_rw [hfj] at hf
  simp_rw [hgj] at hg
  have : padicNormE (coeff _ l f + coeff _ l g) * c^l ≤
      padicNormE (coeff _ l f) * c^l ⊔ padicNormE (coeff _ l g) * c^l := by
    have hcc : c ≠ 0:= by
      exact Ne.symm (ne_of_lt hc)
    simp only [le_sup_iff, hc, pow_pos, mul_le_mul_right, Rat.cast_le]
    simp only [le_sup_iff] at this
    exact this
  simp only [map_add, le_sup_iff]
  have hf := hf l
  have hg := hg l
  simp only [le_sup_iff] at this
  cases this
  · left
    sorry -- just need to combine two inequalities now, but one is greyed out
  · right
    sorry

theorem cnorm1_add_leq (hc : 0 < c) : ∀ (x y : PowerSeries ℚ_[p]), cnorm1 c p (x + y) ≤ cnorm1 c p x + cnorm1 c p y
    := by
  have (x y : PowerSeries ℚ_[p]) : max (cnorm1 c p x) (cnorm1 c p y) ≤ cnorm1 c p x + cnorm1 c p y := by
    simp only [sup_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
    constructor
    · exact cnorm1_nonneg c p hc y
    · exact cnorm1_nonneg c p hc x
  have h := cnorm1_nonarchimidean c hc p
  exact fun x y ↦
    Preorder.le_trans (cnorm1 c p (x + y)) (cnorm1 c p x ⊔ cnorm1 c p y) (cnorm1 c p x + cnorm1 c p y)
      (h x y) (this x y)

theorem cnorm1_mul : ∀ (x y : PowerSeries ℚ_[p]), cnorm1 c p (x * y) = cnorm1 c p x * cnorm1 c p y := by
  sorry

noncomputable
def cnorm_AbsVal (hc : 0 < c) : AbsoluteValue (PowerSeries ℚ_[p]) ℝ where
  toFun := cnorm1 c p
  map_mul' := cnorm1_mul c p
  nonneg' := cnorm1_nonneg c p hc
  eq_zero' := cnorm1_eq_zero c p hc
  add_le' := cnorm1_add_leq c p hc

end Generalising
