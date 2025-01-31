
import Mathlib

variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

section Generalising

open PowerSeries

noncomputable
def cnorm1 : (PowerSeries ℚ_[p])  → ℝ :=
  fun (f : PowerSeries ℚ_[p]) => sSup {padicNormE (coeff _ i f) * c^i | (i : ℕ)}


lemma cnorm1_existance (f : PowerSeries ℚ_[p]) : ∃ j : ℕ, sSup {padicNormE (coeff _ i f) * c^i | (i : ℕ)} =
    padicNormE (coeff _ j f) * c^j := by
    -- true in the case of restricted powerseries. For this consider the first coefficient.
    -- Then there exists some N such that all the points after that have a smaller padicNormE * c^i
    -- So we can restrict to sSup of a finite set; which is a maximum.
    -- Which gives the existance
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
  -- As aobve in cnorm1_existance; by definition of restricted powerseries it is bdd_above.
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

lemma ineq1 (f g : PowerSeries ℚ_[p]) (hc : 0 < c) : ∀ (k : ℕ), padicNormE ((coeff ℚ_[p] k) (f * g)) * c^k ≤ sSup
    {x : ℝ | ∃ (i j : ℕ), i + j = k ∧
    ((padicNormE (coeff _ i f)) * (padicNormE (coeff _ j g)) * c^k = x)} := by
    intro k
    have : (coeff ℚ_[p] k) (f * g) = ∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p] p_1.2) g := by
      exact coeff_mul k f g
    simp_rw [this]
    have : ∃ i j : ℕ, i + j = k ∧
        padicNormE (∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p] p_1.2) g) ≤
        padicNormE (coeff _ i f * coeff _ j g) := by
        -- done by padicNormE nonarchimedean

      sorry
    obtain ⟨i, j, hij, start⟩ := this
    have interim : padicNormE (∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p] p_1.2) g) * c^k ≤
        padicNormE ((coeff ℚ_[p] i) f * (coeff ℚ_[p] j) g) * c^k := by
      have hc : c ≠ 0 := by
        exact Ne.symm (ne_of_lt hc)
      simp only [AbsoluteValue.map_mul, Rat.cast_mul, ge_iff_le]
      -- just need to remove the c^k
      sorry
    simp only [AbsoluteValue.map_mul, Rat.cast_mul] at interim
    have final : ↑(padicNormE ((coeff ℚ_[p] i) f)) * ↑(padicNormE ((coeff ℚ_[p] j) g)) * c ^ k ≤
        sSup {x | ∃ i j, i + j = k ∧ ↑(padicNormE ((coeff ℚ_[p] i) f)) * ↑(padicNormE ((coeff ℚ_[p] j) g)) * c ^ k = x} := by
      -- may be a hardish manipulation. If we can show LHS is an element in th RHS and the RHS is bounded we are done
      sorry
    exact
      Preorder.le_trans
        (↑(padicNormE
              (∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p] p_1.2) g)) *
          c ^ k)
        (↑(padicNormE ((coeff ℚ_[p] i) f)) * ↑(padicNormE ((coeff ℚ_[p] j) g)) * c ^ k)
        (sSup
          {x |
            ∃ i j,
              i + j = k ∧
                ↑(padicNormE ((coeff ℚ_[p] i) f)) * ↑(padicNormE ((coeff ℚ_[p] j) g)) * c ^ k = x})
        interim final

lemma eq1 (f g : PowerSeries ℚ_[p]) : ∀ (k : ℕ), sSup {x : ℝ | ∃ (i j : ℕ), i + j = k ∧
    ((padicNormE (coeff _ i f)) * (padicNormE (coeff _ j g)) * c^k = x)} = sSup {x : ℝ | ∃ (i j : ℕ),
    i + j = k ∧ (x = ((padicNormE (coeff _ i f)) * c^i) * ((padicNormE (coeff _ j g)) * c^j) )} := by
  intro k
  refine csSup_eq_csSup_of_forall_exists_le ?hs ?ht
  · simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro x a b hk h
    use x
    simp only [le_refl, and_true]
    use a
    use b
    constructor
    · exact hk
    · ring_nf
      have : c^a * c^b = c^ k := by
        simp_rw [Eq.symm (pow_add c a b)]
        exact congrArg (HPow.hPow c) hk
      rw [← h]
      ring_nf
      nth_rw 2 [mul_assoc]
      rw [this]
  · simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro y a b hk h
    use y
    simp only [le_refl, and_true]
    use a
    use b
    constructor
    · exact hk
    · ring_nf
      have : c^a * c^b = c^ k := by
        simp_rw [Eq.symm (pow_add c a b)]
        exact congrArg (HPow.hPow c) hk
      rw [h]
      ring_nf
      nth_rw 2 [mul_assoc]
      rw [this]

lemma ineq2 (f g : PowerSeries ℚ_[p]) (hc : 0 < c) : ∀ (k : ℕ), sSup {x : ℝ | ∃ (i j : ℕ),
    i + j = k ∧ (x = ((padicNormE (coeff _ i f)) * c^i) * ((padicNormE (coeff _ j g)) * c^j) )} ≤
    (cnorm1 c p f) * (cnorm1 c p g) := by
  intro k
  simp_rw [cnorm1]
  refine Real.sSup_le ?hs ?ha
  · intro x
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro a b hk hx
    rw [hx]
    have hf (a : ℝ) (ha : a ∈ {padicNormE (coeff _ i f) * c^i | (i : ℕ)}) :=
        le_csSup (myset1_bddabove c p f) ha
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hf
    have hg (a : ℝ) (ha : a ∈ {padicNormE (coeff _ i g) * c^i | (i : ℕ)}) :=
        le_csSup (myset1_bddabove c p g) ha
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hg
    -- just need to combine hf and hg
    sorry
  · have := cnorm1_nonneg c p hc
    simp_rw [cnorm1] at this
    exact Left.mul_nonneg (this f) (this g)


/-
Dont believe this is true anymore for anything but polynomials, instead will only have the above part
on restricted powerseries
-/
theorem cnorm1_mul : ∀ (x y : PowerSeries ℚ_[p]), cnorm1 c p (x * y) = cnorm1 c p x * cnorm1 c p y := by
  /-intro f g
  have : ∀ k : ℕ, (coeff ℚ_[p] k) (f * g) = ∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p] p_1.2) g := by
    exact fun k ↦ coeff_mul k f g
  have h1 := ineq1 c p f g
  have h2 := eq1 c p f g-/
  intro x y
  have step1 : cnorm1 c p (x * y) ≤  cnorm1 c p x * cnorm1 c p y :=
    sorry
  have step2 : cnorm1 c p (x * y) ≥ cnorm1 c p x * cnorm1 c p y:=
    --- false in anything but polynomials
    sorry

  sorry


/- Not true even for restricted powerseries I think-/
noncomputable
def cnorm1_AbsVal (hc : 0 < c) : AbsoluteValue (PowerSeries ℚ_[p]) ℝ where
  toFun := cnorm1 c p
  map_mul' := cnorm1_mul c p
  nonneg' := cnorm1_nonneg c p hc
  eq_zero' := cnorm1_eq_zero c p hc
  add_le' := cnorm1_add_leq c p hc

end Generalising


def cnorm1_seminorm (hc : 0 < c) : Seminorm ℚ_[p] (PowerSeries ℚ_[p]) where
  toFun := cnorm1 c p
  map_zero' := by
    rw [cnorm1]
    simp only [map_zero, AbsoluteValue.map_zero, Rat.cast_zero, zero_mul, exists_const,
      Set.setOf_eq_eq_singleton', csSup_singleton]
  add_le' := cnorm1_add_leq c p hc
  neg' := by
    intro f
    simp_rw [cnorm1]
    simp only [map_neg, map_neg_eq_map]
  smul' := by
    intro a f
    simp_rw [cnorm1]
    simp only [map_smul, smul_eq_mul, AbsoluteValue.map_mul, Rat.cast_mul]
    sorry



/-
Need to define restricted powerseries. It is not an absolute value when we are in
powerseries. Rather just a norm with mul ≤ !
Would I want to show it is a seminorm with usual powerseries. Then a full norm on
restricted powerseries? Could also show it is an absolute value when only on
polynomials
Idea: Show seminorm on general powerseries
      Show full norm and majority of abs value properties
      Show mul ≥ on polynomials. (So absolute value on field of fractions of poly)
-/

-- unsure if I should be using filters? which i dont understand

structure PowerSeries_restricted (R : Type*) [NormedRing R] where
  f : PowerSeries R
  convergence : ∀ k : ℝ, ∃ N : ℕ, N < i →  (norm (PowerSeries.coeff R i f)) * c^i < k

-- Want to replicate everything but using this now. (Realistacly this will only be used in the proofs of bddabove and existanc

/- This required minimal changes, just-/
theorem cnorm1_nonneg1 (hc : 0 < c) : ∀ (x : PowerSeries_restricted c ℚ_[p]), 0 ≤ cnorm1 c p x.1 := by
  intro f
  rw [cnorm1]
  have := cnorm1_existance c p f.1
  obtain ⟨j, hj⟩ := this
  simp_rw [hj]
  have : ∀ (i : ℕ), 0 ≤ (padicNormE (PowerSeries.coeff _ i f.1)) * c^i := by
    intro i
    apply mul_nonneg
    · simp only [Rat.cast_nonneg, apply_nonneg]
    · apply pow_nonneg
      exact le_of_lt hc
  exact this j
