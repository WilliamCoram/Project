import Mathlib

variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

open PowerSeries Filter
open scoped Topology

/-- Restricted powerseries, are those that convergence on the disk... -/
structure PowerSeries_restricted_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

instance [NormedRing R] : Semiring (PowerSeries_restricted_c R c) := by
  sorry
  /-
  zero := { function := 0, convergence := by
              simp only [map_zero, norm_zero, zero_mul, tendsto_const_nhds_iff] }
  one := { function := 1, convergence := by
              simp only [coeff_one]
              sorry }
  add f g := { function := f.function + g.function, convergence := by
                simp only [map_add]
                sorry }
  mul f g := { function := f.function * g.function, convergence := sorry}
  zero_add := by
                intro f
  -/



/-- Generalisation of Gauss' norm.-/
noncomputable
def cNorm : (PowerSeries ℚ_[p])  → ℝ :=
  fun (f : PowerSeries ℚ_[p]) => sSup {padicNormE (coeff _ i f) * c^i | (i : ℕ)}

def cNorm_PowerSeries_restricted_bddabove (f : PowerSeries_restricted_c ℚ_[p] c):
    BddAbove {padicNormE (coeff _ i f.1) * c^i | (i : ℕ)} := by

  sorry

lemma cNorm_existance (f : PowerSeries_restricted_c ℚ_[p] c) :
    ∃ j : ℕ, sSup {padicNormE (coeff _ i f.1) * c^i | (i : ℕ)} =
    padicNormE (coeff _ j f.1) * c^j := by

  sorry

lemma cNorm_sSup_le (f : PowerSeries_restricted_c ℚ_[p] c) : ∀ i : ℕ,
    padicNormE (coeff _ i f.1) * c^i ≤ cNorm c p f.1 := by
  have (a : ℝ) (ha : a ∈ {padicNormE (coeff _ i f.1) * c^i | (i : ℕ)}) :=
      le_csSup (cNorm_PowerSeries_restricted_bddabove c p f) ha
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at this
  exact fun i ↦ this i

lemma cNorm_element_nonneg (f : PowerSeries_restricted_c ℚ_[p] c) (hc : 0 < c) : ∀ (i : ℕ),
    0 ≤ (padicNormE (coeff _ i f.1)) * c^i := by
  intro i
  apply mul_nonneg
  · simp only [Rat.cast_nonneg, apply_nonneg]
  · apply pow_nonneg
    exact le_of_lt hc

theorem cNorm_nonneg (hc : 0 < c) : ∀ (x : PowerSeries_restricted_c ℚ_[p] c),
    0 ≤ cNorm c p x.1 := by
  intro f
  have := cNorm_existance c p f
  obtain ⟨j, hj⟩ := this
  simp_rw [cNorm, hj]
  exact cNorm_element_nonneg c p f hc j

theorem cNorm_eq_zero (hc : 0 < c) : ∀ (x : PowerSeries_restricted_c ℚ_[p] c),
    cNorm c p x.1 = 0 ↔ x.1 = 0 := by
  intro f
  constructor
  · intro zero
    have : ∀ i : ℕ, padicNormE (coeff _ i f.1) = 0 := by
      intro i
      have h1 := cNorm_sSup_le c p f i
      simp_rw [zero] at h1
      have h2 := cNorm_element_nonneg c p f hc i
      have hcc : c ≠ 0 := by
        exact Ne.symm (ne_of_lt hc)
      have : ↑(padicNormE (coeff _ i f.1)) * c ^ i = 0 := by
        apply LE.le.eq_of_not_gt
        · exact h2
        · simp only [not_lt]
          exact h1
      simp only [mul_eq_zero, Rat.cast_eq_zero, map_eq_zero, pow_eq_zero_iff', hcc, ne_eq,
        false_and, or_false] at this
      exact (AbsoluteValue.eq_zero padicNormE).mpr this
    have : ∀ i : ℕ, coeff _ i f.1 = 0 := by
      intro i
      exact (AbsoluteValue.eq_zero padicNormE).mp (this i)
    exact ext this
  · have := cNorm_existance c p f
    obtain ⟨j, hj⟩ := this
    simp_rw [cNorm, hj]
    intro hf
    simp only [mul_eq_zero, Rat.cast_eq_zero, map_eq_zero, pow_eq_zero_iff', ne_eq]
    left
    exact
      (AddSemiconjBy.eq_zero_iff ((coeff ℚ_[p] j) 0)
            (congrFun (congrArg HAdd.hAdd (congrArg (⇑(coeff ℚ_[p] j)) (id (Eq.symm hf))))
              ((coeff ℚ_[p] j) 0))).mp
        rfl

theorem cNorm_nonarchimidean (hc : 0 < c): ∀ (x y : PowerSeries_restricted_c ℚ_[p] c),
    cNorm c p (x + y).1 ≤ max (cNorm c p x.1) (cNorm c p y.1) := by
  intro f g
  have := cNorm_existance c p
  obtain ⟨fj, hfj⟩ := this f
  obtain ⟨gj, hgj⟩ := this g
  obtain ⟨l, hl⟩ := this (f + g)
  simp_rw [cNorm, hfj, hgj, hl]
  have hf := cNorm_sSup_le c p f l
  have hg := cNorm_sSup_le c p g l
  simp_rw [cNorm, hfj] at hf
  simp_rw [cNorm, hgj] at hg
  have : padicNormE (coeff _ l f.1 + coeff _ l g.1) * c^l ≤
      padicNormE (coeff _ l f.1) * c^l ⊔ padicNormE (coeff _ l g.1) * c^l := by
    have hcc : c ≠ 0:= by
      exact Ne.symm (ne_of_lt hc)
    have := padicNormE.nonarchimedean' ((coeff ℚ_[p] l) f.1) ((coeff ℚ_[p] l) g.1)
    simp only [le_sup_iff, hc, pow_pos, mul_le_mul_right, Rat.cast_le]
    simp only [le_sup_iff] at this
    exact this

  -- done upto combining inequalities
  sorry

theorem cNorm_add_le (hc : 0 < c) : ∀ (x y : PowerSeries_restricted_c ℚ_[p] c),
    cNorm c p (x + y).1 ≤ cNorm c p x.1 + cNorm c p y.1 := by
  have (x y : PowerSeries_restricted_c ℚ_[p] c) : max (cNorm c p x.1) (cNorm c p y.1) ≤
      cNorm c p x.1 + cNorm c p y.1 := by
    simp only [sup_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
    constructor
    · exact cNorm_nonneg c p hc y
    · exact cNorm_nonneg c p hc x
  have h := cNorm_nonarchimidean c p hc
  exact fun x y ↦
    Preorder.le_trans (cNorm c p (x + y).function) (cNorm c p x.function ⊔ cNorm c p y.function)
      (cNorm c p x.function + cNorm c p y.function) (h x y) (this x y)


lemma cNorm_mul_le_ext1 (f g : PowerSeries_restricted_c ℚ_[p] c) (hc : 0 < c) : ∀ k : ℕ,
    padicNormE ((coeff ℚ_[p] k) (f * g).1) * c^k ≤ sSup {x : ℝ | ∃ (i j : ℕ), i + j = k ∧
    ((padicNormE (coeff _ i f.1)) * (padicNormE (coeff _ j g.1)) * c^k = x)} := by
  intro k
  have := coeff_mul k f.1 g.1
  have oops : (coeff ℚ_[p] k) (f.function * g.function)  = (coeff ℚ_[p] k) (f * g).function := by
    -- follows from multiplication of functions?
    sorry
  simp_rw [← oops, this]
  have : ∃ i j : ℕ, i + j = k ∧
        padicNormE (∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f.1 *
        (coeff ℚ_[p] p_1.2) g.1) ≤ padicNormE (coeff _ i f.1 * coeff _ j g.1) := by
      simp only [AbsoluteValue.map_mul]
      -- need to apply Nonarchimedean property of padicNormE
      sorry
  obtain ⟨i, j, hij, start⟩ := this
  have interim : padicNormE (∑ p_1 ∈ Finset.antidiagonal k, (coeff ℚ_[p] p_1.1) f.1 * (coeff ℚ_[p]
      p_1.2) g.1) * c^k ≤ padicNormE ((coeff ℚ_[p] i) f.1 * (coeff ℚ_[p] j) g.1) * c^k := by
      simp only [AbsoluteValue.map_mul, Rat.cast_mul, ge_iff_le]
      have hc : 0 < c^k := by
        sorry
      simp only [hc, mul_le_mul_right, ge_iff_le]
      simp only [AbsoluteValue.map_mul] at start
      -- need to replace the ratcast stuff
      sorry
  simp only [AbsoluteValue.map_mul, Rat.cast_mul] at interim
  have final : ↑(padicNormE ((coeff ℚ_[p] i) f.1)) * ↑(padicNormE ((coeff ℚ_[p] j) g.1)) * c ^ k ≤
        sSup {x | ∃ i j, i + j = k ∧ ↑(padicNormE ((coeff ℚ_[p] i) f.1)) * ↑(padicNormE ((coeff ℚ_[p] j) g.1)) * c ^ k = x} := by
      -- may be a hardish manipulation. If we can show LHS is an element in th RHS and the RHS is bounded we are done
      sorry
  exact
    Preorder.le_trans
      (↑(padicNormE
            (∑ p_1 ∈ Finset.antidiagonal k,
              (coeff ℚ_[p] p_1.1) f.function * (coeff ℚ_[p] p_1.2) g.function)) *
        c ^ k)
      (↑(padicNormE ((coeff ℚ_[p] i) f.function)) * ↑(padicNormE ((coeff ℚ_[p] j) g.function)) *
        c ^ k)
      (sSup
        {x |
          ∃ i j,
            i + j = k ∧
              ↑(padicNormE ((coeff ℚ_[p] i) f.function)) *
                    ↑(padicNormE ((coeff ℚ_[p] j) g.function)) *
                  c ^ k =
                x})
      interim final

lemma cNorm_mul_le_ext2 (f g : PowerSeries_restricted_c ℚ_[p] c) : ∀ (k : ℕ), sSup {x : ℝ | ∃ (i j : ℕ), i + j = k ∧
    ((padicNormE (coeff _ i f.1)) * (padicNormE (coeff _ j g.1)) * c^k = x)} = sSup {x : ℝ | ∃ (i j : ℕ),
    i + j = k ∧ (x = ((padicNormE (coeff _ i f.1)) * c^i) * ((padicNormE (coeff _ j g.1)) * c^j) )} := by
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

lemma cNorm_mul_le_ext3 (f g : PowerSeries_restricted_c ℚ_[p] c) (hc : 0 < c) : ∀ (k : ℕ), sSup {x : ℝ | ∃ (i j : ℕ),
    i + j = k ∧ (x = ((padicNormE (coeff _ i f.1)) * c^i) * ((padicNormE (coeff _ j g.1)) * c^j) )} ≤
    (cNorm c p f.1) * (cNorm c p g.1) := by
  intro k
  refine Real.sSup_le ?hs ?ha
  · intro x
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro a b hk hx
    rw [hx]
    have hf := cNorm_sSup_le c p f a
    have hg := cNorm_sSup_le c p g b
    have := cNorm_element_nonneg c p f hc
    refine mul_le_mul_of_nonneg hf hg (this a) ?hs.d0
    exact cNorm_nonneg c p hc g
  · have := cNorm_nonneg c p hc
    simp_rw [cNorm] at this
    exact Left.mul_nonneg (this f) (this g)

theorem cNorm_mul_le (hc : 0 < c) : ∀ (x y : PowerSeries_restricted_c ℚ_[p] c),
    cNorm c p (x * y).1 ≤ cNorm c p x.1 * cNorm c p y.1 := by
  intro f g
  have := cNorm_existance c p (f*g)
  obtain ⟨k, hk⟩ := this
  rw [cNorm, hk]
  have h1 := cNorm_mul_le_ext1 c p f g hc k
  have h2 := cNorm_mul_le_ext2 c p f g k
  have h3 := cNorm_mul_le_ext3 c p f g hc k
  simp_rw [h2] at h1
  exact
    Preorder.le_trans (↑(padicNormE ((coeff ℚ_[p] k) (f * g).function)) * c ^ k)
      (sSup
        {x |
          ∃ i j,
            i + j = k ∧
              x =
                ↑(padicNormE ((coeff ℚ_[p] i) f.function)) * c ^ i *
                  (↑(padicNormE ((coeff ℚ_[p] j) g.function)) * c ^ j)})
      (cNorm c p f.function * cNorm c p g.function) h1 h3

-- This gives everything we will initially want about restricted power series

/-
Things to do now:
Finish sorry's
Show absolute value on polynomials (will need to show polynomials are restricted power series,
  should be fine, and they have map_mul_ge - from Gouvea's book)
Show its a norm? Not sure how to do this. Maybe show its a normedspace?
Continue to Weierstrass preperation theorem
-/

noncomputable
def PolyToPowerSeries_restricted (f : Polynomial ℚ_[p]) : PowerSeries_restricted_c ℚ_[p] c where
  function := Polynomial.toPowerSeries f
  convergence := by
    simp only [Polynomial.coeff_coe]
    simp_rw [Tendsto]
    simp_rw [Filter.map]
    sorry

noncomputable
def cNorm_poly : (Polynomial ℚ_[p]) → ℝ :=
  fun f => cNorm c p f


lemma cNorm_poly_mul_ge (f g : Polynomial ℚ_[p]) (hc : 0 < c) : cNorm_poly c p (f * g) ≥
    cNorm_poly c p f * cNorm_poly c p g := by
  sorry

noncomputable
def cNorm_poly_AbsVal (hc : 0 < c) : AbsoluteValue (Polynomial ℚ_[p]) ℝ where
  toFun := cNorm_poly c p
  map_mul' := by
    intro f g
    have ge := cNorm_poly_mul_ge c p f g hc
    have le := cNorm_mul_le c p hc (PolyToPowerSeries_restricted c p f)
        (PolyToPowerSeries_restricted c p g)
    simp only [ge_iff_le] at ge
    simp_rw [cNorm_poly]
    simp_rw [cNorm_poly] at ge
    simp_rw [PolyToPowerSeries_restricted] at le

    -- very close need to rw le
    sorry
  nonneg' := by
    intro f
    simp_rw [cNorm_poly]
    exact cNorm_nonneg c p hc (PolyToPowerSeries_restricted c p f)
  eq_zero' := by
    intro f
    simp_rw [cNorm_poly]
    have h1 := cNorm_eq_zero c p hc (PolyToPowerSeries_restricted c p f)
    simp_rw [PolyToPowerSeries_restricted] at h1
    have h2 : f = 0 ↔ (PolyToPowerSeries_restricted c p f).function = 0 := by
      simp_rw [PolyToPowerSeries_restricted]
      exact Iff.symm Polynomial.coe_eq_zero_iff
    simp_rw [PolyToPowerSeries_restricted] at h2
    exact Iff.trans h1 (id (Iff.symm h2))
  add_le' := by
    intro f g
    simp_rw [cNorm_poly]
    have := cNorm_add_le c p hc (PolyToPowerSeries_restricted c p f)
        (PolyToPowerSeries_restricted c p g)
    have help : (PolyToPowerSeries_restricted c p f + PolyToPowerSeries_restricted c p g).function =
        (PolyToPowerSeries_restricted c p f).function + (PolyToPowerSeries_restricted c p g).function := by
      simp_rw [PolyToPowerSeries_restricted]
      -- having issues with addition and multiplication - maybe need to return to it being a semiring
      sorry
    simp only [Polynomial.coe_add, ge_iff_le]
    simp_rw [help, PolyToPowerSeries_restricted] at this
    exact this
