import Mathlib

variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

open PowerSeries Filter
open scoped Topology

/-- Restricted powerseries, are those that convergence on the disk... -/
structure PowerSeries_restricted_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

/-
-- is it maybe easier to show it is a subring of the power series ring?
instance [NormedRing R] : Ring (PowerSeries_restricted_c R c) where
  zero := {function := 0, convergence := by
              simp only [map_zero, norm_zero, zero_mul, tendsto_const_nhds_iff] }
  add := sorry
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  add_comm := sorry
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  neg := sorry
  zsmul := sorry
  neg_add_cancel := sorry
  sub := sorry
  sub_eq_add_neg := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry

  -/

def PowerSeries_restricted_set [NormedRing R] : Set (PowerSeries R) :=
  {g : PowerSeries R | ∃ f : PowerSeries_restricted_c R c, f.function = g}


instance subring [NormedRing R] : Subring (PowerSeries R) where
  carrier := {g : PowerSeries R | ∃ f : PowerSeries_restricted_c R c, f.function = g}
  zero_mem' := by
    use {function := 0, convergence := by
              simp only [map_zero, norm_zero, zero_mul, tendsto_const_nhds_iff] }
  one_mem' := by
    use {function := 1, convergence := by
              simp only [coeff_one]
              intro ε
              intro hε
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
              exact mem_of_mem_nhds hε }
  add_mem' := by
    intro a b ha hb
    obtain ⟨f, hf⟩ := ha
    obtain ⟨g, hg⟩ := hb
    simp only [Set.mem_setOf_eq]
    use {function := f.function + g.function, convergence := by
              simp only [map_add]
              intro ε hε
              simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
              obtain ⟨f, hf⟩ := f
              obtain ⟨g, hg⟩ := g
              simp only

              sorry
              }
    simp only
    rw [hf, hg]
  neg_mem' := by
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
    intro g
    obtain ⟨g, hg⟩ := g
    simp only
    use {function := -g, convergence := by
              simp only [map_neg, norm_neg]
              exact hg}
  mul_mem' := by
    simp only [Set.mem_setOf_eq, forall_exists_index]
    intro f g a haf b hbf
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rw [← haf, ← hbf]
    simp only
    use {function := a * b, convergence := by
              simp only [coeff_mul]
              intro ε hε
              simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]

              sorry
              }

noncomputable
def ring [NormedRing R] : Ring {g : PowerSeries R | ∃ f : PowerSeries_restricted_c R c, f.function = g} := by
  exact Subring.toRing (subring c)

instance [NormedRing R] : Ring (PowerSeries_restricted_c R c) := by

  sorry

/-
instance [NormedRing R] : Semiring (PowerSeries_restricted_c R c) where
  zero := {function := 0, convergence := by
              simp only [map_zero, norm_zero, zero_mul, tendsto_const_nhds_iff] }
  one := {function := 1, convergence := by
              simp only [coeff_one]
              intro ε
              intro hε
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
              }
  add f g := {function := f.function + g.function, convergence := by
                simp only [map_add]
                intro ε hε
                simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
                obtain ⟨f, hf⟩ := f
                obtain ⟨g, hg⟩ := g
                simp only

                sorry
              }
  -/




/-- Generalisation of Gauss' norm.-/
noncomputable
def cNorm : (PowerSeries ℚ_[p])  → ℝ :=
  fun (f : PowerSeries ℚ_[p]) => sSup {padicNormE (coeff _ i f) * c^i | (i : ℕ)}

def cNorm_PowerSeries_restricted_bddabove (f : PowerSeries_restricted_c ℚ_[p] c):
    BddAbove {padicNormE (coeff _ i f.1) * c^i | (i : ℕ)} := by
  -- follows from convergence property
  sorry

lemma cNorm_existance (f : PowerSeries_restricted_c ℚ_[p] c) :
    ∃ j : ℕ, sSup {padicNormE (coeff _ i f.1) * c^i | (i : ℕ)} =
    padicNormE (coeff _ j f.1) * c^j := by
  -- follows from convergence property, then reducing to a finite set and using sup is a max

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
    -- follows from multiplication of polynomials
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
def cNorm_isNorm : NormedSpace ℝ (PowerSeries_restricted_c ℚ_[p] c) where
  norm := cNorm c p
  mul := cNorm_mul_le c p
  norm_nonneg := cNorm_nonneg c p
  norm_eq_zero := cNorm_eq_zero c p
  add_le := cNorm_add_le c p
-/

noncomputable
instance (hc : 0 < c) : RingNorm (PowerSeries_restricted_c ℚ_[p] c) where
  toFun (f : PowerSeries_restricted_c ℚ_[p] c) := cNorm c p f.1
  map_zero' := by
    simp only
    have := cNorm_eq_zero c p hc 0

    -- need to get ring working properly
    sorry
  add_le' := cNorm_add_le c p hc
  mul_le' := cNorm_mul_le c p hc
  neg' := by
    sorry
  eq_zero_of_map_eq_zero' := by
    -- not working since havent finished the Ring part
    sorry


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
    intro ε
    simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
    have h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f.coeff n = 0 := by
      use (Polynomial.natDegree f + 1)
      intro n hn
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hn
    obtain ⟨N, hN⟩ := h
    intro h1
    use N
    intro n hn
    have h2 : f.coeff n = 0 := by
      exact hN n hn
    simp only [h2, sub_zero, norm_zero, mul_zero, zero_mul, sub_self]
    exact mem_of_mem_nhds h1


noncomputable
def cNorm_poly : (Polynomial ℚ_[p]) → ℝ :=
  fun f => cNorm c p f


lemma cNorm_poly_mul_ge (f g : Polynomial ℚ_[p]) (hc : 0 < c) : cNorm_poly c p (f * g) ≥
    cNorm_poly c p f * cNorm_poly c p g := by
  simp_rw [cNorm_poly]
  have := cNorm_existance c p (PolyToPowerSeries_restricted  c p f)
  obtain ⟨I, hI⟩ := this
  have := cNorm_existance c p (PolyToPowerSeries_restricted  c p g)
  obtain ⟨J, hJ⟩ := this
  /-
  have h1 : ∀ i j : ℕ, i < I ∧ i + j = I + J → padicNormE ((coeff ℚ_[p] i f) * (coeff ℚ_[p] j g))
      * c^(((i + j) : ℤ)) ≤ cNorm c p f * cNorm c p g := by
    intro i j hij
    have : ↑(padicNormE ((coeff ℚ_[p] i) ↑f * (coeff ℚ_[p] j) ↑g)) * c ^ (((i + j) : ℤ)) =
        ↑(padicNormE ((coeff ℚ_[p] i) ↑f)) * c ^ (i : ℤ) * (↑(padicNormE ((coeff ℚ_[p] j) ↑g)) * c ^ (j : ℤ)) := by
      simp only [Polynomial.coeff_coe, AbsoluteValue.map_mul, Rat.cast_mul]
      ring_nf
    rw [this]
    have h2 : ↑(padicNormE ((coeff ℚ_[p] i) ↑f)) * c ^ (i : ℤ) ≤ cNorm c p f := by
      exact cNorm_sSup_le c p (PolyToPowerSeries_restricted c p f) i
    have h3 : ↑(padicNormE ((coeff ℚ_[p] j) ↑g)) * c ^ (j : ℤ) ≤ cNorm c p g := by
      exact cNorm_sSup_le c p (PolyToPowerSeries_restricted c p g) j
    exact mul_le_mul_of_nonneg h2 h3
      (cNorm_element_nonneg c p (PolyToPowerSeries_restricted c p f) hc i)
      (cNorm_nonneg c p hc (PolyToPowerSeries_restricted c p g))
  have h2 : ∀ i j : ℕ, j < J ∧ i + j = I + J → padicNormE ((coeff ℚ_[p] i f) * (coeff ℚ_[p] j g)) *
      c^((i + j) : ℤ) ≤ cNorm c p f * cNorm c p g := by
    -- surely there is a way to use symmetry of h1
    sorry
  -/
  have h3 : padicNormE ((coeff ℚ_[p] I f) * (coeff ℚ_[p] J g)) * c^(((I + J) : ℤ)) =
      cNorm c p f * cNorm c p g := by
    simp_rw [cNorm]
    simp_rw [PolyToPowerSeries_restricted] at hI hJ
    rw [hI, hJ]
    have : ↑(padicNormE ((coeff ℚ_[p] I) ↑f * (coeff ℚ_[p] J) ↑g)) * c ^ (((I + J) : ℤ)) =
        ↑(padicNormE ((coeff ℚ_[p] I) ↑f)) * c ^ (I : ℤ) * (↑(padicNormE ((coeff ℚ_[p] J) ↑g)) * c ^ (J : ℤ)) := by
      simp only [Polynomial.coeff_coe, AbsoluteValue.map_mul, Rat.cast_mul]
      ring_nf
      have : (c^ (I : ℤ)) * (c ^ (J : ℤ)) = c ^ ((I + J) : ℤ) := by
        sorry
      -- why
    simp_rw [this]
    rfl
  /-
  have h4 : padicNormE (∑ p_1 ∈ Finset.antidiagonal (I+J), (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p]
      p_1.2) g) * c^((I +  J) : ℤ) = cNorm c p f * cNorm c p g := by
    simp only [Polynomial.coeff_coe]
    rw [← h3]
    have hc : c ≠ 0 := by
      exact Ne.symm (ne_of_lt hc)
    simp only [hc, mul_eq_mul_right_iff, mul_eq_mul_left_iff]
    left

    -- Need to use the Nonarchimidien property of padicNormE

    -- done by arguement of h1,h2,h3 as we have max at h3 case; do we need h1 and h2??
    sorry
   -/
  have h4 : padicNormE (∑ p_1 ∈ Finset.antidiagonal (I+J), (coeff ℚ_[p] p_1.1) f * (coeff ℚ_[p]
      p_1.2) g) * c^((I +  J) : ℤ) ≥ cNorm c p f * cNorm c p g := by
    simp only [Polynomial.coeff_coe, ge_iff_le]
    rw [← h3]
    have hc : c ≠ 0 := by
      exact Ne.symm (ne_of_lt hc)
    simp only [Polynomial.coeff_coe]
    -- Need to apply nonarchimedian property
    sorry
  have h5 : ↑(padicNormE (∑ p_1 ∈ Finset.antidiagonal (I + J), (coeff ℚ_[p] p_1.1) ↑f * (coeff ℚ_[p] p_1.2) ↑g))
      * c ^ ((I + J) : ℤ) ≤ cNorm c p (f * g) := by
    simp_rw [cNorm]
    have := coeff_mul (I + J) (PolyToPowerSeries_restricted c p f).function
        (PolyToPowerSeries_restricted c p g).function
    simp_rw [PolyToPowerSeries_restricted] at this
    rw [← this]
    have := cNorm_sSup_le c p (PolyToPowerSeries_restricted c p (f * g)) (I + J)
    simp only [PolyToPowerSeries_restricted, Polynomial.coe_mul, cNorm] at this
    exact this
  simp only [Polynomial.coe_mul, ge_iff_le]
  simp only [Polynomial.coeff_coe, ge_iff_le] at h4
  simp only [Polynomial.coeff_coe] at h5
  -- apply h4 and h5

  sorry
  /-
  rw [h4] at h5
  simp only [Polynomial.coe_mul, ge_iff_le]
  exact h5
  -/

noncomputable
def cNorm_poly_AbsVal (hc : 0 < c) : AbsoluteValue (Polynomial ℚ_[p]) ℝ where
  toFun := cNorm_poly c p
  map_mul' := by
    intro f g
    have ge := cNorm_poly_mul_ge c p f g hc
    have le := cNorm_mul_le c p hc (PolyToPowerSeries_restricted c p f)
        (PolyToPowerSeries_restricted c p g)
    have : (PolyToPowerSeries_restricted c p f * PolyToPowerSeries_restricted c p g).function =
       (PolyToPowerSeries_restricted c p (f * g)).function := by
      sorry
    rw [this] at le
    simp only [PolyToPowerSeries_restricted, Polynomial.coe_mul] at le
    simp only [cNorm_poly, Polynomial.coe_mul, ge_iff_le] at ge
    simp only [cNorm_poly, Polynomial.coe_mul]
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

----------------------------------------------------------------------------------------------------

/-
To show the Weierstrass preparation Theorem we will need a few things:
The space of restricted powerseries is complete
The space of polynomials is dense in the space of restricted powerseries
A generalistation of a lemma giving wanted inequalities
-/


-- For now we are going to define the Weierstrass preparation theorem; this will be moved down later

theorem Weierstrass_preparation_theorem (hc : 0 < c) (f : PowerSeries_restricted_c ℚ_[p] c) (hN : ∃ N : ℕ,
    (cNorm c p f.1 = padicNormE (coeff ℚ_[p] N f.1) * c^N) ∧ (∀ n : ℕ, N < n →
    (padicNormE (coeff _ N f.1) * c^n ) ≤ cNorm c p f.1 )) : ∃ (g : Polynomial ℚ_[p]),
    Polynomial.degree g = (N : ℕ) ∧ ∃ (h : PowerSeries_restricted_c ℚ_[p] c), coeff ℚ_[p] 1 h.1 = 1 ∧
    f.1 = g * h.1 ∧ cNorm c p g = padicNormE (Polynomial.coeff g N) * c^N ∧ (cNorm c p (h - 1).1) < 1
    ∧ (cNorm c p (f - PolyToPowerSeries_restricted c p g).1) < 1  := by
  sorry

instance PowerSeries_restricted_c_is_uniform : NormedRing (PowerSeries_restricted_c ℚ_[p] c) where
  sorry


instance PowerSeries_restricted_c_is_complete : CompleteSpace (PowerSeries_restricted_c ℚ_[p] c) where
  complete := by
    -- Want to copy 7.2.7 in Gouvea's book but generalised to c -- will have to do for c = 1 first
    sorry

-- Not sure how to show dense without defining sets?
instance Polynomial_is_dense : Dense (PowerSeries_restricted_c ℚ_[p] c) (Polynomial ℚ_[p]) := by
  sorry

-- Maybe need to physically define Dense?


/-
This should say there is a sequence of polynomials converging to the power series
i.e. for the function i -> polynomial i
This may have to be defined via coefficients?
i.e. ∀ n : ℕ , function j -> coeff n (polynomial j) is a sequence converging to coeff _ n f
-/

lemma Polynomial_is_dense2 (f : PowerSeries_restricted_c ℚ_[p] c) : ∃ (g : ℕ → Polynomial ℚ_[p]),
    Tendsto (fun i : ℕ => cNorm c p (f - PolyToPowerSeries_restricted c p (g i)).1 ) atTop (𝓝 0) := by
  -- Want to use the restriction of a powerseries to a polynomial
  use (fun i : ℕ => PowerSeries.trunc i f.1)

  /-
  simp only
  --intro ε hε
  --simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  have : ∀ k : ℕ, cNorm c p (f - PolyToPowerSeries_restricted c p (PowerSeries.trunc k f.1)).1 =
      sSup {padicNormE (coeff _ n f.1) * c^n | n > k} := by
    sorry
  simp_rw [this]
  simp only [gt_iff_lt]
  obtain ⟨f, hf⟩ := f
  -- im guessing we could use that the sSup is less than cNorm c p f.1, which tends to zero
  -/

  have (i : ℕ): cNorm c p (f - PolyToPowerSeries_restricted c p (PowerSeries.trunc i f.1)).function
      ≤ cNorm c p f.1 := by
      -- true since the LHS is the tail of a truncation of f
    sorry


  sorry
