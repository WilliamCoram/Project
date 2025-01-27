import Mathlib

section Definitions

variable (F M L : Type*) [OrderedSemiring F]
variable [AddCommMonoid M] [OrderedSemiring L] [Module F M] [Module F L] [InfSet L]

variable (U : Set (Prod M L))

/-- The Newton Polygon of a set of points `p` in `Prod M L`. -/
def NewtonPolygon : Set (Prod M L) :=
  {u : Prod M L | (∃ u' : convexHull F U, u'.1.1 = u.1) ∧
  (u.2 = sInf {v : L | ∃ v' : convexHull F U,  v'.1.1 = u.1 ∧ v = v'.1.2})}

/-- The intersection of the NewtonPolygon and its defining set-/
def NewtonPolygon_breaks : Set (Prod M L) :=
  (NewtonPolygon F M L U) ∩ U

end Definitions

section ksquared

/- Unsure if these are the best/most general choice of variables-/
variable (k : Type*) [OrderedRing k] [Field k] [InfSet k]
variable (U : Set (Prod k k))


/-- Given a point in NewtonPolygon_breaks this gives the first coordinate of the next point in NewtonPolygon_breaks -/
def NextPoint1 (a : NewtonPolygon_breaks k k k U) : k :=
  sInf {u : k | ∃ u' : NewtonPolygon_breaks k k k U, u'.1.1 = u ∧ u > a.1.1}

def NextPoint2 (a : NewtonPolygon_breaks k k k U)  : k :=
  sorry

/-- The distance between a point in NewtonPolygon_breaks and its NextPoint-/
def NewtonPolygon_slope_length (a : NewtonPolygon_breaks k k k U) : k :=
  (NextPoint1 k U a) - a.1.1

def NewtonPolygon_slope (a : NewtonPolygon_breaks k k k U) : k :=
  (sorry - a.1.1) / (NewtonPolygon_slope_length k U a)

end ksquared

section NonArchAbsValue

open Polynomial

variable (c : ℝ) (p : ℕ)

noncomputable
def cnorm : ℚ[X] → ℝ :=
  fun f => sSup {padicNorm p (coeff f i) * c^i | (i : ℕ)}

theorem cnorm_mul : ∀ (x y : ℚ[X]), cnorm c p (x * y) = cnorm c p x * cnorm c p y := by
  sorry

theorem cnorm_nonneg (hc : c > 0) : ∀ (x : ℚ[X]), 0 ≤ cnorm c p x := by
  sorry

theorem cnorm_eq_zero (hc : c > 0) : ∀ (x : ℚ[X]), cnorm c p x = 0 ↔ x = 0 := by
  sorry

theorem cnorm_add_leq (hc : c > 0) : ∀ (x y : ℚ[X]), cnorm c p (x + y) ≤ cnorm c p x + cnorm c p y := by
  sorry

/-- cnorm is an absolute value-/
noncomputable
def cnorm_AbsVal (hc : c > 0) : AbsoluteValue ℚ[X] ℝ where
  toFun := cnorm c p
  map_mul' := cnorm_mul c p
  nonneg' := cnorm_nonneg c p hc
  eq_zero' := cnorm_eq_zero c p hc
  add_le' := cnorm_add_leq c p hc

/-- cnorm is a nonarchimidean absolute value -/
theorem cnorm_nonarchimidean : ∀ (x y : ℚ[X]), cnorm c p (x + y) ≤ max (cnorm c p x) (cnorm c p y) := by
  sorry

/-- cnorm induces the p-adic norm on the degree zero polynomials -/
theorem cnorm_inducespnorm (x : ℚ[X]) (hx : degree x = 0): cnorm c p x = padicNorm p (coeff x 0) := by
  sorry

/-- Given a polynomial `f` in `K[X]` and a valid `N` then there exists `g,h` in `K[X]` such that
`f = g h` with some given properties.-/
theorem WeierstrassPrepThm_polynomials (hc : c > 0) (f : ℚ[X]) (hf : degree f = (n : ℕ))
    (hN : ∃ N : ℕ, (0 < N ∧ N < n) ∧ (cnorm c p f = padicNorm p (coeff f N) * c^N) ∧
    (∀ j > N, cnorm c p f > padicNorm p (coeff f j) * c^j)) : ∃ g h : ℚ[X], (degree g = (N : ℕ)) ∧
    (degree h = n - N) ∧ (f = g * h) ∧ (cnorm c p f = cnorm c p g) ∧ (cnorm c p (h - (1 : ℚ[X])) < 1) := by
      sorry
