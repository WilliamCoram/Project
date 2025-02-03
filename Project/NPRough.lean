import Mathlib

open PowerSeries

variable (k : Type*) [Semiring k] [Algebra ℚ k]
variable (p : ℕ) [Fact (Nat.Prime p)]

def Poly_set (f : PowerSeries ℚ_[p]): Set (Prod ℝ ℝ) :=
  {((i , Padic.valuation (coeff ℚ_[p] i f)) : Prod ℝ ℝ) | (i : ℕ)}

/- Not sure I actually wanting to be doing this
def LowerConvexHull (f : PowerSeries ℚ_[p]) : Set (Prod ℝ ℝ) :=
    {u : Prod ℝ ℝ | (∃ u' : convexHull ℝ (Poly_set p f), u'.1 = u) ∧
    (∀ (q : convexHull ℝ (Poly_set p f)), q.1.1 = u.1 → u.2 ≤ q.1.2)}

def Poly_set_breaks (f : PowerSeries ℚ_[p]): Set (Prod ℝ ℝ) :=
  (Poly_set p f) ∩ (LowerConvexHull p f)
-/

-- Need to create the reduced set of Poly_set so that we actually only have the points we want

structure FirstPoint (t : Set (Prod ℝ ℝ)) where
  point : t
  minimal : ∀ v : t, point.1.1 ≤ v.1.1

def Reducedset (t : Set (Prod ℝ ℝ)) (u : FirstPoint t)  : Set (Prod ℝ ℝ) :=
  t \ {u.1.1}



def IndexingFunction : ℕ → Prod ℝ ℝ :=
  fun i ↦
  sorry
