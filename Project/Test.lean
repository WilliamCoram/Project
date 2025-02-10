import Mathlib

variable (k : Type*) [Semiring k] [Algebra ℚ k]
variable (p : ℕ) [Fact (Nat.Prime p)]

open PowerSeries

-- This may be specialising too much. Could do the work for a general set; then apply this for sets given.
-- Other than working from a PowerSeries and up.


--- As above better to work in a Finset first do calculations on nexpoint

def Poly_set (f : PowerSeries ℚ_[p]) : Set (Prod ℤ ℝ) :=
  {(a,b) : Prod ℤ ℝ | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f) ≠ 0 ∧ b = Padic.valuation (coeff ℚ_[p] i f)}

def Poly_firstCoord (f : PowerSeries ℚ_[p]) : Set ℕ :=
  {a | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f) ≠ 0 }

noncomputable
def FirstPoint (f : PowerSeries ℚ_[p]) : Prod ℤ ℝ :=
  (Int.ofNat (sInf (Poly_firstCoord p f)), Padic.valuation (coeff ℚ_[p] (sInf (Poly_firstCoord p f)) f))

noncomputable
def FirstPointinc (f : PowerSeries ℚ_[p]) : FirstPoint p f ∈ Poly_set p f := by
  rw [Poly_set, FirstPoint]
  simp only [ne_eq, Int.ofNat_eq_coe, Set.mem_setOf_eq, Nat.cast_inj, Int.cast_inj, exists_eq_left',
    and_true]
  simp_rw [← ne_eq]
  simp_rw [Poly_firstCoord]
  simp only [exists_eq_left']
  -- need the case of f not being zero; but this is working
  sorry


def SetofSlopes (a : Poly_set p f) : Set ℝ :=
  { c  | ∃ b : Poly_set p f, b.1.1 > a.1.1 ∧ c = (a.1.2 - b.1.2) / (a.1.1 - b.1.1) }

-- Want to find the minimum of this set; how do I argue this minimum exists

-- If the above set is empty we can map nextpoint u to u

-- Then the values what correspond to this
-- Then find the min or max that does this
-- Probably should be minimum as it could technically be a flat line so has inifinitely many points?

noncomputable
def NextPoint (u : Poly_set p f) : Poly_set p f :=
  if h : ∃ b : Poly_set p f, b.1.1 > u.1.1 ∧ (u.1.2 - b.1.2) / (u.1.1 - b.1.1) = sorry
  then Classical.choose h
  else u

noncomputable
def IndexFunction (u : Poly_set p f) : ℕ → Poly_set p f :=
  fun i => Nat.iterate (NextPoint p) i u

/-
Wanting to create two functions
n to the relevant points
n to the slopes at the points


convergent powerseries implies there exists a finite set of slopes we would need to consider,
as there exists some i such that padic evaluations always increases, choosing the interval which includes
all the finite points that are smaller.
This will give a function from a fin set to the padic valuations in the interval
Have a function from valuations to the slopes
And take the minimum of these

-/

/-Planned set up:
  ⬝ Give a first point of the restricted powerseries
  ⬝ Construct a Finset of points starting from this point that will include the next point; this
    is obtained via using convergence property and the N s.t. the valuation is strictly increasing
    aftwards
  ⬝ Construct a function that will give the minimum of the slopes of the points in the Finset
  ⬝ Construct a function that will give the next point; defined as the maximum (or minimum) of the points which
    give the minimum slope
  ⬝ Construct a function that maps from first point to the next point; obtained as a map from first
    point to its Finset, then the corresponding minimum slope, then the next point
  ⬝ Construct an indexing function that will give the nth point

  ⬝ Construct a second function that will give the corresponding slope to each of the points in the
    other function

  ⬝ The NP is then the two functions indexing the nth point and the nth slope
-/
