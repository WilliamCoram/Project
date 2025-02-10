import Mathlib

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
open PowerSeries Filter
open scoped Topology

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (c : ℝ)

structure PowerSeries_restricted_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

instance [NormedRing R] : Semiring (PowerSeries_restricted_c R c) := by
  sorry

def Coeff_set (f : PowerSeries_restricted_c ℚ_[p] c) : Set (Prod ℕ ℝ) :=
  {(a,b) : Prod ℕ ℝ | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f.1) ≠ 0 ∧ b = Padic.valuation (coeff ℚ_[p] i f.1)}

-- If f is the zero powerseries then this gives the first point is (0,0)
noncomputable
def First_point (f : PowerSeries_restricted_c ℚ_[p] c) : Prod ℕ ℝ :=
  let s := Coeff_set p c f
  let s' := {x : ℕ | ∃ y : ℝ, (x, y) ∈ s}
  let min := sInf s'
  (min, Padic.valuation (coeff ℚ_[p] (min) f.function))

-- Want to define a Finset based on a point

-- Convergence property gives an N such that something?? Not sure what we need to say to give this
-- finset
def givenN (f : PowerSeries_restricted_c ℚ_[p] c) (n : ℕ) : ∃ N : ℕ, sorry := sorry




---- At some point we are given a finset; which is non-empty

variable (U : Finset (Prod ℝ ℝ))

-- The a will be the defining point of the FinSet U
def SetofSlopes (a : U) : Set ℝ :=
  {c  | ∃ b : U, a.1.1 < b.1.1 ∧ c = (b.1.2 - a.1.2) / (b.1.1 - a.1.1)}

def SetofSlopes_finite (a : U) : Set.Finite (SetofSlopes U a) := by
  have : Set.Finite {x | x ∈ U} := by
    exact Set.finite_mem_finset U
  rw [SetofSlopes]
  /-by_contra h
  have : ¬(SetofSlopes U a).Finite → (SetofSlopes U a).Infinite := by
    exact fun a ↦ h
  apply this at h
  rw [SetofSlopes] at h
  -/
  sorry

noncomputable
def SetofSlopes_finset (a : U) : Finset ℝ :=
  Set.Finite.toFinset (SetofSlopes_finite U a)


noncomputable
def NextPoint (U : Finset (ℝ × ℝ)) (u : U) : U :=
  if h : ¬(SetofSlopes_finset U u).Nonempty then u
  else
  let min := Finset.min' (SetofSlopes_finset U u) (of_not_not h)
  let min_point := {x : U | x ≠ u ∧ x.1.2 - u.1.2 = min * (x.1.1 - u.1.1)}
  let firstentry := {x : ℝ | ∃ y : min_point, x = y.1.1.1}
  have h1 : Set.Finite firstentry := sorry
  have h2 : (h1.toFinset).Nonempty := sorry
  let min' := Finset.min' (h1.toFinset) h2
  -- want to show min_point' is a single point and we can choose that
  sorry


-- Now we can define our indexing function that iterates nextpoint
-- will have to do this after setting up the defining sets and construst it as a function from there

def Indexing_points (f : PowerSeries_restricted_c ℚ_[p] c) : ℕ → Prod ℕ ℝ
  | 0 => First_point p c f
  | n+1 => NextPoint sorry (Indexing_points n)

  -- or have to use Nat.iterate as previously done


def Indexing_slopes (f : PowerSeries_restricted_c ℚ_[p] c) : ℕ → ℝ
  | 0 => sorry
  | n+1 => sorry


def NewtonPolygon (f : PowerSeries_restricted_c )
