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

-- Convergence such that ∃ N, s.t. ∀ n ≥ N,
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

-- still need to dfine two functions for i and nu
-- fun i to set of points to consider slopes on
-- fun i to x coord (maybe  not needed)
-- then fun i to y coord
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

noncomputable
def NP (f : PowerSeries_restricted_c ℚ_[p] c): ℕ → Prod ℕ ℝ × ℝ :=
  fun i => (Indexing_points p c f i, Indexing_slopes p c f i)



-- still need to define two functions for i and nu
-- fun i to x coord (maybe  not needed; its just ℕ)
-- fun i to set of points to consider slopes on (by a finset of x coords)
-- then fun i to point slope pair based on finset
-- fun point to its next point which is the 'min' of the pairs

-- proceed as before
-- then NP is the two functions enumerating next points and their slopes

variable (f : PowerSeries_restricted_c ℚ_[p] c)

/-
def xset : Set ℕ :=
  {a | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f.function) ≠ 0 }
-/

/- For now ignoring this
/- Problem is we need to restrict to when coeff is non-zero? Unless we do not and go more careful later on -/
def fun_x : ℕ → ℕ :=
  fun i => i
-/

/- Function indexing the valuations of the coeff - based on the previous function -/
noncomputable
def fun_y : ℕ → ℤ :=
  fun i => Padic.valuation (coeff ℚ_[p] i f.function)


/- This is the corresponding finite set for each (i,nu); with the assumption of indexing the x coords
this will be where we limit the choice of coeff not 0-/
def finite_set (i : ℕ) : Finset ℕ :=
  sorry


/- This is the function sending i to its finite set -/
def fun_set : ℕ → Finset ℕ :=
  fun i => finite_set i

-- Now we will assume we have a Finset

variable (V : Finset ℕ)

/-
noncomputable
def slope_pair (i : ℕ) : V → Prod ℕ ℤ :=
  fun v => (v, (fun_y p c f v - fun_y p c f i) / (v - i))
-/

-- the i will be the x coord of the defining Finset
noncomputable
def slopes (i : ℕ) : V → ℤ :=
  fun v => (fun_y p c f v - fun_y p c f i) / (v - i)

-- Will need to adjust to when it is non-empty and not; but this is only a slight change
noncomputable
def min_slope (i : ℕ) : ℤ :=
  Finset.min' ((V.attach).image (slopes p c f V i)) sorry

-- This will reduce the finite set to the points that give the minimum slope
noncomputable
def reduced_finset (i : ℕ) : Finset ℕ :=
  V.filter (λ (a : ℕ) =>  (fun_y p c f a - fun_y p c f i) / (a - i) = min_slope p c f V i)


-- will be reliant on V being nonempty following from above
noncomputable
def next_point (i : ℕ) : ℕ :=
  Finset.min' (reduced_finset p c f V i) sorry

-- This will need to have a fun_set nonempty if in the second part
/- Indexing x coord -/
noncomputable
def Index_x : ℕ → ℕ
  | 0 => 0 -- Just need to adjust 0 to the first point
  | i + 1 => next_point p c f (fun_set (Index_x i)) (Index_x i)

-- This will need a fun_set non_empty if else map to???
/- Indexing slope -/
noncomputable
def Index_slope : ℕ → ℤ :=
  fun i => min_slope p c f (fun_set (Index_x p c f i)) (Index_x p c f i)

structure lowerconvexhull where
  points_x : ℕ → ℕ
  points_y : ℕ → ℤ
  slopes : ℕ → ℤ
  relation : ∀ i : ℕ, points_y (i + 1) - points_y i = slopes i * (points_x (i + 1) - points_x (i))
  slopes_increase : ∀ i : ℕ, slopes (i + 1) ≥ slopes i

noncomputable
def NewtonPolygon (f : PowerSeries_restricted_c ℚ_[p] c) : lowerconvexhull :=
  ⟨Index_x p c f, fun_y p c f, Index_slope p c f, sorry, sorry⟩
