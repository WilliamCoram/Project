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

-- Feel like I want a function that maps t to its first points?????

structure FirstPoint (t : Set (Prod ℝ ℝ)) where
  point : t
  minimal : ∀ v : t, point.1.1 ≤ v.1.1

def Reducedset (t : Set (Prod ℝ ℝ)) (u : t)  : Set (Prod ℝ ℝ) :=
  t \ {u.1}


-- Could try something like this, but not sure how to specialise at each of the new firstpoints
def StepFun : Set (Prod ℝ ℝ) → Set (Prod ℝ ℝ) :=
  fun t => Reducedset t




-- example of some recursive definition
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n

def function (t : Set (Prod ℝ ℝ)): t → Set (Prod ℝ ℝ) :=
  fun u => (Reducedset t u)

def IndexingFunction (t : Set (Prod ℝ ℝ)): ℕ → Prod ℝ ℝ :=
  sorry


----------------------------------------------------------------------------------------------------

/-
New idea is to define the set of slopes at a point. Then take the smallest one. And the NewtonPolygon
is then the union of all these slopes
-/

variable (t : Finset (Prod ℝ ℝ))


def SetofSlopes (a : t) : Set ℝ :=
  { c  | ∃ b : t, b.1.1 > a.1.1 ∧ c = (a.1.2 - b.1.2) / (a.1.1 - b.1.1) }

def SetofSlopes_finite (a : t) : Set.Finite (SetofSlopes t a) := by
  -- t finite
  sorry

def SetofSlopes_nonempty (a : t)  : (Set.Finite.toFinset (SetofSlopes_finite t a)).Nonempty :=
  -- t nonempty and assuming we are NOT at the end point.
  sorry

noncomputable
def SetofSlopes_minimum (a : t) : ℝ :=
  Finset.min' (Set.Finite.toFinset (SetofSlopes_finite t a)) (SetofSlopes_nonempty t a)

/-
def SetofSegments (a : t) : Set (Set (Prod ℝ ℝ)) :=
  {(segment (Prod ℝ ℝ) a.1 b.1) | b : t}
-/

/-
def SetofSegments_minimum (a : t) : Set (Set (Prod ℝ ℝ)) :=
  {(segment (Prod ℝ ℝ) a.1 b.1) | ∃ b : t, (a.1.2 - b.1.2)/(a.1.1 - b.1.1) = SetofSlopes_minimum t a}

def SetofSegments_minimum1 (a : t) : Set (Set (Prod ℝ ℝ)) :=
  {(u : SetofSegments t a).1 | ∃ b : t, u = (segment (Prod ℝ ℝ) a.1 b.1) ∧ (a.1.2 - b.1.2)/(a.1.1 - b.1.1) = SetofSlopes_minimum t a }
-/

def SetofSlopes_minimum_nextpoint (a : t) : Set (Prod ℝ ℝ) :=
  {b : Prod ℝ ℝ | b ∈ t ∧ b.1 > a.1.1 ∧ (a.1.2 - b.2)/(a.1.1 - b.1) = SetofSlopes_minimum t a}

-- If we have this set is nonempty (not guarenteed from b.1 > a.1.1 requirement); nonempty if not endpoint
--                        finite (guarenteed from t definition)
-- Then we can takes its max (and ignore multiplicity)
--                       min (and consider multiplicity)

def SetofSlopes_minimum_nextpoint_finite (a : t) : Set.Finite (SetofSlopes_minimum_nextpoint t a) := by
  sorry

/- This is not always true -/
def SetofSlopes_minimum_nextpoint_nonempty (a : t) :
    (Set.Finite.toFinset (SetofSlopes_minimum_nextpoint_finite t a)).Nonempty := by
  sorry

/-
Now we can construct our function mapping 0 to first point,
  i+1 to SetofSlopes_minimum_nexpoint f^i
-/

def NextPoint : t → t :=
  fun a => SetofSlopes_minimum_nextpoint t a --- when nonempty; if empty need to map to something else?


def IndexFunction (a : FirstPoint t) : ℕ → t :=
  fun i => (NextPoint)^[i] t a.1

-- The Newton Polygon can then be defined via taking the union of slopes between this indexing set??
