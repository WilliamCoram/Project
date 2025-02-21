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
  fun t => if h : ∃ u : t, true then
    let u := Classical.choose h
    Reducedset t u
    else t




-- example of some recursive definition
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n

def IndexingFunction (t : Set (Prod ℝ ℝ)) : ℕ → Prod ℝ ℝ :=
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
  -- t finite, image of a fin set 
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

structure FinalPoint (t : Set (Prod ℝ ℝ)) where
  point : t
  maximal : ∀ v : t, v.1.1 ≤ point.1.1

def SetofSlopes_minimum_nextpoint_finite (a : t) : Set.Finite (SetofSlopes_minimum_nextpoint t a) := by
  sorry

/- This is not always true, need to assume it is not the final point -/
def SetofSlopes_minimum_nextpoint_nonempty (a : t) :
    (Set.Finite.toFinset (SetofSlopes_minimum_nextpoint_finite t a)).Nonempty := by
  sorry

/-
Now we can construct our function mapping 0 to first point,
  i+1 to SetofSlopes_minimum_nexpoint f^i
-/

noncomputable
def NextPoint (t : Finset (ℝ × ℝ)) (u : t) : t :=
  if h : ∃ b : t, b.1.1 > u.1.1 ∧ (u.1.2 - b.1.2) / (u.1.1 - b.1.1) = SetofSlopes_minimum t u
  then Classical.choose h
  else u

noncomputable
def IndexFunction (t : Finset (ℝ × ℝ)) (a : t) : ℕ → t :=
  fun i => Nat.iterate (NextPoint t) i a

-- The Newton Polygon can then be defined via taking the union of slopes between this indexing set??





/-
Could also use Int.csInf_mem that is the minimum point exists. This can be used to define the x
first coordinate of the next point

-/


-- Need to adjust such that coeff is non zero

def Poly_set' (f : PowerSeries ℚ_[p]) : Set (Prod ℤ ℝ) :=
  {((i , Padic.valuation (coeff ℚ_[p] i f)) : Prod ℤ ℝ) | ∀ i : ℕ, (coeff ℚ_[p] i f) ≠ 0}



def Poly_set'' (f : PowerSeries ℚ_[p]) : Set (Prod ℤ ℝ) :=
  {(a,b) : Prod ℤ ℝ | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f) ≠ 0 ∧ b = Padic.valuation (coeff ℚ_[p] i f)}

def Poly_set''_firstCoord (f : PowerSeries ℚ_[p]): Set ℤ :=
  {a : ℤ | ∃ (u : Poly_set'' p f), u.1 = a }


/- or define firstCoord first -/

def Poly_firstCoord (f : PowerSeries ℚ_[p]) : Set ℕ :=
  {a | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f) ≠ 0 }

noncomputable
def FirstPoint_firstentry (f : PowerSeries ℚ_[p]) : ℕ:=
  sInf (Poly_firstCoord p f)

def myset_nonempty : (Poly_firstCoord p f).Nonempty := by
  simp_rw [Poly_firstCoord]
  simp only [ne_eq, exists_eq_left']
  use 0
  -- at this point will need to give the requirement of f not having first term 0
  sorry

def myset_bddbelow : BddBelow (Poly_firstCoord p f) := by
  use 0
  intro a ha
  exact Nat.zero_le a

/-
The two above allows us to use Int.csInf_mem
-/

noncomputable
def FirstPoint1 (f : PowerSeries ℚ_[p]) : Prod ℕ ℝ :=
  (sInf (Poly_firstCoord p f), Padic.valuation (coeff ℚ_[p] (sInf (Poly_firstCoord p f)) f))

def Poly_set1 (f : PowerSeries ℚ_[p]) : Set (Prod ℕ ℝ) :=
  {(a,b) : Prod ℕ ℝ | ∃ i : ℕ, a = i ∧ (coeff ℚ_[p] i f) ≠ 0 ∧ b = Padic.valuation (coeff ℚ_[p] i f)}


noncomputable
def FirstPointinc (f : PowerSeries ℚ_[p]) : FirstPoint1 p f ∈ Poly_set1 p f := by
  sorry
--- But from here if I can adjust the definition of NextPoint we could be good.









-- alternatively if we set it up so that we always have first point (0,0)?


----- if we can switch nextpoint and the above to non-finite t we are looking good.

variable (U : Set (Prod ℝ ℝ))

def SetofSlopesNew (a : U) : Set ℝ :=
  { c  | ∃ b : t, b.1.1 > a.1.1 ∧ c = (a.1.2 - b.1.2) / (a.1.1 - b.1.1) }



noncomputable
def NextPointNew (t : Set (ℝ × ℝ)) (u : t) : t :=
  if h : ∃ b : t, b.1.1 > u.1.1 ∧ (u.1.2 - b.1.2) / (u.1.1 - b.1.1) = SetofSlopes_minimum t u
  then Classical.choose h
  else u

