import mathlib

/-
Convex hulls are already defined in lean. The first step at defining a Newton polygon
could be achieved by defining the boundary of the convex hull?
-/
section General


variable {k E F : Type*}

variable [OrderedSemiring k]
variable (k)
variable [AddCommMonoid E] [AddCommMonoid F] [Module k E] [Module k F]

variable (s : Set E)

variable (t : Set (ℝ × ℝ))

/-- The Newton Polygon of a set in `ℝ × ℝ`.-/
def test3 : Set (ℝ × ℝ) :=
    {u : ℝ × ℝ | (∃ u' : convexHull ℝ t, u'.1 = u) ∧ (∀ (q : convexHull ℝ t) (h : q.1.1 = u.1),
    u.2 ≤ q.1.2)}

/-- The intersection of the Newton Polygon with the defining set `t`.-/
def Int_NP_set : Set (ℝ × ℝ) :=
    (test3 t) ∩ t


/- These definitions are unused for now.
def Pos_Int_NP_set : Set (ℝ × ℝ) :=
    {u : ℝ × ℝ | ∃ u' : Int_NP_set t, u' = u ∧ u.1 ≥ 0}

def Neg_Int_NP_set : Set (ℝ × ℝ) :=
    {u : ℝ × ℝ | ∃ u' : Int_NP_set t, u' = u ∧ u.1 ≤ 0}
-/

noncomputable
def slopey (x y : (ℝ × ℝ)) : ℝ :=
    (x.1 - y.1)/(x.2 - y.2)

-- Defining the next point in the set, I am unhappy with this definition as it gives a set, not a
-- single point. Obviously it will be single though - for now leaving like this, may need to
-- rewrite and/or write a lemma saying this has size 1.

def NextPoint (l : Int_NP_set t) : Set (ℝ × ℝ) :=
    {u : ℝ × ℝ | (∃ u' : Int_NP_set t, u' = u) ∧ (u.1 > l.1.1) ∧
    (∀ (y : Int_NP_set t) (h : y.1.1 > l.1.1), y.1.1 ≥ u.1)}

noncomputable
def NP_slope (l : Int_NP_set t) (m : NextPoint t l) : ℝ :=
    slopey l m.1

end General
