/-
The aim of this file is to formalise results about Newton Polygons from Gouveas p-adic Numbers
-/
import Mathlib

variable (F M : Type*) [OrderedSemiring F]
variable [AddCommMonoid M] [Module F M]

variable (p : Set (Prod M F))

/-- The Newton Polygon of a set of points `p` in `Prod M F`. -/
def NewtonPolygon : Set (Prod M F) :=
    {u : Prod M F | (∃ u' : convexHull F p, u'.1 = u) ∧ (∀ (q : convexHull F p) (h : q.1.1 = u.1),
    u.2 ≤ q.1.2)}

/-
Specifcally, when `M` is `F` itself we can define slopes of the `NewtonPolygon`.
-/

variable (k : Type*) [OrderedRing k] [Field k]
variable (t : Set (Prod k k))

/-- The intersection of the set `t` in `Prod k k` and its `NewtonPolygon` it defines. This set will
define the vertex of the `NewtonPolygon`.  -/
def NewtonPolygon_breaks : Set (Prod k k) :=
    (NewtonPolygon k k t) ∩ t

/-- The next point in `NewtonPolygon_breaks` ordered by the first entry.-/
def NextPoint (l : NewtonPolygon_breaks k t) : Set (Prod k k) :=
    {u : Prod k k | (∃ u' : NewtonPolygon_breaks k t, u' = u) ∧ (u.1 > l.1.1) ∧
    (∀ (y : NewtonPolygon_breaks k t) (h : y.1.1 > l.1.1), y.1.1 ≥ u.1)}

/-- The length of a `NewtonPolygon_slope`-/
def NewtonPolygon_slope_length (l : NewtonPolygon_breaks k t) (m : NextPoint k t l) : k :=
  (m.1.2 - l.1.2)

/-- The slope of the `NewtonPolgon` of a set `t` in `Prod k k` at a point vertex `l`.-/
noncomputable
def NewtonPolygon_slope (l : NewtonPolygon_breaks k t) (m : NextPoint k t l) : k :=
  (m.1.1 - l.1.1) / (NewtonPolygon_slope_length k t l m)

/-
The use of Newton Polygons is to eventually relate them to zeros of the polynomial f; and so we
can factor out aby powers of x in our polynomial of interest so that f is of the form
  f = 1 + a1 * x + a2 * x^2 + ...
Specifically, we will have our Newton Polygon starts from the y-axis and the first slope will be of
the form y = m * x + c (and usually c will be zero)

However to keep a more general definition we could ask for the first two breaks and then consider
the equation between those points
-/

/-
Gouvea's book first considers some properties arising from the first slope
-/

def FirstPoint : Set ((Prod k k)) :=
  {u : Prod k k | (∃ u' : NewtonPolygon_breaks k t, u' = u) ∧ ∀ (y : NewtonPolygon_breaks k t),
    u.1 ≤ y.1.1}

-- Not liking how this is not working - could need to rework everything from the start so that the
-- typing works out nicer?
def FirstSlope (l : FirstPoint k t) (m : NextPoint k t l) : k := sorry

/-
The first definition we want to give from Gouvea's book is that of pure polynomials.
I think the best way will be saying `NewtonPolygon_breaks` is of size 2?
-/

/-- A polynomial `f` is `PurePoly` of slope `m` if its `NewtonPolygon` has one slope of slope `m`.-/
def PurePoly : sorry := sorry

/-
We can then give our first theorem, which says that irreducible polynomials are pure
-/
