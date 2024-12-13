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

/-- The intersection of the set `t` in `Prod k k` and its `NewtonPolygon` it defines.  -/
def Int_NP_set : Set (Prod k k) :=
    (NewtonPolygon k k t) ∩ t

/-- The next point in `Int_NP_set` along the first axis.-/
def NextPoint (l : Int_NP_set k t) : Set (Prod k k) :=
    {u : Prod k k | (∃ u' : Int_NP_set k t, u' = u) ∧ (u.1 > l.1.1) ∧
    (∀ (y : Int_NP_set k t) (h : y.1.1 > l.1.1), y.1.1 ≥ u.1)}

/-- The slope of the `NewtonPolgon` of a set `t` in `Prod k k` at a point vertex `l`.-/
noncomputable
def NP_slope (l : Int_NP_set k t) (m : NextPoint k t l) : k :=
  (m.1.1 - l.1.1) / (m.1.2 - l.1.2)
