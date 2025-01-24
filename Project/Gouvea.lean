/-
The aim of this file is to formalise results about Newton Polygons from Gouveas p-adic Numbers
-/
import Mathlib

variable (F M L : Type*) [OrderedSemiring F]
variable [AddCommMonoid M] [OrderedSemiring L] [Module F M] [Module F L] [InfSet L]

variable (p : Set (Prod M L))

/-- The Newton Polygon of a set of points `p` in `Prod M L`. -/
def NewtonPolygon : Set (Prod M L) :=
    {u : Prod M L | (∃ u' : convexHull F p, u'.1 = u) ∧ (∀ (q : convexHull F p) (h : q.1.1 = u.1),
    u.2 ≤ q.1.2)}


-- Another way to write NewtonPolygon? Not sure if it is nicer??
def NewtonPolygon2 : Set (Prod M L) :=
  {u : Prod M L | (∃ u' : convexHull F p, u'.1.1 = u.1) ∧
  (u.2 = sInf {v : L | ∃ v' : convexHull F p,  v'.1.1 = u.1 ∧ v = v'.1.2})}

/-
Specifcally, when `M` is `F` itself we can define slopes of the `NewtonPolygon`.
-/

variable (k : Type*) [OrderedRing k] [Field k] [InfSet k]
variable (t : Set (Prod k k))

/-- The intersection of the set `t` in `Prod k k` and its `NewtonPolygon` it defines. This set will
define the vertex of the `NewtonPolygon`.  -/
def NewtonPolygon_breaks : Set (Prod k k) :=
    (NewtonPolygon k k k t) ∩ t

/-
Can I rewrite the following such that it is only a single point? I guess this allows it to be empty?
This will also allow me to remove NextPoints as a hypothesis?
-/
/-- The next point in `NewtonPolygon_breaks` ordered by the first entry.-/
def NextPoint (l : NewtonPolygon_breaks k t) : Set (NewtonPolygon_breaks k t) :=
  {u | u.1.1 > l.1.1 ∧ (∀ (y : NewtonPolygon_breaks k t) (h : y.1.1 > l.1.1), y.1.1 ≥ u.1.1)}


-------------- Testing


-- Idea for removing dependency of NextPoint being a set?? What happens in non discrete sets??????

def NextPoint2 (l : NewtonPolygon_breaks k t) : Set (Prod k k) :=
  {u | ∃ u' : NewtonPolygon_breaks k t, u'.1 = u ∧ u.1 > l.1.1}

def NextPoint2_1 (l : NewtonPolygon_breaks k t) : Set k :=
  {u | ∃ u' : NextPoint2 k t l, u'.1.1 = u}

def NewtonPolygon_slope_length2 (l : NewtonPolygon_breaks k t) : k :=
  (sInf (NextPoint2_1 k t l)) - l.1.1

-- Why not take it a step further

def NextPoint3 (l : NewtonPolygon_breaks k t) : Prod k k :=
  (sInf {u : k | ∃ u' : NewtonPolygon_breaks k t, u'.1.1 = u ∧ u > l.1.1} ,
  sInf {u : k | ∃ u' : NewtonPolygon_breaks k t,
  u'.1.1 = sInf {v : k | ∃ v' : NewtonPolygon_breaks k t, v'.1.1 = v ∧ v > l.1.1} ∧ u = u'.1.2})

def NewtonPolygon_slope_length3 (l : NewtonPolygon_breaks k t) : k :=
  (NextPoint3 k t l).1 - l.1.1

def NewtonPolygon_slope3 (l : NewtonPolygon_breaks k t) : k :=
  ((NextPoint3 k t l).2 - l.1.2) / ((NextPoint3 k t l).1 - l.1.1)



------------------


/-- The length of a `NewtonPolygon_slope`-/
def NewtonPolygon_slope_length (l : NewtonPolygon_breaks k t) (m : NextPoint k t l) : k :=
  (m.1.1.1 - l.1.1)

/-- The slope of the `NewtonPolgon` of a set `t` in `Prod k k` at a point vertex `l`.-/
noncomputable
def NewtonPolygon_slope (l : NewtonPolygon_breaks k t) (m : NextPoint k t l) : k :=
  (m.1.1.2 - l.1.2) / (NewtonPolygon_slope_length k t l m)

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

def FirstPoint : Set (NewtonPolygon_breaks k t) :=
  {u | ∀ (y : NewtonPolygon_breaks k t), u.1.1 ≤ y.1.1}

noncomputable
def FirstSlope (l : FirstPoint k t) (m : NextPoint k t l) : k :=
  NewtonPolygon_slope k t l m

/-
At this point we can give some information about the first slope
-/

/-- Points in the NewtonPolygon lie 'above' the first slope.-/
lemma MinValue (q : NewtonPolygon k k k t) (l : FirstPoint k t) (m : NextPoint k t l) :
    q.1.2 ≥ (((FirstSlope k t l m) * (q.1.1 - l.1.1.2)) + l.1.1.2) := by
  rw [FirstSlope, NewtonPolygon_slope, NewtonPolygon_slope_length]
  sorry
/-
The following lemma seems pointless?
-/
lemma SecondValue (l : FirstPoint k t) (m : NextPoint k t l):
    m.1.1.2 = (FirstSlope k t l m) * (m.1.1.1 - l.1.1.1) + l.1.1.2 := by
  rw [FirstSlope, NewtonPolygon_slope, NewtonPolygon_slope_length]
  have : m.1.1.1 - l.1.1.1 ≠ 0 := by
    sorry -- follows from definitions
  field_simp

/-
h2 is included to reduce to the case where the second slope is indeed different.
-/

lemma SubsequentPointsMinValue (q : NewtonPolygon k k k t) (l : FirstPoint k t)
    (m : NextPoint k t l) (h1 : q.1.1 > m.1.1.1) (n : NextPoint k t m)
    (h2 : NewtonPolygon_slope k t m n > FirstSlope k t l m):
    q.1.2 > (((FirstSlope k t l m) * (q.1.1 - l.1.1.2)) + l.1.1.2) := by
  sorry

/- Gouvea has 'y'-coords as p-adic valuations of coefficienets; but this fact should not matter in
lean, and it should be okay defined as is - i.e. the set can be defined via taking the p-adic
valuations. -/

/- At this point we can state and prove a version of the Weierstrass preparation theorem for
polynomials.-/

/- Will need to give Theorem 6.2.1 first-/

open Polynomial

/-
Firstly, need to replace ℝ[X] with F[X] for F some complete extension of Q_p
-/

def Set1 (f : ℚ[X]) (p : ℕ) (c : ℝ) : Set ℝ :=
  {padicValRat p (coeff f i) * c^i | (i : ℕ)}

/- Not needed if sSup works as intended??
def Set2 (f : ℚ[X]) (p : ℕ) (c : ℝ) : Set ℝ :=
  {u | (∃ u' : Set1 f p c, u'.1 = u) ∧ (∀ v : Set1 f p c, u ≥ v.1)}
-/

noncomputable
def NonArchimedeanAbsVal_c (c : ℝ) (p : ℕ) : AbsoluteValue ℚ[X] ℝ where
  toFun := fun f => sSup (Set1 f p c)
  map_mul' := sorry
  nonneg' := sorry
  eq_zero' := sorry
  add_le' := sorry



/-- Prop 6.2.3 in Gouvea. -/
lemma WeierstrassPrepThmPolynomials (c : ℝ): 0 = 0 := by
  sorry



/-
The first definition we want to give from Gouvea's book is that of pure polynomials, question is how
to differentiate between slopes of the same slope.
-/

/-- A polynomial `f` is `PurePoly` of slope `m` if its `NewtonPolygon` has one slope of slope `m`.-/
def PurePoly : sorry := sorry

/-
We can then give our first theorem, which says that irreducible polynomials are pure
-/
