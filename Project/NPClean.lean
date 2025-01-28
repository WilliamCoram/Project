import Mathlib

section NewtonPolygon

variable (F M L : Type*) [OrderedSemiring F] [AddCommMonoid M] [OrderedSemiring L] [Module F M]
    [Module F L]

variable (U : Set (Prod M L))

/-- NewtonPolygon via inequalities-/
def NewtonPolygon : Set (Prod M L) :=
    {u : Prod M L | (∃ u' : convexHull F U, u'.1 = u) ∧ (∀ (q : convexHull F U) (h : q.1.1 = u.1),
    u.2 ≤ q.1.2)}

/-- NewtonPolygon via sInf-/
def NewtonPolygon2 [InfSet L] : Set (Prod M L) :=
  {u : Prod M L | (∃ u' : convexHull F U, u'.1.1 = u.1) ∧
  (u.2 = sInf {v : L | ∃ v' : convexHull F U,  v'.1.1 = u.1 ∧ v = v'.1.2})}

def NewtonPolygon_breaks : Set (Prod M L) :=
    (NewtonPolygon F M L U) ∩ U

end NewtonPolygon

----------------------------------------------------------------------------------------------------

section ksquared_def

variable (k : Type*) [OrderedRing k] [Field k] [InfSet k]
variable (t : Set (Prod k k))


/- Ideas of how to do next point-/

/-- NextPoint via defintion of a set-/
def NextPoint (l : NewtonPolygon_breaks k k k t) : Set (NewtonPolygon_breaks k k k t) :=
  {u | u.1.1 > l.1.1 ∧ (∀ (y : NewtonPolygon_breaks k k k t) (h : y.1.1 > l.1.1), y.1.1 ≥ u.1.1)}

/-- NextPoint via defining their two components seperately -/
def NextPoint2_1 (a : NewtonPolygon_breaks k k k t) : k :=
  sInf {u : k | ∃ u' : NewtonPolygon_breaks k k k t, u'.1.1 = u ∧ u > a.1.1}

def NextPoint2_2 (a : NewtonPolygon_breaks k k k t) : k :=
  sorry

/-- NextPoint via combining ideas of 2 together-/
def NextPoint3 (l : NewtonPolygon_breaks k k k t) : Prod k k :=
  (sInf {u : k | ∃ u' : NewtonPolygon_breaks k k k t, u'.1.1 = u ∧ u > l.1.1} ,
  sInf {u : k | ∃ u' : NewtonPolygon_breaks k k k t,
  u'.1.1 = sInf {v : k | ∃ v' : NewtonPolygon_breaks k k k t, v'.1.1 = v ∧ v > l.1.1} ∧ u = u'.1.2})

/-- NextPoint via using a structure-/
structure nps where
  point : (Prod k k)
  myprop : Prop

/- Ideas of how to do slope_length-/

/-- Slope_length via giving l and m -/
def NewtonPolygon_slope_length (l : NewtonPolygon_breaks k k k t) (m : NextPoint k t l) : k :=
  (m.1.1.1 - l.1.1)

def NewtonPolygon_slope_length2 (a : NewtonPolygon_breaks k k k t) : k :=
  (NextPoint2_1 k t a) - a.1.1

/-- Slope length via just -/
def NewtonPolygon_slope_length3 (l : NewtonPolygon_breaks k k k t) : k :=
  (NextPoint3 k t l).1 - l.1.1

/- Ideas of how to do slope-/

noncomputable
def NewtonPolygon_slope (l : NewtonPolygon_breaks k k k t) (m : NextPoint k t l) : k :=
  (m.1.1.2 - l.1.2) / (NewtonPolygon_slope_length k t l m)

def NewtonPolygon_slope2 (l : NewtonPolygon_breaks k k k t) : k :=
  (NextPoint2_2 k t l  - l.1.1) / (NewtonPolygon_slope_length2 k t l)

def NewtonPolygon_slope3 (l : NewtonPolygon_breaks k k k t) : k :=
  ((NextPoint3 k t l).2 - l.1.2) / ((NextPoint3 k t l).1 - l.1.1)

end ksquared_def

section ksquared_firstslope

variable (k : Type*) [OrderedRing k] [Field k] [InfSet k]
variable (t : Set (Prod k k))

/- Ideas for defining the first Point-/

/-- FirstPoint via a set-/
def FirstPoint : Set (NewtonPolygon_breaks k k k t) :=
  {u | ∀ (y : NewtonPolygon_breaks k k k t), u.1.1 ≤ y.1.1}

/-- FirstPoint via explicit construction -/
def FirstPoint2 : Prod k k :=
  (sInf {u : k| ∃ u' : NewtonPolygon_breaks k k k t, u'.1.1 = u},
  sInf {u : k | ∃ u' : NewtonPolygon_breaks k k k t,
  u'.1.1 = sInf {v : k | ∃ v' : NewtonPolygon_breaks k k k t, v'.1.1 = v} ∧ u = u'.1.2} )

/- Properties of the first slope-/
noncomputable
def FirstSlope (l : FirstPoint k t) (m : NextPoint k t l) : k :=
  NewtonPolygon_slope k t l m

lemma MinValue (q : NewtonPolygon k k k t) (l : FirstPoint k t) (m : NextPoint k t l) :
    q.1.2 ≥ (((FirstSlope k t l m) * (q.1.1 - l.1.1.2)) + l.1.1.2) := by
  rw [FirstSlope, NewtonPolygon_slope, NewtonPolygon_slope_length]
  sorry

lemma SecondValue (l : FirstPoint k t) (m : NextPoint k t l):
    m.1.1.2 = (FirstSlope k t l m) * (m.1.1.1 - l.1.1.1) + l.1.1.2 := by
  rw [FirstSlope, NewtonPolygon_slope, NewtonPolygon_slope_length]
  have : m.1.1.1 - l.1.1.1 ≠ 0 := by
    sorry
  field_simp

lemma SubsequentPointsMinValue (q : NewtonPolygon k k k t) (l : FirstPoint k t)
    (m : NextPoint k t l) (h1 : q.1.1 > m.1.1.1) (n : NextPoint k t m)
    (h2 : NewtonPolygon_slope k t m n > FirstSlope k t l m):
    q.1.2 > (((FirstSlope k t l m) * (q.1.1 - l.1.1.2)) + l.1.1.2) := by
  sorry

end ksquared_firstslope
