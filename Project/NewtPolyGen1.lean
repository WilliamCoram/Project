import mathlib

variable {k : Type*}
variable [OrderedRing k] [Field k]
-- for now this is the generality I have - requirement of ordered; ring for subtraction; field for division
variable (k)
variable (t : Set (k × k))

-- Generalised ℝ to k, for some ordered field.

def NewtonPolygon_G1 : Set (Prod k k) :=
    {u : k × k | (∃ u' : convexHull k t, u'.1 = u) ∧ (∀ (q : convexHull k t) (h : q.1.1 = u.1),
    u.2 ≤ q.1.2)}

def Int_NP_set : Set (Prod k k) :=
    (NewtonPolygon_G1 k t) ∩ t


def NextPoint (l : Int_NP_set k t) : Set (Prod k k) :=
    {u : Prod k k | (∃ u' : Int_NP_set k t, u' = u) ∧ (u.1 > l.1.1) ∧
    (∀ (y : Int_NP_set k t) (h : y.1.1 > l.1.1), y.1.1 ≥ u.1)}

noncomputable
def NP_slope (l : Int_NP_set k t) (m : NextPoint k t l) : k :=
  (m.1.1 - l.1.1) / (m.1.2 - l.1.2)

-- How to write k^n??
-- Or do I want to consider someting like (Prod R k) where R is some arbitary module. And we consider
-- the slope in this module?
-- This would work by asking the module to be a normed space, then using the norm to measure the distance
-- between two points in R, we can then calculate the slope as dist(in R)/dist(in k)
-- The problem is we would require this module to be totally ordered (i.e. can escape the case of things
-- like ℂ arising; giving us no way to define NextPoint)


-- Work in progress of generalisation to k^n?
variable (K R : Type*) [OrderedSemiring K]
variable [AddCommMonoid R] [Module K R]

variable (s : Set R)

def NewtonPolygon_G2 (h : Module.rank K R = (n : ℕ)) : Set R :=
    {u : R | (∃ u' : convexHull K s, u'.1 = u) ∧ (∀ (q : convexHull K s), ((a : ℕ) < n)
    (h1 : q.1.a = u.a)), q.1.n ≤ u.n }


-- Generalisation of Prod R k idea

variable (F M : Type*) [OrderedSemiring F]
variable [AddCommMonoid M] [Module F M]

variable (p : Set (Prod M F))

def NewtonPolygon_G3 : Set (Prod M F) :=
    {u : Prod M F | (∃ u' : convexHull F p, u'.1 = u) ∧ (∀ (q : convexHull F p) (h : q.1.1 = u.1),
    u.2 ≤ q.1.2)}

-- Would I ever need to define slope in anything more than 2D??
/- NextPoint needs to be generalised in the case of a general module. Cannot use the same as in 2D
case. E.g. in R^3 what does-/

def Int_NP_set_G3 : Set (Prod M F) :=
    (NewtonPolygon_G3 F M p) ∩ p

def NextPoint_G3 (l : Int_NP_set_G3 F M p) : Set (Prod M F) :=
    {u : Prod M F | (∃ u' : Int_NP_set_G3 F M p, u' = u) ∧  sorry}
