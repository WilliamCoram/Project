import Mathlib

open PowerSeries Filter
open scoped Topology

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (c : ℝ)

structure PowerSeries_restricted_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

instance [NormedRing R] : Ring (PowerSeries_restricted_c R c) := by
  sorry

-- The withtop is needed for when we have finite points i.e. slopes are infinity.
/-
2D for now? How would I arbitrarily define slopes in non 2D?
-/
structure lowerconvexhull where
  set : Set (Prod ℝ ℝ) -- Defining set of
  points : ℕ → Prod ℝ ℝ -- function indexing vertices of the lowerconvexhull
  slopes : ℕ → EReal -- slope between i and i + 1 vertex
  relation : ∀ i : ℕ, slopes i ≠ ⊤ ∧ slopes i ≠ ⊥ →
    (points (i + 1)).2 - (points i).2 = slopes i * ((points (i + 1)).1 - (points i).1)
    -- we actually have segments touching
  slopes_increase : ∀ i : ℕ, slopes i ≤ slopes (i + 1) -- convexity condition

def Lowerconvexhull_fun : Set (Prod ℝ ℝ) → lowerconvexhull_structure :=
  sorry

/-
-- maybe this is a better definition?- could be a list of segments?
structure lowerconvexhull1 where
  set : Set (Prod ℝ ℝ)
  points : ℕ → Prod ℝ ℝ
  segments : sorry
  relation : sorry
-/

variable (f : PowerSeries_restricted_c ℚ_[p] c)

noncomputable
def fun_y : ℕ → ℤ :=
  fun i => Padic.valuation (coeff ℚ_[p] i f.function)


-------------------------- Constructing the finite set ---------------------------






--- This has to be completed at some point
def finite_set (i : ℕ) : Finset ℕ :=
  sorry

def fun_set : ℕ → Finset ℕ :=
  fun i => finite_set i


------------------- Section of a general Finset -------------------
/-
Here we define a general way to get a next point based on computing slopes from a finset of x coords
and a function giving the y values
-/
variable (V : Finset ℕ)

variable (f_y : ℕ → ℤ)
/-
If V is non-empty we will eventually define next point; if it is empty nextpoint will be the identity
-/

/-
What happens if i is in V? Can I ignore this as when showing something is a convexHull you would always
be constructing the Finsets such that i is not in its own set?
 -/
 noncomputable
def slopes (i : ℕ) : V → ℝ :=
  fun v => (f_y v - f_y i) / (v - i)

-- Maybe there is a way to include this specifically below in the def?
lemma Image_nonempty : V.Nonempty → (Finset.image (slopes V f_y i) V.attach).Nonempty := by
  simp only [Finset.image_nonempty, Finset.attach_nonempty_iff, imp_self]

-- At this point we are wanting V to be non-empty
noncomputable
def min_slope (i : ℕ) (hV : V.Nonempty) : ℝ :=
  Finset.min' ((V.attach).image (slopes V f_y i)) (Image_nonempty V f_y hV)

/-
noncomputable
def reduced_finset (i : ℕ) (hV : V.Nonempty): Finset ℕ :=
  V.filter (fun (a : ℕ) => (f_y a - f_y i) / (a - i) = min_slope V f_y i hV)

def Image_nonempty2 (hV : V.Nonempty) : (reduced_finset V f_y i hV).Nonempty := by
  rw [reduced_finset]
  apply Finset.filter_nonempty_iff.mpr
  simp_rw [min_slope]
  -- true by definition but I cannot work out the api to get this working
  sorry

noncomputable
def next_point (i : ℕ) : ℕ :=
  if hV : V.Nonempty
    then Finset.min' (reduced_finset V f_y i hV) sorry
  else i
-/

noncomputable
def next_point (i : ℕ) : ℕ :=
  if hV : V.Nonempty then
    if h : ∃ j : V, min_slope V f_y i hV = slopes V f_y i j then Nat.find h -- maybe do something like this if I can get it to work
    else i
  else i
------------------------- Return to Powerseries case --------------------------

/-
How to generate first non-zero coeff of a powerseries?
-/

-- The fun_set will need to be adjusted when I bring in the conditions on it
noncomputable
def Index_x : ℕ → ℕ
  | 0 => letI := Classical.decEq ℚ_[p]
         letI := Classical.decEq (PowerSeries ℚ_[p])
         if h : f.function = 0 then 0
         else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)
  | i + 1 => next_point (fun_set (Index_x i)) (fun_y p c f i) (Index_x i)


noncomputable
def Index_slope : ℕ → WithTop ℝ :=
  fun i => if hV : (fun_set (Index_x p c f i)).Nonempty
              then min_slope (fun_set (Index_x p c f i)) (fun_y p c f i) (Index_x p c f i) hV
           else ⊤

-- alternatively could define slopes via Index_x i and Index_x i+1

noncomputable
def NewtonPolygon : lowerconvexhull_structure where
  points := fun i => (Index_x p c f i, fun_y p c f (Index_x p c f i))
  slopes := Index_slope p c f
  relation := by
    intro i h
    ring_nf
    simp only [Pi.intCast_def, Int.cast_id, WithTop.coe_natCast, dite_mul]
    -- i see the problem with top in the api now though
    -- kill me; I want the min to just be as it is defined! there must be a lemma to manipulate this
    sorry
  slopes_increase := sorry
