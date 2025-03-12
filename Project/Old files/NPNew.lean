import Mathlib

open PowerSeries Filter
open scoped Topology

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (c : ℝ)

structure PowerSeries_restricted_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

instance [NormedRing R] : Ring (PowerSeries_restricted_c R c) := by
  sorry

structure lowerconvexhull_R2 where
  set : Set (Prod ℝ ℝ) -- Defining set of the lch
  points : ℕ → Prod ℝ ℝ -- function indexing vertices of the lch
  slopes : ℕ → EReal -- slope between i and i + 1 vertex
  relation : ∀ i : ℕ, slopes i ≠ ⊤ ∧ slopes i ≠ ⊥ →
    (points (i + 1)).2 - (points i).2 = slopes i * ((points (i + 1)).1 - (points i).1)
    -- we actually have segments touching
  slopes_increase : ∀ i : ℕ, slopes i ≤ slopes (i + 1) -- convexity condition

variable (f : PowerSeries_restricted_c ℚ_[p] c)

noncomputable
def fun_y : ℕ → ℤ :=
  fun i => Padic.valuation (coeff ℚ_[p] i f.function)

variable (f_y : ℕ → ℤ)

/-
Two new ideas to approach this:
1: Consider the limit of the sequence (ν(a_i) - ν(a_j))/(i - j) and do cases on what this is
   e.g. If ∞, by convergence we can construct our finite sets such the slope is smaller than N
        If -∞ we choose NP as vertical line down
        If empty set, choose vertical line up
        If a : subcases based on what this sequence is. i.e.
               If its an eventually increasing sequence then there exists finite set.
               If its an eventually decreasing set then we take the slope as a and choose next point as i+1
               If neither then just use convergence as usual to get a finite set (think this is possible?)

2: Consider the Infimum of the set of slopes and do cases
   e.g. If -∞, then take vertical line down
        If exists: subcases of
                   Attained by value. Choose minimum of bdd below indexing set of attaining i
                   Notattained. Then choose slope and choose nextpoint as i+1
        If empty set, take vertical line up
        (The infimum cannot not exist? assuming we are allowing a bot.)
-/

---------------------------------- Idea 1 ------------------------------------

def set_greater (i : ℕ) : Set ℕ :=
  {a | i < a }

noncomputable
def slope_fun (i : ℕ) : set_greater i → ℝ :=
  fun a => (f_y a - f_y i)/(a - i)

-- Now want to consider the limit of this sequence


---------------------------------- Idea 2 ------------------------------------

/-
Can I define this in a total general sense that works. e.g. for now this will not be correct for
powerseries as we need to restrict to set_of_slopes when coeff is not zero

Maybe Set ℕ
      Set ℕ → ℝ (slopes at i)
      Either Set ℝ (set of slopes from image of above map) or use Range of the map
      NextPoint as below

      i.e. for PowerSeries, will define Set ℕ as the later points with non-zero coeff
           for just Sets of points, just use their later coords

           .. the idea is that NextPoint will be dependant on the initial set
-/

variable (S : Set ℕ) -- this is our general step, this will be the relevant one for each case

def set_of_slopes1 (i : ℕ) : Set ℝ :=
  {m | ∃ j : S, m = ((f_y j - f_y i) : ℝ)/((j-i) : ℝ)}

def set' (i : ℕ) : Set EReal :=
  {m | ∃ a : set_of_slopes1 f_y S i, a = m}

noncomputable
def min_slope1 (i : ℕ) : EReal :=
  sInf (set' f_y S i)

noncomputable
instance Dec1 (i : ℕ) : Decidable (set' f_y S i).Nonempty :=
  Classical.propDecidable (set' f_y S i).Nonempty

noncomputable
instance Dec2 (i : ℕ) : Decidable (∃ j : ℕ, ∃ s : S, j = s ∧ min_slope1 f_y S i = ((f_y s - f_y i) : ℝ)/((s-i) : ℝ)) :=
  Classical.propDecidable (∃ j : ℕ, ∃ s : S, j = s ∧ min_slope1 f_y S i = ((f_y s - f_y i) : ℝ)/((s-i) : ℝ))

noncomputable
def NextPoint1 (i : ℕ) : ℕ :=
  if h : (set' f_y S i).Nonempty then
    if h1 : min_slope1 f_y S i = ⊤ ∨ min_slope1 f_y S i = ⊥ then i
    else if h2 : ∃ j : ℕ, ∃ s : S, j = s ∧ min_slope1 f_y S i = ((f_y s - f_y i) : ℝ)/((s-i) : ℝ) then Nat.find h2
         else i + 1
  else i


/-
I am not sure if using EReal is 'correct' could use WithTop WithBot and coercions where needed?
-/

noncomputable
def fun_y : ℕ → ℤ :=
  fun i => Padic.valuation (coeff ℚ_[p] i f.function)

def set_of_slopes (i : ℕ) : Set EReal :=
  {m : EReal | ∃ (j : ℕ), i < j ∧ m = ((f_y j - f_y i) : ℝ)/((j-i) : ℝ) ∧ coeff ℚ_[p] j f.function ≠ 0 }

noncomputable
def min_slope (i : ℕ) : EReal :=
  sInf (set_of_slopes p c f f_y i)

noncomputable
instance decidableSetOfSlopesNonempty (i : ℕ) : Decidable (set_of_slopes p c f f_y i).Nonempty :=
  Classical.propDecidable _

noncomputable
instance dec1 (i : ℕ) : Decidable (∃ j : ℕ, i < j ∧ min_slope p c f f_y i = ((f_y j - f_y i) : ℝ)/((j - i) : ℝ)) := by
  exact Classical.propDecidable (∃ j : ℕ, i < j ∧ min_slope p c f f_y i = ((f_y j - f_y i) : ℝ)/((j - i) : ℝ))

noncomputable
def NextPoint (i : ℕ) : ℕ :=
  if h : (set_of_slopes p c f f_y i).Nonempty then -- so there is something to take an inf of
    (if h1 : min_slope p c f f_y i = ⊥ ∨ min_slope p c f f_y i = ⊤ then i -- case of slope being either vertical line (⊤ is impossible)
      else if h2 : ∃ j : ℕ, i < j ∧ min_slope p c f f_y i = ((f_y j - f_y i) : ℝ)/((j - i) : ℝ) then Nat.find h2 -- inf is attained
              else i) -- inf is not attained
    else i  -- empty set_of_slopes; i.e. we have reached the last point


noncomputable
def Index_x : ℕ → ℕ
  | 0 => letI := Classical.decEq ℚ_[p]
         letI := Classical.decEq (PowerSeries ℚ_[p])
         if h : f.function = 0 then 0
         else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)
  | i + 1 => NextPoint p c f (fun_y p c f) i

-- what happens if min_slope is ⊤... this does not make any sense; as ⊤ cannot be in set_of_slopes. But does lean know this
noncomputable
def Index_slope : ℕ → EReal :=
  fun i => if h : (set_of_slopes p c f f_y i).Nonempty then min_slope p c f (fun_y p c f) i
            else ⊤

def NewtonPolygon : lowerconvexhull_R2 where
  points := fun i => ((Index_x p c f i), fun_y p c f (Index_x p c f i))
  slopes := fun i => Index_slope p c f (fun_y p c f) (Index_x p c f i)
  relation := by
    intro i h
    obtain ⟨h1, h2⟩ := h
    have : Index_slope p c f (fun_y p c f) ≠ ⊤ →
    sorry

  slopes_increase := sorry


  /-
  Is our idea now to adjust i+1 to i and keep slope as whatever but need to intuitvely realise the NP is a line

  Or create the NewtonPolygon of a powerseries as a family of newtonPolygons of its truncated polynomials.
  -/
