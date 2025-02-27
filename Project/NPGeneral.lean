import Mathlib

structure LowerConvexHull (k : Type*) [LinearOrderedField k] where
  /-- The number of points -/
  n : ℕ
  /-- `x j` is the x-coordinate of the `j`th point when `0 ≤ j < n`. -/
  x : ℕ → k
  /-- `y j` is the y-coordinate of the `j`th point when `0 ≤ j < n`. -/
  y : ℕ → k
  /-- The x-coordinates are strictly increasing -/
  increasing : StrictMonoOn x (Set.Ico 0 n)
  /-- The Newton polygon is lower convex.
  This considers three successive points with indices `j`, `j+1` and `j+2`.
  (Replace `<` by `≤` if successive slopes are allowed to be equal). -/
  convex : ∀ j : ℕ, j + 2 < n →
      x j * y (j + 2) + x (j + 1) * y j  + x (j + 2) * y (j + 1) <
        x j * y (j + 1) + x (j + 1) * y (j + 2) + x (j + 2) * y j

namespace LowerConvexHull

variable {k : Type*} [LinearOrderedField k]

/-- The slopes of a Newton polygon. -/
def slope (U : LowerConvexHull k) (j : ℕ) : k :=
  (U.y (j + 1) - U.y j) / (U.x (j + 1) - U.x j)

/-- The segments have positive (projected) length. -/
lemma length_pos (U : LowerConvexHull k) {j : ℕ} (hj : j ∈ Set.Ico 0 (U.n - 1)) :
    0 < U.x (j + 1) - U.x j := by
  rw [sub_pos]
  simp only [Set.mem_Ico, zero_le, true_and] at hj
  refine U.increasing ?_ ?_ (lt_add_one j) <;> simp <;> omega

/-- The slopes are strictly increasing. -/
lemma slope_strictMonoOn (U : LowerConvexHull k) : StrictMonoOn U.slope (Set.Ico 0 (U.n - 1)) := by
  refine strictMonoOn_of_lt_succ Set.ordConnected_Ico ?_
  intro j hj₁ hj₂ hj₃
  simp only [slope]
  have h₁ : 0 < U.x (j + 1) - U.x j := U.length_pos hj₂
  have h₂ : 0 < U.x (j + 2) - U.x (j + 1) := U.length_pos hj₃
  simp +arith only [Nat.succ_eq_succ, Nat.succ_eq_add_one]
  rw [div_lt_div_iff₀ h₁ h₂, ← sub_pos]
  have := U.convex j (by simp at hj₃; omega)
  rw [← sub_pos] at this
  convert this using 1
  ring -- strangely, `ring` complains that it doesn't solve the goal even though it does?


------------------------------------------------------------------------------------------------


/-
If we denote a finite set S in Prod k k by f_x : ℕ → k and f_y : ℕ → k indexing their
x and y points, with x values ordered, we want to compute its LowerConvexHull
-/
variable (N : ℕ) -- Size of our finite set, i.e. only care for i < N in f_x and f_y
variable (f_x : ℕ → k) (f_y : ℕ → k) [hx : Fact (StrictMonoOn (f_x) (Set.Ico 0 N))]

/- The set of slopes out of the point indexed by i -/
def Set_of_Slopes (i : ℕ) : Set k :=
  Set.image (fun j => (f_y j - f_y i) / (f_x j - f_x i)) {j | j < N ∧ i < j}

def Set_of_Slopes_isFinite (i : ℕ): Set.Finite (Set_of_Slopes N f_y f_x i) := by
  apply Set.Finite.image
  have h2 : {j | j < N}.Finite := by
    exact Set.finite_lt_nat N
  exact Set.Finite.sep h2 (LT.lt i)

noncomputable
def Set_of_Slopes_isFinset (i : ℕ) : Finset k :=
  Set.Finite.toFinset (Set_of_Slopes_isFinite N f_y f_x i)

noncomputable
def MinSlope (i : ℕ) (Nonempty : Nonempty (Set_of_Slopes_isFinset N f_y f_x i)) : k :=
  Finset.min' (Set_of_Slopes_isFinset N f_y f_x i ) sorry -- not sure why this is not working?


noncomputable
def NextPoint (i : ℕ) : ℕ :=
  letI := Classical.propDecidable (Nonempty (Set_of_Slopes_isFinset N f_y f_x i))
  if Nonempty : Nonempty (Set_of_Slopes_isFinset N f_y f_x i) then
    letI := Classical.propDecidable
      (∃ j : ℕ, i < j ∧ j < N ∧ (f_y j - f_y i) / (f_x j - f_x i) = MinSlope N f_x f_y i Nonempty)
    if h : ∃ j : ℕ, i < j ∧ j < N ∧ (f_y j - f_y i) / (f_x j - f_x i) = MinSlope N f_x f_y i Nonempty
      then Nat.find h
     else i + 1 -- so that it is strictly mono
  else i + 1

noncomputable
def Index_x : ℕ → ℕ
  | 0 => 0
  | i + 1 => NextPoint N f_x f_y i

noncomputable
def LowerConvexHull_n (h : (∃ i,  Index_x N f_x f_y i = N - 1)) : ℕ :=
  --the final point will always be at the largest x value in the original set]
  Nat.find h + 1

noncomputable
def LowerConvexHull_set : LowerConvexHull k where
  n := have h : (∃ i,  Index_x N f_x f_y i = N - 1) := by
        sorry
    LowerConvexHull_n N f_x f_y h
  x := fun i => f_x (Index_x N f_x f_y i)
  y := fun i => f_y (Index_x N f_x f_y i)
  increasing := by
    refine StrictMono.strictMonoOn ?_ (Set.Ico 0 (LowerConvexHull_n N f_x f_y sorry))
    simp_rw [Index_x]
    refine strictMono_nat_of_lt_succ ?_
    intro r
    simp only
    cases r
    · simp only
      -- True by hx and NextPoint 0 < n
      have : NextPoint N f_x f_y 0 < n  := by
        sorry
      sorry
    · simp only
      -- this is only true for n < N, so we have lost information somewhere!
      sorry

  convex := by
    simp only
    intro i hi
    have h :
        (f_y (Index_x N f_x f_y (i+1)) - f_y (Index_x N f_x f_y i)) /
        (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)) ≤
        (f_y (Index_x N f_x f_y (i+2)) - f_y (Index_x N f_x f_y i)) /
        (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)) := by
      -- this is just showing the slope to a later point is greater; which works as both slopes are in
      -- the set of slopes and the first one is the min
      -- how to do this in lean?
      sorry
    have h1 :
        (f_y (Index_x N f_x f_y (i+1)) - f_y (Index_x N f_x f_y i)) *
        (f_x (Index_x N f_x f_y (i+2)) - f_x (Index_x N f_x f_y i)) ≤
        (f_y (Index_x N f_x f_y (i+2)) - f_y (Index_x N f_x f_y i)) *
        (f_x (Index_x N f_x f_y (i+1)) - f_x (Index_x N f_x f_y i)) := by
      -- multiply out at h
      sorry
    -- rearrange h1
    sorry

end LowerConvexHull

----------------------------------------------------------------------------------------------------
namespace NewtonPolygons

open Polynomial

variable {k : Type*} [LinearOrderedField k]
variable (f : Polynomial k)

/-
It thus remains to find `N`, `f_x`, `f_y` for polynomials, and show `f_x` is strictly mono
-/

def coeff_set : Set ℕ :=
  Set.image (fun i => i) {i | i ≤ degree f ∧ coeff f i ≠ 0 }

def coeff_set_is_finite : Set.Finite (coeff_set f) := by
  apply Set.Finite.image
  have : {i : ℕ | i ≤ degree f}.Finite := by
    cases degree f
    · simp only [le_bot_iff, WithBot.natCast_ne_bot, Set.setOf_false, Set.finite_empty]
    · exact Set.finite_lt_nat ?_ -- i am unsure how to not grey out the a†
  exact Set.Finite.sep this (fun i => coeff f i ≠ 0)

/-- The number of coefficients that have non-zero coefficients-/
noncomputable
def Polynomial_N : ℕ :=
  (coeff_set_is_finite f).toFinset.card

noncomputable
def fun_x : ℕ → ℕ
  | 0 => letI := Classical.propDecidable (∃ n : ℕ, coeff f n ≠ 0)
         if h : ∃ n : ℕ, coeff f n ≠ 0 then (Nat.find h)
         else 0
  | i + 1 => letI := Classical.propDecidable (∃ n : ℕ, coeff f n ≠ 0 ∧ n > fun_x i)
             if h : ∃ n : ℕ, coeff f n ≠ 0 ∧ n > fun_x i then (Nat.find h)
             else 0

/- There may be a better way to show that this is the inclusion of the function fun_x into k -/
/-- The function indexing the first coord of the points in the relevant set to consider -/
noncomputable
def fun_x' : ℕ → k :=
  fun i => fun_x f i

/-- fun_x is strictly increasing -/
def fun_x.isMono : (StrictMonoOn (fun_x f) (Set.Ico 0 (Polynomial_N f))) := by
  -- certainly true by construction; have coeff f fun_x (Polynomial_N f) ≠ 0 as fun_x (Polynomial_N f) = degree f
  rw [StrictMonoOn]
  simp only [Set.mem_Ico, zero_le, true_and]
  intro a ha b hb hab
  cases a
  · simp_rw [fun_x]

    sorry
  ·
    sorry


/-- The function indexing the second coord of the points in the relevant set to consider-/
noncomputable
def fun_y : ℕ → k :=
  fun i => coeff f (fun_x f i)
