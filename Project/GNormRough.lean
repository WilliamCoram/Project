/-
The aim of this file is to formalise results about Newton Polygons from Gouveas p-adic Numbers
-/
import Mathlib

open Polynomial

/-
Firstly, need to replace ℝ[X] with F[X] for F some complete extension of Q_p
-/


-- May need to be chagning to supremum of finite sets?? As this would make it easier?
variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable
def cnorm : ℚ[X] → ℝ :=
  fun f => sSup {padicNorm p (coeff f i) * c^i | (i : ℕ)}

instance cnorm'_finite : Fintype {x | ∃ i : ℕ, i ≤ degree f ∧ padicNorm p (coeff f i) * c^i = x} := by
  sorry

def myfinset (f :  ℚ[X]) : Finset ℝ := Set.toFinset {x | ∃ i : ℕ, i ≤ degree f ∧ padicNorm p (coeff f i) * c^i = x}

noncomputable def cnorm' : ℚ[X] → WithBot ℝ :=
  fun f => Finset.max (myfinset c p f) --{x | ∃ i : ℕ, i ≤ degree f ∧ padicNorm p (coeff f i) * c^i = x}

def cnorm_existance : ∃ j : ℕ, j ≤ degree f ∧ sSup {padicNorm p (coeff f i) * c^i | (i : ℕ)} = padicNorm p (coeff f j) * c^j := by

  sorry

variable (k : ℕ)

theorem afinset : Set.Finite { (i, j) : Prod ℕ ℕ | i + j = k} := by
  sorry
