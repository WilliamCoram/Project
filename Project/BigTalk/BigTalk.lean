import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-- How lean reads math -/
example (a b c : ℕ) : a + b + c = (a + b) + c := by
  rfl

/-- Commutativity of addition -/
def add_comm' (a b : ℕ) : a + b = b + a := by

  sorry

/-- Associativity of addition -/
def add_assoc' (a b c : ℕ) : a + b + c = a + (b + c) := by
  exact Nat.add_assoc a b c
  sorry

example (a b c : ℕ) : a + b + c = a + c + b := by
  ring


open Complex UpperHalfPlane

open scoped Topology Manifold MatrixGroups


#check SlashAction
#check ModularForm.slash
#check SlashInvariantForm
#check ModularForm
#check ModularForm.eisensteinSeries_MF

variable (Γ : Subgroup SL(2,ℤ)) (k : ℤ)

def Zero_MF : ModularForm Γ k where
  toFun := 0
  slash_action_eq' := by

    --apply?
    exact fun γ a ↦ SlashAction.zero_slash k γ

  holo' := by

  bdd_at_infty' := by
    sorry
