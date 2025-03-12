import Mathlib


variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

open PowerSeries Filter
open scoped Topology

/-- Restricted powerseries, are those that convergence on the disk... -/
structure RestrictedPowerSeries_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence' : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

variable (R : Type*) [NormedRing R] (c : ℝ)

instance (c : ℝ) : CoeOut (RestrictedPowerSeries_c R c) (PowerSeries R) where
  coe f := f.function

@[ext]
theorem ext_RPS {R : Type*} [NormedRing R] {c : ℝ} (f g : RestrictedPowerSeries_c R c) :
    f.function = g.function → f = g := by
  intro h
  cases f; cases g
  congr

noncomputable
instance add (hc : 0 < c): Add (RestrictedPowerSeries_c R c) :=
  ⟨fun f g => {function := f.function + g.function
               convergence' := by
                obtain ⟨f, hf⟩ := f
                obtain ⟨g, hg⟩ := g
                simp only [map_add]
                have h1 : ∀ (t : ℕ), 0 ≤ ‖(coeff R t) f + (coeff R t) g‖ * c ^ t := by
                  intro t
                  have : 0 < c^t := by
                    exact pow_pos hc t
                  exact mul_nonneg (norm_nonneg _) (le_of_lt this)
                have h2 : ∀ (t : ℕ), ‖(coeff R t) f + (coeff R t) g‖ * c ^ t ≤ ‖coeff R t f‖ * c^t +
                    ‖coeff R t g‖ * c^t := by
                  intro t
                  have := mul_le_mul_of_nonneg_right (norm_add_le (coeff R t f) (coeff R t g)) (le_of_lt (pow_pos hc t))
                  rw [RightDistribClass.right_distrib] at this
                  exact this
                have h3 : Tendsto (fun t ↦ ‖(coeff R t) f‖ * c ^ t + ‖(coeff R t) g‖ * c ^ t) atTop (𝓝 0) := by
                  have := Tendsto.add hf hg
                  simp only [add_zero] at this
                  exact this
                exact squeeze_zero h1 h2 h3}⟩

instance [NormedRing R] (c : ℝ) (hc : 0 < c) : Ring (RestrictedPowerSeries_c R c) where
  add := (add R c hc).add
  add_comm {f g} := by
    ext i
    simp only [add] -- why??
    exact add_comm (f.function) (g.function)

  add_assoc := sorry
  zero := ⟨0, sorry⟩
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  mul := fun f g => ⟨f.function * g.function, sorry⟩
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := ⟨1, sorry⟩
  one_mul := sorry
  mul_one := sorry
  neg := fun f => ⟨-f.function, sorry⟩
  neg_add_cancel := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  npow_zero := sorry
  npow_succ := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  intCast_negSucc := sorry
