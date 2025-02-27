import Mathlib

variable (c : ℝ) (p : ℕ) [hp : Fact (Nat.Prime p)]

open PowerSeries Filter
open scoped Topology

/-- Restricted powerseries, are those that convergence on the disk... -/
structure RestrictedPowerSeries_c (R : Type*) (c : ℝ) [NormedRing R] where
  function : PowerSeries R
  convergence' : Tendsto (fun (i : ℕ) => (norm (coeff R i function)) * c^i) atTop (𝓝 0)

/-
Copying Chris' work on Modular forms as it is a similar structure
Worry that I have PowerSeries R and (Unit →₀ ℕ) → R at different times?
-/

variable (R : Type*) [NormedRing R] (c : ℝ)

class RestrictedPowerSeries_Class (F : Type*) [FunLike F (Unit →₀ ℕ) R] : Prop where
  convergence : ∀ (f : F), Tendsto (fun (i : ℕ) =>
      (norm (coeff R i (f : (Unit →₀ ℕ) → R))) * c^i) atTop (𝓝 0)

instance RestrictedPowerSeries.funLike :
    FunLike (RestrictedPowerSeries_c R c) (Unit →₀ ℕ) R where
  coe := fun f => f.function
  coe_injective' f g h := by cases f; cases g; congr

instance RestrictedPowerSeries_Class.RestrictedPowerSeries :
  (RestrictedPowerSeries_Class R c) (RestrictedPowerSeries_c R c) where
  convergence := fun f => f.convergence'

@[simp]
theorem RestrictedPowerSeries.function_eq_coe (f : RestrictedPowerSeries_c R c) : f.function =
    (f : (Unit →₀ ℕ) → R) := rfl

@[simp]
theorem RestrictedPowerSeries.coe_mk (f : PowerSeries R) (hf : Tendsto (fun (i : ℕ) =>
    (norm (coeff R i f)) * c^i) atTop (𝓝 0)) : ⇑(RestrictedPowerSeries_c.mk f hf) = f := rfl

@[ext]
theorem RestrictedPowerSeries.ext {f g : RestrictedPowerSeries_c R c} (h : ∀ x, f x = g x) :
    f = g :=
  DFunLike.ext f g h

def RestrictedPowerSeries_c.copy (f : RestrictedPowerSeries_c R c) (f' : PowerSeries R)
    (h : f' = ⇑f) : RestrictedPowerSeries_c R c where
  function := f'
  convergence' := h.symm ▸ f.convergence'


namespace RestrictedPowerSeries

noncomputable
instance add (hc : 0 < c) : Add (RestrictedPowerSeries_c R c) :=
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
                  have := mul_le_mul_of_nonneg_right (norm_add_le (coeff R t f) (coeff R t g))
                     (le_of_lt (pow_pos hc t))
                  rw [RightDistribClass.right_distrib] at this
                  exact this
                have h3 : Tendsto (fun t ↦ ‖(coeff R t) f‖ * c ^ t + ‖(coeff R t) g‖ * c ^ t) atTop (𝓝 0) := by
                  have := Tendsto.add hf hg
                  simp only [add_zero] at this
                  exact this
                exact squeeze_zero h1 h2 h3}⟩

@[simp]
theorem coe_add (hc : 0 < c) (f g : RestrictedPowerSeries_c R c) : ⇑(f + g) = f + g :=
  rfl

/--/

def zero : RestrictedPowerSeries_c R c hc:=
  {function := 0, convergence := by
              simp only [map_zero, norm_zero, zero_mul, tendsto_const_nhds_iff] }

noncomputable
def one : RestrictedPowerSeries_c R c hc :=
  {function := 1, convergence := by
    simp only [coeff_one]
    intro ε
    intro hε
    simp only [mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
    use 1
    intro b hb
    have h : ‖((if b = 0 then 1 else 0) : R)‖ * c ^ b = 0 := by
      simp only [mul_eq_zero, norm_eq_zero, ite_eq_right_iff, pow_eq_zero_iff', ne_eq]
      left
      intro h
      contrapose h
      simp_rw [← ne_eq]
      exact Nat.not_eq_zero_of_lt hb
    simp only [h, sub_zero, norm_zero, mul_zero, zero_mul, sub_self]
    exact mem_of_mem_nhds hε
  }



instance [NormedRing R] : Ring (RestrictedPowerSeries_c R c hc) where
  zero := zero R c
  one := one R c
  add f g := {function := f.function + g.function, convergence := by
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
                  have := mul_le_mul_of_nonneg_right (norm_add_le (coeff R t f) (coeff R t g))
                     (le_of_lt (pow_pos hc t))
                  rw [RightDistribClass.right_distrib] at this
                  exact this
                have h3 : Tendsto (fun t ↦ ‖(coeff R t) f‖ * c ^ t + ‖(coeff R t) g‖ * c ^ t) atTop (𝓝 0) := by
                  have := Tendsto.add hf hg
                  simp only [add_zero] at this
                  exact this
                exact squeeze_zero h1 h2 h3
              }
