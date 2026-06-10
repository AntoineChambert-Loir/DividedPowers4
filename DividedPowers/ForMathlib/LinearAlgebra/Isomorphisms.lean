/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.LinearAlgebra.Isomorphisms

-- In #40417

namespace LinearMap

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] {f : M →ₗ[R] N} (hf : Function.Surjective f)

/- @[simp]
theorem quotKerEquivOfSurjective_symm_apply (hf : Function.Surjective f) (x : M) :
    (f.quotKerEquivOfSurjective hf).symm (f x) =
      (LinearMap.ker f).mkQ x := by
  rw [← LinearMap.quotKerEquivOfSurjective_apply_mk f hf,
    @LinearEquiv.symm_apply_apply, @Submodule.mkQ_apply] -/

/-- Given a surjective `f : M →ₗ[R] N` and an `R`-module `P`, this is a bijection between `R`-linear
  maps `N →ₗ[R] P` and `R`-linear maps `g : M →ₗ[R] P` such that `ker f ≤ ker g`. -/
noncomputable def equivOfSurjective :
    (N →ₗ[R] P) ≃ {g : M →ₗ[R] P // ker f ≤ ker g} where
  toFun h := ⟨h.comp f, fun x hx ↦ by
    simp only [mem_ker, coe_comp, Function.comp_apply] at hx ⊢
    rw [hx, map_zero]⟩
  invFun := fun ⟨g, hg⟩ ↦ (Submodule.liftQ (ker f) g hg).comp
     (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  left_inv h := by
    ext n
    obtain ⟨m, rfl⟩ := hf n
    simp [f.quotKerEquivOfSurjective_symm_apply hf]
  right_inv := fun ⟨g, hg⟩ ↦ by
    ext m
    simp [f.quotKerEquivOfSurjective_symm_apply hf]

@[simp]
theorem equivOfSurjective_apply {h : N →ₗ[R] P} {m : M} :
    ((f.equivOfSurjective hf) h).1 m = h (f m) := rfl

@[simp]
theorem equivOfSurjective_symm_apply {g : M →ₗ[R] P} (hg : ker f ≤ ker g) {m : M} :
    (f.equivOfSurjective hf).symm ⟨g, hg⟩ (f m) = g m := by
  simp [equivOfSurjective]

end LinearMap
