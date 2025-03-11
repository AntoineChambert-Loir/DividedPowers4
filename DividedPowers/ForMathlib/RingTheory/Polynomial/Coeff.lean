/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Polynomial.Coeff

namespace Polynomial

open Ring

variable {R : Type*} [Semiring R]

theorem C_eq_smul_one  {a : R} : (C a : Polynomial R) = a • (1 : Polynomial R) := by
  rw [← C_mul', mul_one]

theorem inv_C_eq_C_inv {a : R} : inverse (C a) = C (inverse a) := by
  simp only [inverse]
  by_cases ha : IsUnit a
  · have hCa : IsUnit (C a) := by
      rw [← IsUnit.unit_spec ha]
      exact RingHom.isUnit_map C ha
    rw [dif_pos ha, dif_pos hCa]
    apply IsUnit.mul_right_cancel hCa
    simp only [← map_mul, IsUnit.val_inv_mul, map_one]
  · simp only [inverse, dif_neg ha, map_zero]
    rw [dif_neg]
    intro hCa
    apply ha
    rw [isUnit_iff_exists_and_exists] at hCa ⊢
    obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := hCa
    exact ⟨⟨b.coeff 0, by rw [← coeff_C_mul, hb, coeff_one_zero]⟩,
      ⟨c.coeff 0, by rw [← coeff_mul_C, hc, coeff_one_zero]⟩⟩

end Polynomial
