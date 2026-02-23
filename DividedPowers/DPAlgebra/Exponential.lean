/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.Init
import DividedPowers.ExponentialModule.Basic
import DividedPowers.ForMathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Divided power algebra and exponential modules

Here we prove Theorem III.1 of [Roby1963]: let `R` be a commutative ring, `M` be an `R`-module and
`A` be an `R`-algebra.
There is an equivalence between
* algebra morphisms `α : DividedPowerAlgebra R M →ₐ[R] A`
* module morphisms `β : M →ₗ[R] ExponentialModule A`
which satisfies `β m = ∑ α ( dp n m ) X ^ n` `for all m : M`.

## Main definitions/results

* `DividedPowerAlgebra.exp` : The exponential power series of an element `m : M` is the power
  series `∑ (dp n m) X ^ n`, in the `ExponentialModule` of `DividedPowerAlgebra R M`.

* `DividedPowerAlgebra.exponentialModule_equiv`: the equivalence between algebra morphisms
  `DividedPowerAlgebra R M →ₐ[R] S` and linear maps `M →ₗ[R] ExponentialModule S`.
  This is [Roby1963, theorem III.1]

-/

variable (R : Type*) [CommRing R] {A : Type*} [CommSemiring A] [Algebra R A]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

namespace DividedPowerAlgebra

open PowerSeries Additive ExponentialModule

/-- The exponential power series of an element of a module, in the DividedPowerAlgebra -/
noncomputable def exp' (m : M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dp R n m)

lemma coeff_exp' (m : M) (n : ℕ) : coeff n (exp' R m) = dp R n m := by
  simp only [coeff_mk, exp']

theorem isExponential_exp' (m : M) : IsExponential (exp' R m) := by
  rw [isExponential_iff]
  constructor
  · intro p q
    simp only [coeff_exp', dp_mul, nsmul_eq_mul]
  · rw [← coeff_zero_eq_constantCoeff, coeff_exp', dp_zero]

/-- The exponential power series of an element of a module,
  in the ExponentialModule of the DividedPowerAlgebra -/
noncomputable def exp (m : M) : ExponentialModule (DividedPowerAlgebra R M) :=
  ⟨ofMul (exp' R m), isExponential_exp' R m⟩

theorem coe_exp (m : M) : ↑(exp R m) = exp' R m := rfl

theorem coeff_exp (m : M) (n : ℕ) : coeff n (exp R m) = dp R n m := by
  simp only [coe_exp, coeff_exp']

-- TODO: The following could serve as a definition of an exponential structure
-- this is equivalent to the combination of dpow_zero, dpow_add and dpow_smul

variable (M) in
/-- The exponential power series of an element of a module, valued in the ExponentialModule of the
  DividedPowerAlgebra, as a LinearMap -/
noncomputable def exp_LinearMap :
    M →ₗ[R] ExponentialModule (DividedPowerAlgebra R M) where
  toFun := exp R
  map_add' x y := by
    apply coe_injective
    ext n
    simp only [ExponentialModule.coe_add, coeff_exp, coeff_mul, dp_add]
  map_smul' r m := by
    apply coe_injective
    ext n
    simp only [coeff_exp, RingHom.id_apply]
    rw [← algebraMap_smul (DividedPowerAlgebra R M) r (exp R m), coe_smul, coeff_rescale, coeff_exp,
      ← map_pow, dp_smul, Algebra.algebraMap_self, RingHom.id_apply,Algebra.smul_def, map_pow]


theorem coe_exp_LinearMap : ⇑(exp_LinearMap R M) = exp R := rfl

theorem coeff_exp_LinearMap (n : ℕ) (m : M) :
    coeff n (exp_LinearMap R M m) = dp R n m := by
  rw [coe_exp_LinearMap, coeff_exp]

variable {S : Type*} [CommRing S] [Algebra R S]

variable (M S) in

/-- The equivalence between algebra morphisms `DividedPowerAlgebra R M →ₐ[R] S` and
  linear maps `M →ₗ[R] ExponentialModule S`. This is [Roby1963, theorem III.1] -/
noncomputable
def exponentialModule_equiv :
    (DividedPowerAlgebra R M →ₐ[R] S) ≃ (M →ₗ[R] ExponentialModule S) where
  toFun α := (linearMap α).comp (exp_LinearMap R M)
  invFun β := by
    apply DividedPowerAlgebra.lift' (f := fun (n, m) ↦ coeff n (β m))
    · intro m
      simp only [coeff_zero_eq_constantCoeff]
      exact constantCoeff_coe (β m)
    · intro n r m
      simp only [LinearMapClass.map_smul, coe_smul, coeff_rescale]
      rw [Algebra.smul_def, map_pow]
    · intro n p m
      simp only [nsmul_eq_mul]
      rw [(isExponential_iff.mp (isExponential_coe _)).1]
    · intro n x y
      simp only [map_add, coe_add, coeff_mul]
  left_inv := by
    intro α
    simp only [LinearMap.coe_comp, Function.comp_apply]
    apply algHom_ext
    intro n m
    simp [lift'_apply_dp, coeff_linearMap, coeff_exp_LinearMap]
  right_inv := by
    intro β
    ext m n
    simp [Function.comp_apply, coeff_linearMap, coeff_exp_LinearMap, lift'_apply_dp]

variable {R}

theorem exponentialModule_equiv_apply (α : DividedPowerAlgebra R M →ₐ[R] S) :
    exponentialModule_equiv R M S α = (linearMap α).comp (exp_LinearMap R M) := rfl

theorem exponentialModule_equiv_symm_apply
    (β : M →ₗ[R] ExponentialModule S) (n : ℕ) (m : M) :
    (exponentialModule_equiv R M S).symm β (dp R n m) = coeff n (β m) := by
  unfold exponentialModule_equiv
  simp only [Equiv.coe_fn_symm_mk, lift'_apply_dp]

end DividedPowerAlgebra

variable (R : Type*) [CommRing R] {A : Type*} [CommSemiring A] [Algebra R A]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

namespace DividedPowerAlgebra

open PowerSeries Additive ExponentialModule


variable {S : Type*} [CommRing S] [Algebra R S]

section quotient

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (hf : Function.Surjective f)

/-- The kernel of the canonical map from `DividedPowerAlgebra R M`
to `DividedPowerAlgebra R N` associated with a surjective linear map
from `M` to `N`. -/
def kerLift : Ideal (DividedPowerAlgebra R M) := Ideal.span
  (Set.range (fun (nq : PNat × (LinearMap.ker f)) ↦ dp R nq.1 (nq.2 : M)))

noncomputable def quotientEquiv_toAlgHom :
    DividedPowerAlgebra R M ⧸ (kerLift f) →ₐ[R] DividedPowerAlgebra R N := by
  apply Ideal.Quotient.liftₐ (kerLift f) (LinearMap.lift R f)
  suffices kerLift f ≤  RingHom.ker (LinearMap.lift R f) by
    exact fun a ha ↦ this ha
  simp only [kerLift, Ideal.span_le]
  intro x
  simp only [Set.mem_range, Prod.exists, Subtype.exists, LinearMap.mem_ker, exists_prop,
    SetLike.mem_coe, RingHom.mem_ker, forall_exists_index, and_imp]
  rintro ⟨n, hn⟩ m hm ⟨rfl⟩
  simp only [PNat.mk_coe, LinearMap.lift_apply_dp, hm]
  exact dp_null_of_ne_zero R (Nat.ne_zero_of_lt hn)

@[simp]
theorem quotientEquiv_toAlgHom_mk_dp (n : ℕ) (m : M) :
    (quotientEquiv_toAlgHom f) ((Ideal.Quotient.mk (kerLift f)) (dp R n m)) = dp R n (f m) := by
  simp [quotientEquiv_toAlgHom, LinearMap.lift_apply_dp]

noncomputable def quotientEquiv_symm_toAlgHom :
    DividedPowerAlgebra R N →ₐ[R] (DividedPowerAlgebra R M ⧸ (kerLift f)) :=
  (exponentialModule_equiv R N (DividedPowerAlgebra R M ⧸ kerLift f)).symm (by
    let h : M →ₗ[R] (ExponentialModule (DividedPowerAlgebra R M)) :=
      exp_LinearMap R M
    let h' : (ExponentialModule (DividedPowerAlgebra R M)) →ₗ[R] (ExponentialModule (DividedPowerAlgebra R M ⧸ kerLift f)) :=
      linearMap (Ideal.Quotient.mkₐ R (kerLift f))
    refine (f.equiv_of_isSurjective _ hf).invFun ⟨h'.comp h, ?_⟩
    intro m hm
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, h', h] at hm ⊢
    ext k
    simp only [coeff_linearMap, coeff_exp_LinearMap, Ideal.Quotient.mkₐ_eq_mk, coe_zero_eq_one,
      coeff_one]
    split_ifs with hk
    · simp [hk, dp_zero]
    · rw [Ideal.Quotient.eq_zero_iff_mem, kerLift]
      apply Ideal.subset_span
      simp only [Set.mem_range, Prod.exists, Subtype.exists, LinearMap.mem_ker, exists_prop]
      exact ⟨⟨k, Nat.zero_lt_of_ne_zero hk⟩, m, hm, by simp⟩)

@[simp]
def quotientEquiv_symm_toAlgHom_dp (k : ℕ) (m : M) :
    quotientEquiv_symm_toAlgHom f hf (dp R k (f m)) = Submodule.mkQ _ (dp R k m) := by
  simp [quotientEquiv_symm_toAlgHom, exponentialModule_equiv_symm_apply, coeff_linearMap, coeff_exp_LinearMap]

/-- The canonical algebra equivalence of a quotient of
divided power algebra associated with a surjective linear map. -/
noncomputable def quotientEquiv :
    (DividedPowerAlgebra R M ⧸ (kerLift f)) ≃ₐ[R] DividedPowerAlgebra R N := by
  apply AlgEquiv.ofAlgHom (quotientEquiv_toAlgHom f) (quotientEquiv_symm_toAlgHom f hf)
  · rw [algHom_ext_iff]
    intro k n
    obtain ⟨m, rfl⟩ := hf n
    simp
  · apply Ideal.Quotient.algHom_ext
    rw [algHom_ext_iff]
    intros; simp

include hf in
-- This is [Roby-1963, Prop. IV.8].
theorem LinearMap.ker_lift_of_surjective :
    RingHom.ker (LinearMap.lift R f) = kerLift f := by
  ext x
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  simp [← EmbeddingLike.map_eq_zero_iff (f := (quotientEquiv f hf)),
    quotientEquiv, quotientEquiv_toAlgHom]

end quotient

end DividedPowerAlgebra
