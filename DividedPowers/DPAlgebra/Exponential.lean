import DividedPowers.DPAlgebra.Init
import DividedPowers.ExponentialModule.Basic
-- import DividedPowers.ForMathlib.MvPowerSeries.Order
-- import DividedPowers.ForMathlib.MvPowerSeries.Topology


/-! # Divided power algebra and exponential modules

Here we prove Theorem III.1 of [Roby1963].
M is an R-module
A is an R-algebra
There is an equivalence between
* algebra morphisms α : DividedPowerAlgebra R M →ₐ[R] A
* module morphisms β : M →ₗ[R] ExponentialModule (A)
which satisfies
  β m = ∑ α ( dp n m ) X ^ n
for all m : M

We define
- `DividedPowerAlgebra.exp` : the power series `∑ (dp n m) X ^ n

-/

variable (R : Type*) [CommRing R] {A : Type*} [CommSemiring A] [Algebra R A]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

namespace DividedPowerAlgebra

open PowerSeries Additive ExponentialModule

/-- The exponential power series of an element of a module, in the DividedPowerAlgebra -/
noncomputable def exp' (m : M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dp R n m)

lemma coeff_exp' (m : M) (n : ℕ) :
    coeff (DividedPowerAlgebra R M) n (exp' R m) = dp R n m := by
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

theorem coeff_exp (m : M) (n : ℕ) : coeff _ n (exp R m) = dp R n m := by
  simp only [coe_exp, coeff_exp']

-- TODO : The following could serve as a definition of an exponential structure
-- this is equivalent to the combination of dpow_zero, dpow_add and dpow_smul

variable (M) in
/-- The exponential power series of an element of a module,
  valued in the ExponentialModule of the DividedPowerAlgebra,
  as a LinearMap -/
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
    rw [← algebraMap_smul (DividedPowerAlgebra R M) r (exp R m),
      coe_smul, coeff_rescale, coeff_exp, ← map_pow, dp_smul]
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.smul_def, map_pow]


theorem coe_exp_LinearMap :
    ⇑(exp_LinearMap R M) = exp R := rfl

theorem coeff_exp_LinearMap (n : ℕ) (m : M) :
    coeff (DividedPowerAlgebra R M) n (exp_LinearMap R M m) = dp R n m := by
  rw [coe_exp_LinearMap, coeff_exp]

variable {S : Type*} [CommRing S] [Algebra R S]

variable (M S) in
/-- The equivalence between
  algebra morphisms `DividedPowerAlgebra R M →ₐ[R] S` and
  linear maps `M →ₗ[R] ExponentialModule S`

  [Roby1963, theorem III.1] -/
noncomputable
def dividedPowerAlgebra_exponentialModule_equiv :
    (DividedPowerAlgebra R M →ₐ[R] S) ≃ (M →ₗ[R] ExponentialModule S) where
  toFun α := (linearMap α).comp (exp_LinearMap R M)
  invFun β := by
    apply DividedPowerAlgebra.lift' (f := fun (n, m) ↦ coeff S n (β m))
    · intro m
      simp only [coeff_zero_eq_constantCoeff]
      exact constantCoeff_coe (β m)
    · intro n r m
      simp only [LinearMapClass.map_smul, coe_smul, coeff_rescale]
      rw [Algebra.smul_def, map_pow]
    · intro n p m
      simp only [nsmul_eq_mul]
      rw [(isExponential_iff.mp (isExponential_coe _)).1]
      -- TODO: add lemmas for product of coeff and constant coeff
    · intro n x y
      simp only [map_add, coe_add, coeff_mul]
  left_inv := by
    intro α
    simp only [LinearMap.coe_comp, Function.comp_apply]
    apply algHom_ext
    intro n m
    simp only [lift'_apply_dp]
    rw [coeff_linearMap]
    simp only [coeff_exp_LinearMap]
  right_inv := by
    intro β
    ext m n
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [coeff_linearMap]
    rw [coeff_exp_LinearMap]
    simp only [lift'_apply_dp]

variable {R} in
theorem dividedPowerAlgebra_exponentialModule_equiv_apply
    (α : DividedPowerAlgebra R M →ₐ[R] S) :
    dividedPowerAlgebra_exponentialModule_equiv R M S α = (linearMap α).comp (exp_LinearMap R M) :=
  rfl

variable {R} in
theorem dividedPowerAlgebra_exponentialModule_equiv_symm_apply
    (β : M →ₗ[R] ExponentialModule S) (n : ℕ) (m : M):
    (dividedPowerAlgebra_exponentialModule_equiv R M S).symm β (dp R n m)
      = coeff S n (β m) := by
  unfold dividedPowerAlgebra_exponentialModule_equiv
  simp only [Equiv.coe_fn_symm_mk, lift'_apply_dp]
