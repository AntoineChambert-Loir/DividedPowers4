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
- `DividedPowerAlgebra.exp` : the power series
-/

variable (R : Type*) [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

namespace DividedPowerAlgebra

open PowerSeries Additive

/-- The exponential power series of an element of a module, in the DividedPowerAlgebra -/
noncomputable def exp' (m : M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dp R n m)

lemma coeff_exp' (m : M) (n : ℕ) :
    coeff (DividedPowerAlgebra R M) n (exp' R m) = dp R n m := by
  simp only [coeff_mk, exp']

theorem isExponential_exp' (m : M) : IsExponential (exp' R m) := by
  rw [isExponential_iff]
  constructor
  · rw [← coeff_zero_eq_constantCoeff, coeff_exp', dp_zero]
  · intro p q
    simp only [coeff_exp', dp_mul, nsmul_eq_mul]

/-- The exponential power series of an element of a module,
  ExponentialModule of the DividedPowerAlgebra -/
noncomputable def exp (m : M) : ExponentialModule (DividedPowerAlgebra R M) :=
  ⟨ofMul (exp' R m), isExponential_exp' R m⟩

theorem coe_exp (m : M) : ↑(exp R m) = exp' R m := rfl

theorem coeff_exp (m : M) (n : ℕ) : coeff _ n (exp R m) = dp R n m := by
  simp only [coe_exp, coeff_exp']

noncomputable instance : Algebra R (DividedPowerAlgebra R M) := inferInstance

noncomputable instance : Module R (ExponentialModule R) := inferInstance

noncomputable instance : Module R (ExponentialModule (DividedPowerAlgebra R M)) :=
  Module.compHom _ (algebraMap R (DividedPowerAlgebra R M))

noncomputable instance :
    IsScalarTower R (DividedPowerAlgebra R M) (ExponentialModule (DividedPowerAlgebra R M)) :=
  IsScalarTower.of_compHom _ _ _

-- TODO : The following could serve as a definition of an exponential structure
-- this is equivalent to the combination of dpow_null, dpow_add and dpow_smul

/-- The exponential power series of an element of a module,
  ExponentialModule of the DividedPowerAlgebra,
  as a LinearMap -/
noncomputable def exp_LinearMap : M →ₗ[R] ExponentialModule (DividedPowerAlgebra R M) where
  toFun := exp R
  map_add' x y := by
    apply ExponentialModule.coe_injective
    ext n
    simp only [ExponentialModule.coe_add, coeff_exp, coeff_mul, dp_add]
  map_smul' r m := by
    apply ExponentialModule.coe_injective
    ext n
    simp only [coeff_exp, RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_smul (DividedPowerAlgebra R M) r (exp R m),
      ExponentialModule.coe_smul, coeff_scale, coeff_exp, ← map_pow,
      IsScalarTower.algebraMap_smul, dp_smul]

/- -- Old version
variable (R : Type _) [CommSemiring R]

def IsExponential (f : ℕ → R) : Prop :=
  f 0 = 1 ∧ ∀ p q, f (p + q) = Nat.choose (p + q) q * f p * f q
#align is_exponential IsExponential

set_option linter.uppercaseLean3 false
structure Exp (R : Type _) [Semiring R] where
  toFun : ℕ → R
  map_zero : toFun 0 = 1
  map_add : ∀ p q, toFun (p + q) = Nat.choose (p + q) q * toFun p * toFun q
#align Exp Exp

namespace Exp

instance funLike : DFunLike (Exp R) ℕ (fun _ => R)
    where
  coe := Exp.toFun
  coe_injective' f g h := by cases f ; cases g ; congr
#align Exp.fun_like Exp.funLike

@[simp] theorem toFun_eq_coe {f : Exp R} : f.toFun = (f : ℕ → R) := rfl
#align Exp.to_fun_eq_coe Exp.toFun_eq_coe

@[ext] theorem ext {f g : Exp R} (h : ∀ n, f n = g n) : f = g := DFunLike.ext f g h
#align Exp.ext Exp.ext

protected def copy (f : Exp R) (f' : ℕ → R) (h : f' = f) : Exp R where
  toFun    := f'
  map_zero := h.symm ▸ f.map_zero
  map_add  := h.symm ▸ f.map_add
#align Exp.copy Exp.copy

def add : Exp R → Exp R → Exp R := fun f g =>
  { toFun := fun p => (Finset.antidiagonal p).sum fun rs => f rs.1 * g rs.2
    map_zero := by
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, ← toFun_eq_coe, map_zero,
        mul_one]
    map_add := by sorry }
#align Exp.add Exp.add

/- example : add_comm_group (Exp R) := {

} -/
--#print is_exponential
end Exp
-/
