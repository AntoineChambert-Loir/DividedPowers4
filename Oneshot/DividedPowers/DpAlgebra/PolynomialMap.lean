import Oneshot.DividedPowers.DpAlgebra.Init
import Oneshot.DividedPowers.DpAlgebra.Graded
import Mathbin.RingTheory.PowerSeries.Basic
import Mathbin.RingTheory.TensorProduct
import Mathbin.LinearAlgebra.Multilinear.Basic
import Oneshot.ForMathlib.RingTheory.SubmoduleMem

/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules… 

-/


open Algebra Function LinearMap

section Misc

theorem Finsupp.ofSupportFinite_support {ι α : Type _} [Zero α] (f : ι → α)
    (hf : f.support.Finite) : (Finsupp.ofSupportFinite f hf).support = hf.toFinset := by ext;
  simp only [Finsupp.ofSupportFinite_coe, Finsupp.mem_support_iff, Set.Finite.mem_toFinset,
    Function.mem_support]
#align finsupp.of_support_finite_support Finsupp.ofSupportFinite_support

end Misc

open scoped TensorProduct

section Algebra

variable (A : Type _) [CommSemiring A] (R : Type _) [CommSemiring R] [Algebra A R]

namespace Algebra.TensorProduct

-- The natural `R`-algebra map from `R ⊗[A] A` to `R`.
def rid' : R ⊗[A] A →ₐ[R] R :=
  {
    Algebra.TensorProduct.rid A
      R with
    map_one' := by simp only [AlgEquiv.toFun_eq_coe, map_one]
    map_zero' := by simp only [AlgEquiv.toFun_eq_coe, map_zero]
    commutes' := fun r => by
      simp only [algebraMap_apply, AlgEquiv.toFun_eq_coe, rid_tmul, one_smul] }
#align algebra.tensor_product.rid' Algebra.TensorProduct.rid'

@[simp]
theorem rid'_tmul (a : A) (r : R) : (rid' A R) (r ⊗ₜ[A] a) = a • r :=
  rfl
#align algebra.tensor_product.rid'_tmul Algebra.TensorProduct.rid'_tmul

end Algebra.TensorProduct

variable (M : Type _) [AddCommMonoid M] [Module A M]

-- Q (not important): I am not sure if `linear_form` is used in mathlib.
namespace LinearForm

open Algebra.TensorProduct LinearMap

def baseChange (f : M →ₗ[A] A) : R ⊗[A] M →ₗ[R] R :=
  (rid' A R).toLinearMap.comp (baseChange R f)
#align linear_form.base_change LinearForm.baseChange

theorem baseChange_apply_tmul (f : M →ₗ[A] A) (r : R) (m : M) :
    baseChange A R M f (r ⊗ₜ[A] m) = r * f m • 1 := by
  simp only [base_change, rid'_tmul, coe_comp, comp_app, base_change_tmul, AlgHom.toLinearMap_apply,
    mul_smul_comm, _root_.mul_one]
#align linear_form.base_change_apply_tmul LinearForm.baseChange_apply_tmul

variable (R' : Type _) [CommSemiring R'] [Algebra A R'] (φ : R →ₐ[A] R')

theorem baseChange_compat_apply (f : M →ₗ[A] A) (m : R ⊗[A] M) :
    φ (baseChange A R M f m) = (baseChange A R' M f) ((rTensor M φ.toLinearMap) m) :=
  by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · simp only [map_zero]
  ·
    simp only [base_change, rid'_tmul, coe_comp, comp_app, base_change_tmul,
      AlgHom.toLinearMap_apply, AlgHom.map_smul, rtensor_tmul]
  · simp only [map_add, hx, hy]
#align linear_form.base_change_compat_apply LinearForm.baseChange_compat_apply

end LinearForm

end Algebra

namespace MvPolynomial

variable {A : Type _} [CommSemiring A] {ι : Type _}

-- I think it makes more sense to have this in the `mv_polynomial` namespace
--def linear_map.mv_polynomial.coeff (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A :=
def coeffHom (k : ι →₀ ℕ) : MvPolynomial ι A →ₗ[A] A
    where
  -- or `coeff_linear_map`
  toFun := coeff k
  map_add' := coeff_add k
  map_smul' := coeff_smul k
#align mv_polynomial.coeff_hom MvPolynomial.coeffHom

theorem coeffHom_apply (k : ι →₀ ℕ) (f : MvPolynomial ι A) :
    coeffHom k f = MvPolynomial.coeff k f :=
  rfl
#align mv_polynomial.coeff_hom_apply MvPolynomial.coeffHom_apply

end MvPolynomial

section MvPolynomialModule

/- This is boring stuff devoted to prove the standard linear equivalence between M[σ] and A[σ] ⊗ M 
  for any A-module M and any type ι.
  Probably, this should be generalized to an arbitrary monoid, not only polynomials (corresponding 
  to σ →₀ ℕ). M[σ] has to be defined has (σ →₀ M) because mathlib doesn't know 
  about “the monoid module”. -/
open scoped TensorProduct

variable (σ : Type _) (A : Type _) [CommSemiring A] (N : Type _) [AddCommMonoid N] [Module A N]

open Finsupp

-- TODO: rename
noncomputable def zoo [DecidableEq σ] : ((σ →₀ ℕ) →₀ N) →ₗ[A] MvPolynomial σ A ⊗[A] N
    where
  toFun f := f.Sum fun k n => MvPolynomial.monomial k 1 ⊗ₜ[A] n
  map_add' f g :=
    by
    rw [sum_of_support_subset f (f.support.subset_union_left g.support),
      sum_of_support_subset g (f.support.subset_union_right g.support),
      sum_of_support_subset (f + g) support_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [coe_add, Pi.add_apply, TensorProduct.tmul_add]
    all_goals intro k hk; rw [TensorProduct.tmul_zero]
  map_smul' a f :=
    by
    rw [RingHom.id_apply, smul_sum, sum_of_support_subset (a • f) support_smul, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finsupp.coe_smul, Pi.smul_apply, TensorProduct.tmul_smul]
    · intro k hk; rw [TensorProduct.tmul_zero]
#align zoo zoo

theorem zoo_apply_single [DecidableEq σ] (k : σ →₀ ℕ) (n : N) :
    zoo σ A N (single k n) = (MvPolynomial.monomial k) 1 ⊗ₜ[A] n := by
  simp only [zoo, sum_single_index, TensorProduct.tmul_zero, LinearMap.coe_mk]
#align zoo_apply_single zoo_apply_single

noncomputable def zooInv' : MvPolynomial σ A ⊗[A] N →ₗ[A] (σ →₀ ℕ) → N
    where
  toFun f k := TensorProduct.lid A N (LinearMap.rTensor N (MvPolynomial.coeffHom k) f)
  map_add' f g := by ext k <;> simp only [map_add, Pi.add_apply]
  map_smul' a f := by
    ext k <;>
      simp only [LinearMap.map_smulₛₗ, RingHom.id_apply, LinearEquiv.map_smulₛₗ, Pi.smul_apply]
#align zoo_inv' zooInv'

theorem zooInv'_apply_tmul (f : MvPolynomial σ A) (n : N) (k : σ →₀ ℕ) :
    zooInv' σ A N (f ⊗ₜ[A] n) k = MvPolynomial.coeff k f • n := by
  simp only [zooInv', LinearMap.coe_mk, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    MvPolynomial.coeffHom_apply]
#align zoo_inv'_apply_tmul zooInv'_apply_tmul

theorem zooInv'_eq (f : MvPolynomial σ A) (n : N) :
    zooInv' σ A N (f ⊗ₜ[A] n) = fun k => MvPolynomial.coeff k f • n := by
  ext k <;> rw [zooInv'_apply_tmul]
#align zoo_inv'_eq zooInv'_eq

theorem zooInv'_support (p : MvPolynomial σ A ⊗[A] N) : (support (zooInv' σ A N p)).Finite :=
  by
  induction' p using TensorProduct.induction_on with f n f g hf hg
  -- case C0
  · simp only [map_zero, support_zero', Set.finite_empty]
  -- case C1,
  · apply Set.Finite.subset (MvPolynomial.support f).finite_toSet
    intro k
    simp only [mem_support, Finset.mem_coe, MvPolynomial.mem_support_iff, not_imp_not,
      zooInv'_apply_tmul]
    intro hk
    rw [hk, zero_smul]
  -- case Cp
  · rw [map_add]
    exact Set.Finite.subset (Set.Finite.union hf hg) (Function.support_add _ _)
#align zoo_inv'_support zooInv'_support

noncomputable def zooInv : MvPolynomial σ A ⊗[A] N →ₗ[A] (σ →₀ ℕ) →₀ N
    where
  toFun p := ofSupportFinite _ (zooInv'_support σ A N p)
  map_add' p q := by ext k <;> simp only [of_support_finite_coe, map_add, coe_add, Pi.add_apply]
  map_smul' a p := by
    ext k <;> simp only [of_support_finite_coe, LinearMap.map_smulₛₗ, Finsupp.coe_smul]
#align zoo_inv zooInv

theorem zooInv_coe_apply (p : MvPolynomial σ A ⊗[A] N) : zooInv' σ A N p = zooInv σ A N p :=
  rfl
#align zoo_inv_coe_apply zooInv_coe_apply

theorem zooInv_apply_tmul (f : MvPolynomial σ A) (n : N) :
    zooInv σ A N (f ⊗ₜ[A] n) = f.Sum fun (k : σ →₀ ℕ) (a : A) => single k (a • n) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [TensorProduct.sum_tmul, _root_.map_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro k hk
  ext l
  rw [← zooInv_coe_apply, zooInv'_apply_tmul, MvPolynomial.coeff_monomial, single_apply]
  split_ifs with h
  · rfl
  · rw [zero_smul]
#align zoo_inv_apply_tmul zooInv_apply_tmul

theorem zooInv'_comp_zoo [DecidableEq σ] (f : (σ →₀ ℕ) →₀ N) (k : σ →₀ ℕ) :
    zooInv' σ A N (zoo σ A N f) k = f k :=
  by
  simp only [zoo, Finsupp.sum, LinearMap.coe_mk, _root_.map_sum, zooInv'_eq,
    MvPolynomial.coeff_monomial, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp only [eq_self_iff_true, if_true, one_smul]
  · intro b hb hb'
    rw [if_neg hb', zero_smul]
  · rw [Finsupp.not_mem_support_iff]
    intro hk
    rw [hk, smul_zero]
#align zoo_inv'_comp_zoo zooInv'_comp_zoo

theorem zooInv_zoo_apply [DecidableEq σ] (f) : zooInv σ A N (zoo σ A N f) = f := by
  ext k <;> rw [← zooInv_coe_apply σ A N, zooInv'_comp_zoo]
#align zoo_inv_zoo_apply zooInv_zoo_apply

/- lemma zoo_inv_zoo' : function.left_inverse (zoo_inv σ A N) (zoo σ A N) :=
zoo_inv_zoo_apply σ A N -/
theorem zooInv_zoo [DecidableEq σ] : (zooInv σ A N).comp (zoo σ A N) = id := by
  ext f <;> simp only [zooInv_zoo_apply, coe_comp, comp_app, id_coe, id.def]
#align zoo_inv_zoo zooInv_zoo

theorem zoo_injective [DecidableEq σ] : Function.Injective (zoo σ A N) :=
  Function.HasLeftInverse.injective ⟨zooInv σ A N, zooInv_zoo_apply σ A N⟩
#align zoo_injective zoo_injective

theorem zoo_zooInv_of_tmul [DecidableEq σ] (f : MvPolynomial σ A) (n : N) :
    zoo σ A N (zooInv σ A N (f ⊗ₜ[A] n)) = f ⊗ₜ[A] n :=
  by
  conv_rhs => rw [f.as_sum]
  rw [zooInv_apply_tmul, Finsupp.sum, LinearMap.map_sum, TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zoo_apply_single, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← map_smul,
    Algebra.id.smul_eq_mul, mul_one]
  rfl
#align zoo_zoo_inv_of_tmul zoo_zooInv_of_tmul

theorem zoo_zooInv_apply [DecidableEq σ] (p : MvPolynomial σ A ⊗[A] N) :
    zoo σ A N (zooInv σ A N p) = p :=
  by
  induction' p using TensorProduct.induction_on with f n f g hf hg
  · rw [map_zero, map_zero]
  · rw [zoo_zooInv_of_tmul]
  · rw [map_add, map_add, hf, hg]
#align zoo_zoo_inv_apply zoo_zooInv_apply

theorem zoo_surjective [DecidableEq σ] : Function.Surjective (zoo σ A N) :=
  Function.HasRightInverse.surjective ⟨zooInv σ A N, zoo_zooInv_apply σ A N⟩
#align zoo_surjective zoo_surjective

theorem zoo_zooInv [DecidableEq σ] : (zoo σ A N).comp (zooInv σ A N) = LinearMap.id :=
  by
  apply LinearMap.ext
  intro p
  simp only [zoo_zooInv_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id.def]
#align zoo_zoo_inv zoo_zooInv

theorem zooInv_injective : Function.Injective (zooInv σ A N) := by
  classical exact Function.HasLeftInverse.injective ⟨zoo σ A N, zoo_zooInv_apply σ A N⟩
#align zoo_inv_injective zooInv_injective

noncomputable def linearMapEquiv [DecidableEq σ] : ((σ →₀ ℕ) →₀ N) ≃ₗ[A] MvPolynomial σ A ⊗[A] N :=
  { zoo σ A N with
    invFun := zooInv σ A N
    left_inv := zooInv_zoo_apply σ A N
    right_inv := zoo_zooInv_apply σ A N }
#align linear_map_equiv linearMapEquiv

end MvPolynomialModule

open scoped TensorProduct

section PolynomialMap

--universes u v₁ v₂ v₃ v₄ w w'
/- variables {A : Type u} {M : Type v₁} {N : Type v₂} [comm_semiring A] [add_comm_monoid M] 
  [module A M] [add_comm_monoid N] [module A N] -/
-- variables {A M N : Type*} [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N]
/-- A polynomial map M → N between A-modules is a functorial family
of maps R ⊗[A] M → R ⊗[A] N, for all A-algebras R -/
@[ext]
structure PolynomialMap (A : Type _) [CommSemiring A] (M : Type _) [AddCommMonoid M] [Module A M]
    (N : Type _) [AddCommMonoid N] [Module A N] where
  toFun : ∀ (R : Type _) [CommSemiring R], ∀ [Algebra A R], R ⊗[A] M → R ⊗[A] N
  is_compat :
    ∀ {R : Type _} [CommSemiring R] [Algebra A R] {R' : Type _} [CommSemiring R'] [Algebra A R']
      (φ : R →ₐ[A] R'), φ.toLinearMap.rTensor N ∘ to_fun R = to_fun R' ∘ φ.toLinearMap.rTensor M
#align polynomial_map PolynomialMap

namespace PolynomialMap

section Apply

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [Module A M] [AddCommMonoid N]
  [Module A N]

/- lemma is_compat_apply (f : polynomial_map A M N) (R : Type w) [comm_semiring R] [algebra A R] 
  (R' : Type w) [comm_semiring R'] [algebra A R'] (φ : R →ₐ[A] R') (x : R ⊗[A] M) : 
  (φ.to_linear_map.rtensor N) ((f.to_fun R) x) = ((f.to_fun R') (φ.to_linear_map.rtensor M x)) :=
by simpa only using congr_fun (f.is_compat φ) x-/
theorem is_compat_apply (f : PolynomialMap A M N) (R : Type _) [CommSemiring R] [Algebra A R]
    (R' : Type _) [CommSemiring R'] [Algebra A R'] (φ : R →ₐ[A] R') (x : R ⊗[A] M) :
    (φ.toLinearMap.rTensor N) ((f.toFun R) x) = (f.toFun R') (φ.toLinearMap.rTensor M x) := by
  simpa only using congr_fun (f.is_compat φ) x
#align polynomial_map.is_compat_apply PolynomialMap.is_compat_apply

end Apply

section Module

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [Module A M] [AddCommMonoid N]
  [Module A N]

def add (f g : PolynomialMap A M N) : PolynomialMap A M N
    where
  toFun R _ _ := f.to_fun R + g.to_fun R
  is_compat R _ _ R' _ _ φ := by
    ext <;> simp only [comp_app, Pi.add_apply, map_add, is_compat_apply]
#align polynomial_map.add PolynomialMap.add

instance : Zero (PolynomialMap A M N) :=
  ⟨{  toFun := fun R _ _ => 0
      is_compat := fun R _ _ R' _ _ φ => rfl }⟩

@[simp]
theorem zero_def (R : Type _) [CommSemiring R] [Algebra A R] :
    (0 : PolynomialMap A M N).toFun R = 0 :=
  rfl
#align polynomial_map.zero_def PolynomialMap.zero_def

instance : Inhabited (PolynomialMap A M N) :=
  ⟨Zero.zero⟩

instance : Add (PolynomialMap A M N) :=
  ⟨add⟩

@[simp]
theorem add_def (f g : PolynomialMap A M N) (R : Type _) [CommSemiring R] [Algebra A R] :
    (f + g).toFun R = f.toFun R + g.toFun R :=
  rfl
#align polynomial_map.add_def PolynomialMap.add_def

@[simp]
theorem add_def_apply (f g : PolynomialMap A M N) (R : Type _) [CommSemiring R] [Algebra A R]
    (m : R ⊗[A] M) : (f + g).toFun R m = f.toFun R m + g.toFun R m :=
  rfl
#align polynomial_map.add_def_apply PolynomialMap.add_def_apply

instance addCommMonoid : AddCommMonoid (PolynomialMap A M N)
    where
  add := Add.add
  add_assoc f g h := by ext R _ _ m resetI; simp only [add_def, add_assoc]
  zero := Zero.zero
  zero_add f := by ext R _ _ m; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext R _ _ m; simp only [add_def, add_zero, zero_def]
  nsmul n f :=
    { toFun := fun R _ _ => n • f.to_fun R
      is_compat := fun R R' _ _ _ _ φ => by
        ext m <;> simp only [is_compat_apply, map_nsmul, Function.comp_apply, Pi.smul_apply] }
  nsmul_zero f := by ext R _ _ m; simp only [zero_smul, Pi.smul_apply]; rfl
  nsmul_succ n f := by
    ext R _ _m
    simp only [add_def, Pi.smul_apply, Pi.add_apply, Nat.succ_eq_one_add, add_smul, one_smul]
  add_comm f g := by ext R _ _ m; simp only [add_def, add_comm]
#align polynomial_map.add_comm_monoid PolynomialMap.addCommMonoid

def smul (a : A) (f : PolynomialMap A M N) : PolynomialMap A M N
    where
  toFun R _ _ := a • f.to_fun R
  is_compat R R' _ _ _ _ φ := by
    ext m <;>
      simp only [is_compat_apply, comp_app, Pi.smul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply]
#align polynomial_map.smul PolynomialMap.smul

instance hasSmul : SMul A (PolynomialMap A M N) :=
  ⟨smul⟩
#align polynomial_map.has_smul PolynomialMap.hasSmul

theorem smul_def (f : PolynomialMap A M N) (a : A) (R : Type _) [CommSemiring R] [Algebra A R] :
    (a • f).toFun R = a • f.toFun R :=
  rfl
#align polynomial_map.smul_def PolynomialMap.smul_def

instance : MulAction A (PolynomialMap A M N)
    where
  one_smul f := by ext R _ _ m <;> simp only [smul_def, one_smul]
  mul_smul a b f := by ext R _ _ m <;> simp only [smul_def, mul_smul]

instance : DistribMulAction A (PolynomialMap A M N)
    where
  smul_zero a := rfl
  smul_add a f g := by ext R _ _ m <;> simp only [smul_def, add_def, smul_add]

instance module : Module A (PolynomialMap A M N)
    where
  add_smul a b f := by ext R _ _ m <;> simp only [smul_def, add_def, add_smul]
  zero_smul f := by ext R _ _ m <;> simp only [smul_def, zero_smul] <;> rfl
#align polynomial_map.module PolynomialMap.module

end Module

section Comp

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [Module A M] [AddCommMonoid N]
  [Module A N]

variable {P : Type _} [AddCommMonoid P] [Module A P]

def comp (g : PolynomialMap A N P) (f : PolynomialMap A M N) : PolynomialMap A M P
    where
  toFun R _ _ := (g.to_fun R).comp (f.to_fun R)
  is_compat R R' _ _ _ _ φ := by ext m <;> simp only [is_compat_apply, Function.comp_apply]
#align polynomial_map.comp PolynomialMap.comp

theorem comp_toFun (f : PolynomialMap A M N) (g : PolynomialMap A N P) (R : Type _) [CommSemiring R]
    [Algebra A R] : (g.comp f).toFun R = (g.toFun R).comp (f.toFun R) :=
  rfl
#align polynomial_map.comp_to_fun PolynomialMap.comp_toFun

theorem comp_apply (f : PolynomialMap A M N) (g : PolynomialMap A N P) (R : Type _) [CommSemiring R]
    [Algebra A R] (m : R ⊗[A] M) : (g.comp f).toFun R m = (g.toFun R) (f.toFun R m) :=
  rfl
#align polynomial_map.comp_apply PolynomialMap.comp_apply

variable {Q : Type _} [AddCommMonoid Q] [Module A Q]

theorem comp_assoc (f : PolynomialMap A M N) (g : PolynomialMap A N P) (h : PolynomialMap A P Q) :
    h.comp (g.comp f) = (h.comp g).comp f := by ext R _ _ m <;> simp only [comp_to_fun]
#align polynomial_map.comp_assoc PolynomialMap.comp_assoc

end Comp

section ConstantMap

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N] [Module A M]
  [Module A N]

open scoped TensorProduct

def ofConstant (n : N) : PolynomialMap A M N
    where
  toFun R _ _ m := TensorProduct.tmul A 1 n
  is_compat R _ _ R' _ _ φ := by
    skip <;> simp only [comp_const, rtensor_tmul, AlgHom.toLinearMap_apply, map_one]
#align polynomial_map.of_constant PolynomialMap.ofConstant

end ConstantMap

section Linear

open scoped TensorProduct

variable {A : Type _} [CommSemiring A] {M N : Type _} [AddCommMonoid M] [AddCommMonoid N]
  [Module A M] [Module A N]

def ofLinearMap (v : M →ₗ[A] N) : PolynomialMap A M N
    where
  toFun R _ _ := v.base_change R
  is_compat R _ _ _ _ _ φ := by
    ext m <;>
      simp only [base_change_eq_ltensor, ← LinearMap.comp_apply, comp_app, rtensor_comp_ltensor,
        ltensor_comp_rtensor]
#align polynomial_map.of_linear_map PolynomialMap.ofLinearMap

theorem ofLinearMap_toFun (u : M →ₗ[A] N) (R : Type _) [CommSemiring R] [Algebra A R] :
    (ofLinearMap u).toFun R = baseChange R u :=
  rfl
#align polynomial_map.of_linear_map_to_fun PolynomialMap.ofLinearMap_toFun

def ofLinearMapHom : (M →ₗ[A] N) →ₗ[A] PolynomialMap A M N
    where
  toFun := ofLinearMap
  map_add' u v := by
    ext R _ _ m
    simp only [PolynomialMap.add_def, of_linear_map_to_fun, Pi.add_apply, base_change_add,
      add_apply]
  map_smul' a v := by ext R _ _ m; simp only [smul_def, of_linear_map_to_fun, base_change_smul]; rfl
#align polynomial_map.of_linear_map_hom PolynomialMap.ofLinearMapHom

theorem ofLinearMapHom_apply (v : M →ₗ[A] N) : ofLinearMapHom v = ofLinearMap v :=
  rfl
#align polynomial_map.of_linear_map_hom_apply PolynomialMap.ofLinearMapHom_apply

end Linear

/- 
section multilinear

-- I need to understand how to do base change of multilinear maps  in Lean

variables (A N : Type*) [comm_semiring A]
variables {ι : Type*} [fintype ι] (M : ι → Type*) [∀ i, add_comm_monoid (M i)] [∀ i, module A (M i)]
variables  [add_comm_monoid N]  [module A N]

def of_multilinear_map (u : multilinear_map A M N) : polynomial_map A (Π i, M i) N := {
 to_fun := λ  R _ _, 
 begin 
--  by exactI u.base_change R, 

 end,
 is_compat := sorry } 

def of_multilinear_map_to_fun (u : multilinear_map A M N) (R : Type*) [comm_semiring R] [algebra A R] : false := sorry 


def of_multilinear_map : (multilinear_map A M N) 
  →ₗ[A] (polynomial_map A (Π i, M i) N) := {
to_fun := of_multilinear_map_to_fun, 
map_add' := sorry,
map_smul' := sorry }


end multilinear 
-/
section LocallyFinite

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N] [Module A M]
  [Module A N]

def Locfinsupp {ι : Type _} (f : ι → PolynomialMap A M N) : Prop :=
  ∀ (R : Type _) [CommSemiring R],
    ∀ [Algebra A R], ∀ m : R ⊗[A] M, (Function.support fun i => (f i).toFun R m).Finite
#align polynomial_map.locfinsupp PolynomialMap.Locfinsupp

variable (A M N)

def withLocfinsupp (ι : Type _) : Submodule A (ι → PolynomialMap A M N)
    where
  carrier := Locfinsupp
  add_mem' a b ha hb R _ _ m := by
    skip
    exact Set.Finite.subset (set.finite_union.mpr ⟨ha R m, hb R m⟩) (Function.support_add _ _)
  zero_mem' R _ _ m := by simp only [Pi.zero_apply, zero_def, support_zero, Set.finite_empty]
  smul_mem' a f hf R _ _ m := by
    skip
    exact Set.Finite.subset (hf R m) (Function.support_smul_subset_right a _)
#align polynomial_map.with_locfinsupp PolynomialMap.withLocfinsupp

namespace Locfinsupp

variable {A M N}

noncomputable def sum {ι : Type _} (f : ι → PolynomialMap A M N) (hf : Locfinsupp f) :
    PolynomialMap A M N
    where
  toFun R _ _ m := (Finsupp.ofSupportFinite _ (hf R m)).Sum fun i m => m
  is_compat R _rR _aR R' _rR' _aR' φ := by
    skip
    ext m
    simp only [Function.comp_apply, LinearMap.map_finsupp_sum]
    rw [Finsupp.sum]
    suffices _ ⊆ (hf R m).toFinset
      by
      rw [Finsupp.sum_of_support_subset _ this]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finsupp.ofSupportFinite_coe, _root_.map_sum, is_compat_apply]
      · intro i hi; rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← is_compat_apply]
      intro hi
      rw [hi, map_zero]
#align polynomial_map.locfinsupp.sum PolynomialMap.Locfinsupp.sum

theorem sum_eq {ι : Type _} (f : ι → PolynomialMap A M N) (hf : Locfinsupp f) (R : Type _)
    [CommSemiring R] [Algebra A R] (m : R ⊗[A] M) :
    (Locfinsupp.sum f hf).toFun R m = (Finsupp.ofSupportFinite _ (hf R m)).Sum fun i m => m :=
  rfl
#align polynomial_map.locfinsupp.sum_eq PolynomialMap.Locfinsupp.sum_eq

end Locfinsupp

--TODO: I don't think this is in the right namespace, but I don't know how to rename it.
noncomputable def LinearMap.Locfinsupp.sum {ι : Type _} [DecidableEq ι] :
    withLocfinsupp A M N ι →ₗ[A] PolynomialMap A M N
    where
  toFun fhf := Locfinsupp.sum fhf.val fhf.Prop
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext R _ _ m
    skip
    simp only [AddMemClass.mk_add_mk, locfinsupp.sum_eq, Pi.add_apply, add_def_apply]
    rw [@Finsupp.sum_of_support_subset _ _ _ _ _ _ ((hf R m).toFinset ∪ (hg R m).toFinset),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_left _ _),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_right _ _), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    all_goals try intro i hi; rfl
    · intro x
      simp only [Finsupp.ofSupportFinite_support, Set.Finite.mem_toFinset, Function.mem_support,
        Ne.def, Finset.mem_union]
      rw [← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' a fhf := by
    ext R _ _ m
    skip
    simp only [smul_def, locfinsupp.sum_eq, Subtype.val_eq_coe, Submodule.coe_smul_of_tower,
      Pi.smul_apply, RingHom.id_apply]
    rw [Finsupp.sum_of_support_subset]
    · rw [Finsupp.smul_sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun i hi => rfl
    · intro i
      simp only [Pi.smul_def, PolynomialMap.smul_def, Finsupp.ofSupportFinite_coe, not_imp_not,
        Finsupp.mem_support_iff]
      intro hi
      rw [hi, smul_zero]
    · intro i hi; rfl
#align polynomial_map.linear_map.locfinsupp.sum PolynomialMap.LinearMap.Locfinsupp.sum

end LocallyFinite

section Coefficients

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N] [Module A M]
  [Module A N]

-- The coefficients of a `polynomial_map` 
/- noncomputable def coeff' {ι : Type*} [fintype ι] (m : ι → M) (k : ι →₀ ℕ) : 
  polynomial_map A M N →ₗ[A] N := 
{ to_fun    := λ f, tensor_product.lid A N ((mv_polynomial.coeff_hom k).rtensor N
    (f.to_fun (mv_polynomial ι A) (k.support.sum (λ i, (mv_polynomial.X i) ⊗ₜ[A] m i)))), 
  map_add'  := λ f g, by simp only [add_def, pi.add_apply, map_add],
  map_smul' := λ a f, by simp only [smul_def, pi.smul_apply, linear_map.map_smulₛₗ, 
    ring_hom.id_apply, linear_equiv.map_smulₛₗ] } -/
/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff {ι : Type _} [Fintype ι] (m : ι → M) :
    PolynomialMap A M N →ₗ[A] (ι →₀ ℕ) →₀ N
    where
  toFun f :=
    zooInv _ A N (f.toFun (MvPolynomial ι A) (Finset.univ.Sum fun i => MvPolynomial.X i ⊗ₜ[A] m i))
  map_add' f g := by rw [← map_add]; rfl
  map_smul' a f := by simp only [RingHom.id_apply, ← map_smul]; rfl
#align polynomial_map.coeff PolynomialMap.coeff

variable {ι : Type _} [Fintype ι]

theorem coeff_eq (m : ι → M) (k : ι →₀ ℕ) (f : PolynomialMap A M N) :
    coeff m f k =
      (TensorProduct.lid A N)
        ((LinearMap.rTensor N (MvPolynomial.coeffHom k))
          (f.toFun (MvPolynomial ι A) (Finset.univ.Sum fun i : ι => MvPolynomial.X i ⊗ₜ[A] m i))) :=
  by simp only [coeff, LinearMap.coe_mk, zooInv, zooInv', Finsupp.ofSupportFinite_coe]
#align polynomial_map.coeff_eq PolynomialMap.coeff_eq

theorem image_eq_coeff_sum {ι : Type _} [Fintype ι] (m : ι → M) (f : PolynomialMap A M N)
    (R : Type _) [CommSemiring R] [Algebra A R] (r : ι → R) :
    f.toFun R (Finset.univ.Sum fun i => r i ⊗ₜ[A] m i) =
      (coeff m f).Sum fun k n => (Finset.univ.Prod fun i => r i ^ k i) ⊗ₜ[A] n :=
  by
  classical
  suffices :
    f.to_fun (MvPolynomial ι A) (finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[A] m i) =
      (coeff m f).Sum fun k n => MvPolynomial.monomial k 1 ⊗ₜ n
  let φ : MvPolynomial ι A →ₐ[A] R := MvPolynomial.aeval r
  have that := congr_fun (f.is_compat φ) (finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[A] m i)
  simp only [Function.comp_apply, LinearMap.map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at that 
  rw [← that]
  rw [this]
  simp only [Finsupp.sum]
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [φ, MvPolynomial.aeval_monomial]
  -- The generic case
  simp only [coeff]
  dsimp
  generalize f.to_fun (MvPolynomial ι A) (finset.univ.sum fun i : ι => MvPolynomial.X i ⊗ₜ[A] m i) =
    p
  obtain ⟨g, rfl⟩ := zoo_surjective ι A N p
  rw [zooInv_zoo_apply]
  rfl
#align polynomial_map.image_eq_coeff_sum PolynomialMap.image_eq_coeff_sum

/- Goal : have the preceding formula without [fintype ι],
but with finite support for r 

How to construct the coefficients:
one needs to restrict m to r.support
-/
theorem image_eq_coeff_sum' {ι : Type _} (m : ι → M) (f : PolynomialMap A M N) (R : Type _)
    [CommSemiring R] [Algebra A R] (r : ι →₀ R) :
    f.toFun R (r.Sum fun i a => a ⊗ₜ[A] m i) =
      (coeff (fun i : r.support => m i) f).Sum fun k n =>
        (r.support.Prod fun i => r i ^ (Function.extend coe k 0) i) ⊗ₜ[A] n :=
  by
  let m' : r.support → M := fun i => m i
  let r' : r.support →₀ R :=
    { toFun := fun i => r i
      support := Finset.univ
      mem_support_toFun := fun ⟨a, ha⟩ => by
        simpa only [Finset.univ_eq_attach, Finset.mem_attach, Subtype.coe_mk, Ne.def, true_iff_iff,
          Finsupp.mem_support_iff] using ha }
  convert image_eq_coeff_sum m' f R r'
  · simp only [Finsupp.sum]
    simp only [Finset.univ_eq_attach, Finsupp.coe_mk]
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro x hx; simp only [m']
  · ext k n
    apply congr_arg₂ _ _ rfl
    simp only [Finset.univ_eq_attach, Finsupp.coe_mk]
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro x hx
    apply congr_arg₂ _ rfl
    rw [subtype.coe_injective.extend_apply]
#align polynomial_map.image_eq_coeff_sum' PolynomialMap.image_eq_coeff_sum'

variable {R : Type _} [CommSemiring R] [Algebra A R]

theorem span_tensorProduct_eq_top_of_span_eq_top (σ : Type _) (e : σ → M)
    (hm : Submodule.span A (Set.range e) = ⊤) :
    (Submodule.span R (Set.range fun s => (1 : R) ⊗ₜ[A] e s) : Submodule R (R ⊗[A] M)) = ⊤ :=
  by
  rw [_root_.eq_top_iff]
  intro m h
  induction' m using TensorProduct.induction_on with r m x y hx hy
  exact zero_mem _
  · let f : M →ₗ[A] R ⊗[A] M :=
      { toFun := fun m => (1 : R) ⊗ₜ[A] m
        map_add' := fun x y => by rw [TensorProduct.tmul_add]
        map_smul' := fun a x => by simp only [TensorProduct.tmul_smul, RingHom.id_apply] }
    have hf : ∀ m : M, (1 : R) ⊗ₜ[A] m = f m; intro m; rfl
    suffices : r ⊗ₜ[A] m = r • (1 : R) ⊗ₜ[A] m
    rw [this]
    refine' Submodule.smul_mem _ r _
    apply Submodule.span_le_restrictScalars A
    rw [hf]; simp_rw [hf]
    convert Submodule.apply_mem_span_image_of_mem_span f _
    swap; exact Set.range e
    conv_rhs => rw [← Set.image_univ]
    rw [Set.image_image]
    rw [Set.image_univ]
    rw [hm]; exact Submodule.mem_top
    rw [TensorProduct.smul_tmul']; simp only [Algebra.id.smul_eq_mul, mul_one]
  exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
#align polynomial_map.span_tensor_product_eq_top_of_span_eq_top PolynomialMap.span_tensorProduct_eq_top_of_span_eq_top

theorem coeff_injective (m : ι → M) (hm : Submodule.span A (Set.range m) = ⊤)
    (f g : PolynomialMap A M N) (h : coeff m f = coeff m g) : f = g :=
  by
  skip
  rw [ext_iff]
  ext R _ _ p
  skip
  have h : p ∈ ⊤ := Submodule.mem_top
  rw [← span_tensor_product_eq_top_of_span_eq_top ι m hm] at h 
  rw [Submodule.mem_span_iff_exists_sum _ p] at h 
  simp [TensorProduct.smul_tmul'] at h 
  obtain ⟨r, rfl⟩ := h
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)]
  rw [image_eq_coeff_sum m f]
  simp only [image_eq_coeff_sum]; rw [h]
  intro i hi; simp only [TensorProduct.zero_tmul]
#align polynomial_map.coeff_injective PolynomialMap.coeff_injective

noncomputable def Finsupp.polynomialMap (b : Basis ι A M) (h : (ι →₀ ℕ) →₀ N) : PolynomialMap A M N
    where
  toFun R _ _ x :=
    h.sum fun k n =>
      (finset.univ.prod fun i => (LinearForm.baseChange A R _ (b.coord i)) x ^ k i) ⊗ₜ[A] n
  is_compat R _ _ R' _ _ φ := by
    skip
    ext m
    dsimp
    simp only [Finsupp.sum]
    rw [_root_.map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    apply congr_arg₂ _ _ rfl
    rw [map_prod φ]
    apply Finset.prod_congr rfl
    intro i hi
    rw [map_pow]
    apply congr_arg₂ _ _ rfl
    rw [LinearForm.baseChange_compat_apply]
#align polynomial_map.finsupp.polynomial_map PolynomialMap.Finsupp.polynomialMap

theorem Finsupp.polynomialMap_toFun_apply (b : Basis ι A M) (h : (ι →₀ ℕ) →₀ N) (m : R ⊗[A] M) :
    (Finsupp.polynomialMap b h).toFun R m =
      h.Sum fun k n =>
        (Finset.univ.Prod fun i => (LinearForm.baseChange A R _ (b.Coord i)) m ^ k i) ⊗ₜ[A] n :=
  rfl
#align polynomial_map.finsupp.polynomial_map_to_fun_apply PolynomialMap.Finsupp.polynomialMap_toFun_apply

example (f g : ι → ℕ) (i : ι) : (f + g) i = f i + g i :=
  Pi.add_apply f g i

theorem coeff_of_finsupp_polynomialMap (b : Basis ι A M) (h : (ι →₀ ℕ) →₀ N) :
    coeff (coeFn b) (Finsupp.polynomialMap b h) = h := by
  classical
  simp only [coeff]
  dsimp
  conv_rhs => rw [← zooInv_zoo_apply ι A N h]
  apply congr_arg
  simp only [zoo, finsupp.polynomial_map]
  dsimp
  apply congr_arg
  ext k
  apply congr_arg₂ _ _ rfl
  rw [MvPolynomial.monomial_eq]
  simp
  apply congr_arg
  ext i
  congr
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  simp [LinearForm.baseChange]
  intro j hj hij
  simp only [LinearForm.baseChange_apply_tmul]
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [if_neg hij]
  simp only [zero_smul, MulZeroClass.mul_zero]
#align polynomial_map.coeff_of_finsupp_polynomial_map PolynomialMap.coeff_of_finsupp_polynomialMap

theorem finsup_polynomialMap_of_coeff (b : Basis ι A M) (f : PolynomialMap A M N) :
    Finsupp.polynomialMap b (coeff (coeFn b) f) = f :=
  by
  apply coeff_injective (coeFn b)
  · rw [_root_.eq_top_iff]; intro m hm
    apply Submodule.span_mono _ (Basis.mem_span_repr_support b m)
    apply Set.image_subset_range
  rw [coeff_of_finsupp_polynomial_map]
#align polynomial_map.finsup_polynomial_map_of_coeff PolynomialMap.finsup_polynomialMap_of_coeff

example [DecidableEq ι] (b : Basis ι A M) (i j : ι) : (b.Coord i) (b j) = ite (j = i) 1 0 := by
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

noncomputable def coeffPolynomialMapEquiv (b : Basis ι A M) :
    ((ι →₀ ℕ) →₀ N) ≃ₗ[A] PolynomialMap A M N
    where
  toFun h := Finsupp.polynomialMap b h
  map_add' h k := by
    classical
    rw [ext_iff]
    ext R _ _ m
    simp only [finsupp.polynomial_map_to_fun_apply, add_def, Pi.add_apply]
    rw [Finsupp.sum_of_support_subset h (h.support.subset_union_left k.support)]
    rw [Finsupp.sum_of_support_subset k (h.support.subset_union_right k.support)]
    rw [Finsupp.sum_of_support_subset (h + k) Finsupp.support_add]
    simp_rw [Finsupp.coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [Finset.sum_add_distrib]
    all_goals intro i hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    rw [ext_iff]; ext R _ _ m; skip
    simp only [RingHom.id_apply, smul_def, Pi.smul_apply]
    simp [finsupp.polynomial_map_to_fun_apply]
    rw [Finsupp.sum_of_support_subset (a • h) Finsupp.support_smul]
    simp only [Finsupp.sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finsupp.coe_smul, Pi.smul_apply, TensorProduct.tmul_smul]
    intro k hk; rw [TensorProduct.tmul_zero]
  invFun f := coeff (coeFn b) f
  left_inv h := by dsimp; rw [coeff_of_finsupp_polynomial_map]
  right_inv f := by dsimp; rw [finsup_polynomial_map_of_coeff b]
#align polynomial_map.coeff_polynomial_map_equiv PolynomialMap.coeffPolynomialMapEquiv

end Coefficients

section Graded

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N] [Module A M]
  [Module A N]

def IsHomogeneousOfDegree {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module A N] (p : ℕ) (f : PolynomialMap A M N) : Prop :=
  ∀ (R : Type _) [CommRing R],
    ∀ [Algebra A R], ∀ (r : R) (m : R ⊗[A] M), f.to_fun R (r • m) = r ^ p • f.to_fun R m
#align polynomial_map.is_homogeneous_of_degree PolynomialMap.IsHomogeneousOfDegree

theorem TensorProduct.is_finsupp_sum_tmul {R : Type _} [CommSemiring R] [Algebra A R]
    (m : R ⊗[A] M) : ∃ r : M →₀ R, m = r.Sum fun x a => a ⊗ₜ[A] x :=
  by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · use 0; simp only [Finsupp.sum_zero_index]
  · use Finsupp.single m r; simp only [Finsupp.sum_single_index, TensorProduct.zero_tmul]
  · obtain ⟨rx, rfl⟩ := hx
    obtain ⟨ry, rfl⟩ := hy
    use rx + ry
    rw [Finsupp.sum_add_index']
    · intro a; simp only [TensorProduct.zero_tmul]
    · intro m r₁ r₂; rw [TensorProduct.add_tmul]
#align tensor_product.is_finsupp_sum_tmul TensorProduct.is_finsupp_sum_tmul

theorem isHomogeneousOfDegree_iff (p : ℕ) (f : PolynomialMap A M N) :
    f.IsHomogeneousOfDegree p ↔
      ∀ (ι : Type _) [Fintype ι],
        ∀ (m : ι → M) (k : ι →₀ ℕ) (h : coeff m f k ≠ 0), (k.Sum fun i n => n) = p :=
  by
  constructor
  · -- difficult direction
    intro hf
    intro ι _ m k h
    sorry
  · intro hf R _ _ a m
    skip
    obtain ⟨r, rfl⟩ := TensorProduct.is_finsupp_sum_tmul m
    rw [Finsupp.smul_sum]
    simp only [Finsupp.sum, TensorProduct.smul_tmul']
    sorry
#align polynomial_map.is_homogeneous_of_degree_iff PolynomialMap.isHomogeneousOfDegree_iff

end Graded

end PolynomialMap

end PolynomialMap

