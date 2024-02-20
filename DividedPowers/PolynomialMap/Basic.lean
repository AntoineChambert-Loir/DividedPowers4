import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Data.MvPolynomial.Basic

-- import Mathlib.LinearAlgebra.Multilinear.Basic
import DividedPowers.ForMathlib.RingTheory.SubmoduleMem


/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules…

-/

section

variable {A B R : Type _} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

lemma AlgEquiv.toFun_eq_coe (e : A ≃ₐ[R] B) : e.toFun = e := rfl

end

section Finset

@[to_additive]
theorem Finset.prod_congr_equiv {α β M : Type _} [CommMonoid M]
  {f : α → M} {s : Finset α}
  (e : α ≃ β) : s.prod f = (s.map e).prod (f ∘ e.symm)  := by
  simp only [Function.comp_apply, Finset.prod_map, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply]

-- Useful ?
@[to_additive]
theorem Finset.prod_congr_equiv' {α β M : Type _} [CommMonoid M]
  {f : β → M} {s : Finset α}
  (e : α ≃ β) : s.prod (f ∘ e) = (s.map e).prod f := by
  simp only [Function.comp_apply, prod_map, Equiv.coe_toEmbedding]

end Finset


section Misc

theorem Finsupp.ofSupportFinite_support {ι α : Type _} [Zero α]
    (f : ι → α) (hf : f.support.Finite) :
  (Finsupp.ofSupportFinite f hf).support = hf.toFinset := by
  ext
  simp only [Finsupp.ofSupportFinite_coe, Finsupp.mem_support_iff,
    Set.Finite.mem_toFinset, Function.mem_support]
#align finsupp.of_support_finite_support Finsupp.ofSupportFinite_support

end Misc

open Algebra Function LinearMap

open scoped TensorProduct

section Algebra

variable (R : Type _) [CommSemiring R]
  (S : Type _) [CommSemiring S] [Algebra R S]

namespace Algebra.TensorProduct

-- The natural `R`-algebra map from `S ⊗[R] R` to `S`.
noncomputable def rid' : S ⊗[R] R →ₐ[S] S := Algebra.TensorProduct.rid R S S/- with
  map_one' := by simp only [AlgEquiv.toFun_eq_coe, map_one]
  map_zero' := by simp only [AlgEquiv.toFun_eq_coe, map_zero]
  commutes' := fun r => by
    simp only [algebraMap_apply, AlgEquiv.toFun_eq_coe, rid_tmul, one_smul] } -/
#align algebra.tensor_product.rid' Algebra.TensorProduct.rid'

@[simp]
theorem rid'_tmul (r : R) (s : S) : (rid' R S) (s ⊗ₜ[R] r) = r • s := rfl
#align algebra.tensor_product.rid'_tmul Algebra.TensorProduct.rid'_tmul

end Algebra.TensorProduct

variable (M : Type _) [AddCommMonoid M] [Module R M]

-- Q (not important): I am not sure if `linear_form` is used in mathlib.
namespace LinearForm

open Algebra.TensorProduct LinearMap

noncomputable def baseChange (f : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (rid' R S).toLinearMap.comp (LinearMap.baseChange S f)
#align linear_form.base_change LinearForm.baseChange

theorem baseChange_apply_tmul (f : M →ₗ[R] R) (r : S) (m : M) :
  baseChange R S M f (r ⊗ₜ[R] m) = r * ((f m) • (1 : S)) := by
  simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
    AlgHom.toLinearMap_apply, rid'_tmul, Algebra.mul_smul_comm, _root_.mul_one]
#align linear_form.base_change_apply_tmul LinearForm.baseChange_apply_tmul

variable (S' : Type _) [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S')

theorem baseChange_compat_apply (f : M →ₗ[R] R) (m : S ⊗[R] M) :
  φ (baseChange R S M f m) =
    (baseChange R S' M f) ((rTensor M φ.toLinearMap) m) := by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · simp only [map_zero]
  · simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
      AlgHom.toLinearMap_apply, rid'_tmul, map_smul, rTensor_tmul]
  · simp only [map_add, hx, hy]
#align linear_form.base_change_compat_apply LinearForm.baseChange_compat_apply

end LinearForm

end Algebra

namespace MvPolynomial

variable {R : Type _} [CommSemiring R] {ι : Type _}

-- I think it makes more sense to have this in the `mv_polynomial` namespace
--def linear_map.mv_polynomial.coeff (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A :=
def lcoeff (k : ι →₀ ℕ) : MvPolynomial ι R →ₗ[R] R where
  -- or `coeff_linear_map`
  toFun     := coeff k
  map_add'  := coeff_add k
  map_smul' := coeff_smul k
#align mv_polynomial.coeff_hom MvPolynomial.lcoeff

--#check MvPolynomial.lcoeff

theorem lcoeff_apply (k : ι →₀ ℕ) (f : MvPolynomial ι R) :
    lcoeff k f = MvPolynomial.coeff k f :=
  rfl
#align mv_polynomial.coeff_hom_apply MvPolynomial.lcoeff_apply

end MvPolynomial

section MvPolynomialModule

/- This is boring stuff devoted to prove
  the standard linear equivalence between M[σ] and R[σ] ⊗ M
  for any semiring R, any R-module M and any type σ.
  Probably, this should be generalized to an arbitrary monoid,
  not only polynomials (corresponding to σ →₀ ℕ).
  M[σ] has to be defined hss (σ →₀ M)
  because mathlib doesn't know about “the monoid module”. -/
open scoped TensorProduct

variable (σ : Type _) [DecidableEq σ]
  (R : Type _) [CommSemiring R]
  (N : Type _) [AddCommMonoid N] [Module R N]

open Finsupp

/- I wonder whether there's a simpler proof using
the fact that MvPolynomial σ R is a free R-module,
with basis given by monomials
One issue is that `Algebra.TensorProduct.Basis` makes
base change on the left, and has different assumptions… -/

-- TODO: rename

noncomputable def zoo :
    ((σ →₀ ℕ) →₀ N) →ₗ[R] MvPolynomial σ R ⊗[R] N := (Finsupp.lsum R)
  (fun d => (LinearMap.rTensor N (MvPolynomial.monomial d)).comp
    (TensorProduct.lid R N).symm.toLinearMap)

theorem zoo_apply_single (k : σ →₀ ℕ) (n : N) :
  zoo σ R N (single k n) =
    (MvPolynomial.monomial k) 1 ⊗ₜ[R] n := by
  simp only [zoo, Finsupp.lsum_single, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.lid_symm_apply, rTensor_tmul]
#align zoo_apply_single zoo_apply_single

noncomputable def zooInv :
    MvPolynomial σ R ⊗[R] N →ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.lift ((Finsupp.llift _ R R _ ).toLinearMap.toFun lsingle )

theorem zooInv_apply_tmul (p : MvPolynomial σ R) (n : N) (k):
  (zooInv σ R N) (p ⊗ₜ[R] n) k = MvPolynomial.coeff k p • n := by
  rw [zooInv]
  simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, TensorProduct.lift.tmul]
  suffices : MvPolynomial.coeff k p • n = sum p fun d b => (Finsupp.single d (b • n)) k
  · rw [this]
    have := Finsupp.llift_apply (N →ₗ[R] (σ →₀ ℕ) →₀ N) R R (σ →₀ ℕ)
    specialize this lsingle p
    rw [LinearMap.ext_iff] at this
    specialize this n
    rw [DFunLike.ext_iff] at this
    apply symm
    specialize this k
    simp only [lift_apply, finsupp_sum_apply, LinearMap.smul_apply,
      lsingle_apply, smul_single, Finsupp.sum_apply] at this
    exact this.symm
  rw [Finsupp.sum_eq_single k]
  · rw [single_eq_same]
    rfl
  · intro d _ hdk
    rw [Finsupp.single_apply, if_neg hdk]
  · intro _
    simp only [zero_smul, single_zero, coe_zero, Pi.zero_apply]

theorem zooInv_apply (pn) :
  (zooInv σ R N) pn k =
    (TensorProduct.lid R N)
      ((rTensor N (MvPolynomial.lcoeff k)) pn) := by
  induction pn using TensorProduct.induction_on with
  | zero => simp only [map_zero, coe_zero, Pi.zero_apply]
  | tmul p n =>
      simp only [rTensor_tmul, TensorProduct.lid_tmul]
      simp only [zooInv_apply_tmul]
      rfl
  | add p q h h' =>
      simp only [map_add, coe_add, Pi.add_apply]
      simp only [h, h']

theorem zooInv_zoo_apply (f) : zooInv σ R N (zoo σ R N f) = f := by
  suffices : (zooInv σ R N) ∘ₗ (zoo σ R N) = LinearMap.id
  · simp only [← LinearMap.comp_apply, this, id_coe, id_eq]
  ext d n e
  simp only [LinearMap.id_comp, lsingle_apply, zoo, coe_comp, coe_lsum, LinearEquiv.coe_coe,
    Function.comp_apply, map_zero, sum_single_index, TensorProduct.lid_symm_apply, rTensor_tmul]
  rw [zooInv_apply]
  simp only [rTensor_tmul, TensorProduct.lid_tmul,  Finsupp.single_apply,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial, ite_smul,
    one_smul, zero_smul]

theorem zoo_zooInv_apply (p) : (zoo σ R N) (zooInv σ R N p) = p := by
  suffices : (zoo σ R N) ∘ₗ (zooInv σ R N) = LinearMap.id
  · simp only [← LinearMap.comp_apply, this, id_coe, id_eq]
  ext d n
  simp only [coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, coe_restrictScalars, id_coe, id_eq]
  suffices : (zooInv σ R N) ((MvPolynomial.monomial d) 1 ⊗ₜ[R] n) =
    Finsupp.single d n
  · rw [this]
    simp only [zoo, coe_lsum, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, map_zero, sum_single_index,
      TensorProduct.lid_symm_apply, rTensor_tmul]
  ext e
  rw [zooInv_apply, Finsupp.single_apply]
  simp only [MvPolynomial.lcoeff, rTensor_tmul, LinearMap.coe_mk, AddHom.coe_mk,
    MvPolynomial.coeff_monomial, TensorProduct.lid_tmul, ite_smul, one_smul, zero_smul]

noncomputable def zooEquiv :
  ((σ →₀ ℕ) →₀ N) ≃ₗ[R] MvPolynomial σ R ⊗[R] N :=
  { zoo σ R N with
    invFun := zooInv σ R N
    left_inv := zooInv_zoo_apply σ R N
    right_inv := zoo_zooInv_apply σ R N }
#align linear_map_equiv zooEquiv

theorem zooEquiv_apply_single (k : σ →₀ ℕ) (n : N) :
  zooEquiv σ R N (single k n) = (MvPolynomial.monomial k) 1 ⊗ₜ[R] n := by
  simp [← LinearEquiv.toFun_eq_coe, zooEquiv, zoo_apply_single]
#align zoo_equiv_apply_single zooEquiv_apply_single

theorem zooEquiv_symm_apply_tmul (p : MvPolynomial σ R) (n : N) (k) :
    (zooEquiv σ R N).symm (p ⊗ₜ[R] n) k = MvPolynomial.coeff k p • n := by
  simp [← LinearEquiv.invFun_eq_symm, zooEquiv, zooInv_apply, MvPolynomial.lcoeff]

theorem zooEquiv_symm_apply (pn) :
  (zooEquiv σ R N).symm pn k = (TensorProduct.lid R N)
      ((rTensor N (MvPolynomial.lcoeff k)) pn) := by
  simp [← LinearEquiv.invFun_eq_symm, zooEquiv, zooInv_apply]
end MvPolynomialModule

open scoped TensorProduct

section PolynomialMap

noncomputable section

/-- A polynomial map M → N between A-modules is a functorial family
of maps R ⊗[A] M → R ⊗[A] N, for all A-algebras R -/
@[ext]
structure PolynomialMap (R : Type u) [CommSemiring R]
    (M : Type _) [AddCommMonoid M] [Module R M]
    (N : Type _) [AddCommMonoid N] [Module R N] where
  toFun (S : Type u) [CommSemiring S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  isCompat {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun S =
      toFun S' ∘ φ.toLinearMap.rTensor M
#align polynomial_map PolynomialMap

namespace PolynomialMap

section Apply

variable {R : Type u} {M N : Type _} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The map M → N associated with a PolynomialMap R M N (essentially, toFun R)-/
noncomputable def ground (f : PolynomialMap R M N) : M → N :=
  (TensorProduct.lid R N) ∘ (f.toFun R) ∘ (TensorProduct.lid R M).symm

theorem isCompat_apply (f : PolynomialMap R M N)
    {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : S ⊗[R] M) :
  (φ.toLinearMap.rTensor N) ((f.toFun S) x) =
      (f.toFun S') (φ.toLinearMap.rTensor M x) := by
  simpa only using congr_fun (f.isCompat φ) x
#align polynomial_map.is_compat_apply PolynomialMap.isCompat_apply

variable {S : Type u} [CommSemiring S] [Algebra R S]

variable (R)
def algebraMap' (S : Type u) [Semiring S] [Algebra R S] : R →ₐ[R] S where
  toRingHom := algebraMap R S
  commutes' := fun _ ↦ rfl

variable {R}

lemma isCompat_aux :
    1 ⊗ₜ[R] (TensorProduct.lid R N) m =
      (rTensor N (AlgHom.toLinearMap (algebraMap' R S))) m := by
  suffices : ∀ m,
    (rTensor N (algebraMap' R S).toLinearMap).comp (TensorProduct.lid R N).symm.toLinearMap m = 1 ⊗ₜ[R] m
  · simp [← this]
  · intro z
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProduct.lid_symm_apply, rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

theorem isCompat_apply_ground (f : PolynomialMap R M N)
    {S : Type u} [CommSemiring S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun S) (1 ⊗ₜ x) := by
  simp only [ground]
  convert f.isCompat_apply (algebraMap' R S) (1 ⊗ₜ[R] x)
  simp only [Function.comp_apply, TensorProduct.lid_symm_apply]
  rw [isCompat_aux]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

end Apply

section Module

variable {R : Type u} [CommSemiring R]
  {M N : Type _} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

noncomputable def add (f g : PolynomialMap R M N) : PolynomialMap R M N
    where
  toFun S _ _ := f.toFun S + g.toFun S
  isCompat φ := by
    ext
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [Function.comp_apply, Pi.add_apply, map_add, isCompat_apply]

#align polynomial_map.add PolynomialMap.add

instance : Zero (PolynomialMap R M N) :=
  ⟨{  toFun := fun _ => 0
      isCompat := fun _ => rfl }⟩

@[simp]
theorem zero_def (S : Type _) [CommSemiring S] [Algebra R S] :
    (0 : PolynomialMap R M N).toFun S = 0 :=
  rfl
#align polynomial_map.zero_def PolynomialMap.zero_def

instance : Inhabited (PolynomialMap R M N) :=
  ⟨Zero.zero⟩

instance : Add (PolynomialMap R M N) :=
  ⟨add⟩

@[simp]
theorem add_def (f g : PolynomialMap R M N)
    (S : Type u) [CommSemiring S] [Algebra R S] :
  (f + g).toFun S = f.toFun S + g.toFun S := rfl
#align polynomial_map.add_def PolynomialMap.add_def

@[simp]
theorem add_def_apply (f g : PolynomialMap R M N)
    (S : Type _) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
  (f + g).toFun S m = f.toFun S m + g.toFun S m := rfl
#align polynomial_map.add_def_apply PolynomialMap.add_def_apply

instance addCommMonoid : AddCommMonoid (PolynomialMap R M N)
    where
  add := Add.add
  add_assoc f g h := by ext ; simp only [add_def, add_assoc]
  zero := Zero.zero
  zero_add f := by ext ; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext ; simp only [add_def, add_zero, zero_def]
  nsmul n f :=
    { toFun := fun S _ _ => n • (f.toFun S)
      isCompat := fun φ => by
        ext m
        simp only [isCompat_apply, map_nsmul, Function.comp_apply, Pi.smul_apply] }
  nsmul_zero f := by ext ; simp only [zero_smul, Pi.smul_apply]; rfl
  nsmul_succ n f := by
    ext
    simp only [Pi.smul_apply, add_def_apply, add_comm _ 1]
    simp only [add_smul, one_smul]
  add_comm f g := by ext ; simp only [add_def, add_comm]
#align polynomial_map.add_comm_monoid PolynomialMap.addCommMonoid

def smul (r : R) (f : PolynomialMap R M N) : PolynomialMap R M N
    where
  toFun S _ _ := r • f.toFun S
  isCompat φ := by
    ext m
    simp only [Function.comp_apply, Pi.smul_apply, map_smul, isCompat_apply]
#align polynomial_map.smul PolynomialMap.smul

instance hasSmul : SMul R (PolynomialMap R M N) :=
  ⟨smul⟩
#align polynomial_map.has_smul PolynomialMap.hasSmul

theorem smul_def (f : PolynomialMap R M N)
    (r : R) (S : Type u) [CommSemiring S] [Algebra R S] :
  (r • f).toFun S = r • f.toFun S :=
  rfl
#align polynomial_map.smul_def PolynomialMap.smul_def

instance : MulAction R (PolynomialMap R M N)
    where
  one_smul f := by ext ; simp only [smul_def, one_smul]
  mul_smul a b f := by ext ; simp only [smul_def, mul_smul]

instance : DistribMulAction R (PolynomialMap R M N)
    where
  smul_zero a := rfl
  smul_add a f g := by ext ; simp only [smul_def, add_def, smul_add]

instance module : Module R (PolynomialMap R M N)
    where
  add_smul a b f := by ext ; simp only [smul_def, add_def, add_smul]
  zero_smul f := by ext ; simp only [smul_def, zero_smul] ; rfl
#align polynomial_map.module PolynomialMap.module

end Module

section Comp

variable {R M N : Type _} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable {P : Type _} [AddCommMonoid P] [Module R P]

def comp (g : PolynomialMap R N P) (f : PolynomialMap R M N) :
  PolynomialMap R M P where
  toFun S _ _ := (g.toFun S).comp (f.toFun S)
  isCompat φ := by ext ; simp only [Function.comp_apply, isCompat_apply]
#align polynomial_map.comp PolynomialMap.comp

theorem comp_toFun (f : PolynomialMap R M N) (g : PolynomialMap R N P)
    (S : Type _) [CommSemiring S] [Algebra R S] :
  (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := rfl
#align polynomial_map.comp_to_fun PolynomialMap.comp_toFun

theorem comp_apply (f : PolynomialMap R M N) (g : PolynomialMap R N P)
    (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
  (g.comp f).toFun S m = (g.toFun S) (f.toFun S m) := rfl
#align polynomial_map.comp_apply PolynomialMap.comp_apply

variable {Q : Type _} [AddCommMonoid Q] [Module R Q]

theorem comp_assoc (f : PolynomialMap R M N) (g : PolynomialMap R N P)
    (h : PolynomialMap R P Q) :
  h.comp (g.comp f) = (h.comp g).comp f := by
  ext; simp only [comp_toFun] ; rfl
#align polynomial_map.comp_assoc PolynomialMap.comp_assoc

end Comp

section Homogeneous

universe u

variable {R M N : Type _} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A polynomial map is homogeneous if all its toFun are homogeneous -/
def IsHomogeneousOfDegree
    (p : ℕ) (f : PolynomialMap R M N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : S) (m : S ⊗[R] M),
    f.toFun S (r • m) = r ^ p • f.toFun S m
#align polynomial_map.is_homogeneous_of_degree PolynomialMap.IsHomogeneousOfDegree

lemma isHomogeneousOfDegree_iff (p : ℕ) (f : PolynomialMap R M N) :
    IsHomogeneousOfDegree p f ↔ ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : S) (m : S ⊗[R] M), f.toFun S (r • m) = r ^ p • f.toFun S m := by
  rfl

theorem IsHomogeneousOfDegree_add (p : ℕ) {f g : PolynomialMap R M N}
    (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree p) :
    (f + g).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsHomogeneousOfDegree_smul (p : ℕ) (r : R) {f : PolynomialMap R M N}
    (hf : f.IsHomogeneousOfDegree p) : (r • f).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm r (s ^ p) (toFun f S m)

/-- The submodule of Homogeneous Polynomial maps -/
def grade (p : ℕ) : Submodule R (PolynomialMap R M N) where
  carrier   := IsHomogeneousOfDegree p
  add_mem' hf hg := IsHomogeneousOfDegree_add p hf hg
  smul_mem' r f hf := IsHomogeneousOfDegree_smul p r hf
  zero_mem' := by
    intro S _ _ r _
    simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_grade (f : PolynomialMap R M N) (p : ℕ) :
    f ∈ grade p ↔ IsHomogeneousOfDegree p f := by
  rfl

end Homogeneous

section ConstantMap

variable {R : Type u} [CommSemiring R]
  {M N : Type _} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

open scoped TensorProduct

def ofConstant (n : N) : PolynomialMap R M N where
  toFun S _ _ _:= TensorProduct.tmul R 1 n
  isCompat φ := by
    ext
    simp only [Function.comp_apply, rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

#align polynomial_map.of_constant PolynomialMap.ofConstant

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
def ofConstantHom : N →ₗ[R] (grade 0 : Submodule R (PolynomialMap R M N)) := {
  toFun := fun n ↦ {
    val := ofConstant n
    property := by
      simp only [grade, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
      intro S _ _ r sm
      simp only [pow_zero, one_smul]
      rfl }
  map_add'  := fun x y ↦ by
    simp only [AddSubmonoid.mk_add_mk, Subtype.mk.injEq, ofConstant]
    ext
    simp only [add_def_apply, TensorProduct.tmul_add]
  map_smul' := fun r x ↦ by
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq, ofConstant,
      TensorProduct.tmul_smul]
    rfl }

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
def ofConstantEquiv : N ≃ₗ[R] (grade 0 : Submodule R (PolynomialMap R M N)) := {
  ofConstantHom with
  invFun    := fun f ↦ f.val.ground 0
  left_inv  := fun x ↦ by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, ground, Function.comp_apply, map_zero,
      ofConstantHom, coe_mk, AddHom.coe_mk, ofConstant, TensorProduct.lid_tmul, one_smul]
  right_inv := fun x ↦ by
    obtain ⟨f, hf⟩ := x
    simp only [mem_grade, isHomogeneousOfDegree_iff] at hf
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    rw [Subtype.ext_iff]
    rw [Subtype.coe_mk]
    simp [ofConstantHom, ground]
    ext S _ _ m
    conv_rhs =>
      rw [← one_smul (M := S) (f.toFun S m), ← pow_zero 0, ← hf S _ m]
      rw [zero_smul]
    --  rw [← TensorProduct.tmul_zero M 1]
    -- set n := ((TensorProduct.lid R N) (f.toFun R (0 : R ⊗[R] M)))
    have := f.isCompat_apply (algebraMap' R S) 0
    simp only [map_zero] at this
    rw [← this]
    simp [ofConstant]
    rw [isCompat_aux] }

end ConstantMap

section Linear

open scoped TensorProduct

variable {R : Type u} [CommSemiring R]
  {M N : Type _} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

def ofLinearMap (v : M →ₗ[R] N) : PolynomialMap R M N where
  toFun S _ _ := v.baseChange S
  isCompat φ := by
    ext
    simp only [← LinearMap.comp_apply, baseChange_eq_ltensor, Function.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]
#align polynomial_map.of_linear_map PolynomialMap.ofLinearMap

theorem ofLinearMap_toFun (u : M →ₗ[R] N)
    (S : Type _) [CommSemiring S] [Algebra R S] :
  (ofLinearMap u).toFun S = baseChange S u := rfl
#align polynomial_map.of_linear_map_to_fun PolynomialMap.ofLinearMap_toFun

def ofLinearMapHom :
  (M →ₗ[R] N) →ₗ[R] (grade 1 : Submodule R (PolynomialMap R M N))
    where
  toFun := fun u ↦ {
    val := ofLinearMap u
    property := sorry }
  map_add' u v := by
    ext S _ _ m
    simp only [ofLinearMap_toFun, baseChange_add, add_apply, AddSubmonoid.mk_add_mk, add_def_apply]
  map_smul' a v := by
    ext S _ _ m
    simp only [smul_def, ofLinearMap_toFun, baseChange_smul]
    rfl
#align polynomial_map.of_linear_map_hom PolynomialMap.ofLinearMapHom

theorem ofLinearMapHom_apply (v : M →ₗ[R] N) :
  ofLinearMapHom v = ofLinearMap v := rfl
#align polynomial_map.of_linear_map_hom_apply PolynomialMap.ofLinearMapHom_apply

def ofLinearMapEquiv :
    (M →ₗ[R] N) ≃ₗ[R] (grade 1 : Submodule R (PolynomialMap R M N)) :=
  { ofLinearMapHom with
    invFun := sorry
    left_inv := sorry
    right_inv := sorry }

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

def of_multilinear_map_to_fun (u : multilinear_map A M N)
  (R : Type*) [comm_semiring R] [algebra A R] : false := sorry


def of_multilinear_map : (multilinear_map A M N)
  →ₗ[A] (polynomial_map A (Π i, M i) N) := {
to_fun := of_multilinear_map_to_fun,
map_add' := sorry,
map_smul' := sorry }


end multilinear
-/
section LocallyFinite

variable {R : Type u} [CommSemiring R]
  {M N : Type _} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

def LocFinsupp {ι : Type _} (f : ι → PolynomialMap R M N) :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M),
    (Function.support fun i => (f i).toFun S m).Finite
#align polynomial_map.locfinsupp PolynomialMap.LocFinsupp

variable (R M N)

def withLocFinsupp (ι : Type _) :
  Submodule R (ι → PolynomialMap R M N) where
  carrier := LocFinsupp
  add_mem' := by
    intro a b ha hb S _ _ m
    exact Set.Finite.subset (Set.finite_union.mpr ⟨ha S m, hb S m⟩)
      (Function.support_add _ _)
  zero_mem' := by
    simp only
    intro R _ _ _
    simp only [Pi.zero_apply, zero_def, support_zero, Set.finite_empty]
  smul_mem' a f hf S _ _ m :=
    Set.Finite.subset (hf S m) (Function.support_smul_subset_right _ _)
#align polynomial_map.with_locfinsupp PolynomialMap.withLocFinsupp

namespace LocFinsupp

variable {R M N}

noncomputable def sum {ι : Type _} (f : ι → PolynomialMap R M N)
    (hf : LocFinsupp f) :
  PolynomialMap R M N where
  toFun S _ _ m := (Finsupp.ofSupportFinite _ (hf S m)).sum fun _ m => m
  isCompat {S _ _ S' _ _} φ := by
    ext m
    simp only [Function.comp_apply, map_finsupp_sum]
    rw [Finsupp.sum]
    suffices _ ⊆ (hf S m).toFinset by
      rw [Finsupp.sum_of_support_subset _ this]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.ofSupportFinite_coe, _root_.map_sum, isCompat_apply]
      · intro i _; rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply]
      intro hi
      rw [hi, map_zero]
#align polynomial_map.locfinsupp.sum PolynomialMap.LocFinsupp.sum

theorem sum_eq {ι : Type _} (f : ι → PolynomialMap R M N)
    (hf : LocFinsupp f)
    (S : Type _) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
  (LocFinsupp.sum f hf).toFun S m =
    (Finsupp.ofSupportFinite _ (hf S m)).sum fun _ m => m := rfl
#align polynomial_map.locfinsupp.sum_eq PolynomialMap.LocFinsupp.sum_eq

end LocFinsupp

--TODO: I don't think this is in the right namespace, but I don't know how to rename it.
noncomputable def LinearMap.LocFinsupp.sum {ι : Type _} [DecidableEq ι] :
    withLocFinsupp R M N ι →ₗ[R] PolynomialMap R M N
    where
  toFun fhf := PolynomialMap.LocFinsupp.sum fhf.val fhf.prop
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext S _ _ m
    skip
    simp only [AddMemClass.mk_add_mk, PolynomialMap.LocFinsupp.sum_eq, Pi.add_apply, add_def_apply]
    rw [@Finsupp.sum_of_support_subset _ _ _ _ _ _ ((hf S m).toFinset ∪ (hg S m).toFinset),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_left _ _),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_right _ _), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    all_goals try intro i hi; rfl
    · intro x
      simp only [Finsupp.ofSupportFinite_support, Set.Finite.mem_toFinset,
        Function.mem_support, Ne.def, Finset.mem_union]
      rw [← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' a fhf := by
    ext S _ _ m
    skip
    simp only [smul_def, PolynomialMap.LocFinsupp.sum_eq, Submodule.coe_smul_of_tower,
      Pi.smul_apply, RingHom.id_apply]
    rw [Finsupp.sum_of_support_subset]
    · rw [Finsupp.smul_sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, SetLike.val_smul, Pi.smul_apply, smul_def, Finsupp.mem_support_iff, ne_eq, not_imp_not, PolynomialMap.smul_def]
      intro hi
      rw [hi, smul_zero]
    · intro i _ ; rfl
#align polynomial_map.linear_map.locfinsupp.sum PolynomialMap.LinearMap.LocFinsupp.sum

end LocallyFinite

section BaseChange

/-

# Base Change

The goal is to define a base change map
  `PolynomialMap R M N → PolynomialMap R' (R' ⊗[R] M) (R' ⊗[R] N)``
when M and N are R-modules and R' is an R-algebra (commutative)

This requires to simplify the tensor product
  `S' ⊗[R'] (R' ⊗[R] M)`
to
  `S' ⊗[R] M`

an S'-isomorphism which Mathlib doesn't know (yet)

What follows is draft

-/
variable {R : Type u} {M N : Type _} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable {R' : Type u} [CommSemiring R'] [Algebra R R']
variable {S' : Type u} [CommSemiring S'] [Algebra R' S']

variable [Algebra R S'] [IsScalarTower R R' S']

def baseChange_include : M →ₗ[R] R' ⊗[R] M := {
  toFun     := fun m ↦ 1 ⊗ₜ[R] m
  map_add'  := fun x y ↦ TensorProduct.tmul_add 1 x y
  map_smul' := fun r m  ↦ by
    simp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, ← TensorProduct.smul_tmul]
    rfl }

example : S' ⊗[R'] (R' ⊗[R] M) →ₗ[S'] S' ⊗[R] M := by
  apply TensorProduct.AlgebraTensorModule.lift {
    toFun := fun s' ↦ {
      toFun := TensorProduct.lift {
        toFun := fun r' ↦ r' • baseChange_include
        map_add' := fun a b ↦ by simp only [add_smul]
        map_smul' := fun a b ↦ by
          simp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, smul_assoc] }
      map_add' := fun x y ↦ by rw [map_add]
      map_smul' := fun r x ↦ by
        simp only [RingHom.id_apply]
        sorry }
    map_add'  := fun x y ↦ by
      sorry
    map_smul' := sorry
  }

--Universe error
def baseChange (f : PolynomialMap R M N) : PolynomialMap R' (R' ⊗[R] M) (R' ⊗[R] N) where
  toFun S' _ _ := by
    /- have : Algebra R S' := RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    let fS' := toFun f S'
    let u := Algebra.TensorProduct.rid R' S' -/

    sorry
  isCompat := sorry

end BaseChange


end PolynomialMap

end
