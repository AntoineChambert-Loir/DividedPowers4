/- Copyright ACL @ MIdFF 2024 -/

import DividedPowers.ForMathlib.TensorProductFinsupp
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct.Basic
--import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.FiniteType

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

/- USE Algebra.linearMap for the linearMap-/
def _root_.algebraMap' (R : Type*) [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S] : R →ₐ[R] S where
  toRingHom := algebraMap R S
  commutes' := fun _ ↦ rfl

lemma _root_.TensorProduct.includeRight_lid
  {S : Type*} [CommSemiring S] [Algebra R S]
  {M : Type*} [AddCommMonoid M] [Module R M] (m) :
    (1 : S)  ⊗ₜ[R] (TensorProduct.lid R M) m =
      (rTensor M (algebraMap' R S).toLinearMap) m := by
  suffices ∀ m, (rTensor M (algebraMap' R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 ⊗ₜ[R] m by
    simp [← this]
  intro z
  simp

end Algebra

section PolynomialMap

noncomputable section

open scoped TensorProduct

open MvPolynomial
/-
structure PolynomialMap (R : Type u) [CommSemiring R]
    (M : Type _) [AddCommMonoid M] [Module R M]
    (N : Type _) [AddCommMonoid N] [Module R N] where
  toFun' (S : Type u) [CommSemiring S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  isCompat' {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M
-/

/-- A polynomial map M → N between A-modules is a functorial family
of maps R ⊗[A] M → R ⊗[A] N, for all A-algebras R -/
@[ext]
structure PolynomialMap (R : Type u) [CommRing R]
    (M : Type _) [AddCommGroup M] [Module R M]
    (N : Type _) [AddCommGroup N] [Module R N] where
  toFun' (S : Type u) [CommRing S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  isCompat' {S : Type u} [CommRing S] [Algebra R S]
    {S' : Type u} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M
#align polynomial_map PolynomialMap

namespace PolynomialMap

section Apply

variable {R : Type u} {M N : Type _} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The map M → N associated with a PolynomialMap R M N (essentially, toFun' R)-/
noncomputable def ground (f : PolynomialMap R M N) : M → N :=
  (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

theorem isCompat_apply' (f : PolynomialMap R M N)
    {S : Type u} [CommRing S] [Algebra R S]
    {S' : Type u} [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : S ⊗[R] M) :
  (φ.toLinearMap.rTensor N) ((f.toFun' S) x) =
      (f.toFun' S') (φ.toLinearMap.rTensor M x) := by
  simpa only using _root_.congr_fun (f.isCompat' φ) x
#align polynomial_map.is_compat_apply PolynomialMap.isCompat_apply'

theorem isCompat_apply'_ground (f : PolynomialMap R M N)
    {S : Type u} [CommRing S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun' S) (1 ⊗ₜ x) := by
  simp only [ground]
  convert f.isCompat_apply' (algebraMap' R S) (1 ⊗ₜ[R] x)
  simp only [Function.comp_apply, TensorProduct.lid_symm_apply]
  rw [TensorProduct.includeRight_lid]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

end Apply

section Module

variable {R : Type u} [CommRing R]
  {M N : Type _} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

noncomputable def add (f g : PolynomialMap R M N) : PolynomialMap R M N
    where
  toFun' S _ _ := f.toFun' S + g.toFun' S
  isCompat' φ := by
    ext
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [Function.comp_apply, Pi.add_apply, map_add, isCompat_apply']
#align polynomial_map.add PolynomialMap.add

instance : Add (PolynomialMap R M N) :=
  ⟨add⟩

@[simp]
theorem add_def (f g : PolynomialMap R M N)
    (S : Type u) [CommRing S] [Algebra R S] :
  (f + g).toFun' S = f.toFun' S + g.toFun' S := rfl

@[simp]
theorem add_def_apply (f g : PolynomialMap R M N)
    (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
  (f + g).toFun' S m = f.toFun' S m + g.toFun' S m := rfl
#align polynomial_map.add_def_apply PolynomialMap.add_def_apply

instance : Zero (PolynomialMap R M N) :=
  ⟨{  toFun' := fun _ => 0
      isCompat' := fun _ => rfl }⟩

@[simp]
theorem zero_def (S : Type u) [CommRing S] [Algebra R S] :
    (0 : PolynomialMap R M N).toFun' S = 0 :=
  rfl
#align polynomial_map.zero_def PolynomialMap.zero_def

instance : Inhabited (PolynomialMap R M N) :=
  ⟨Zero.zero⟩

noncomputable def neg (f : PolynomialMap R M N) : PolynomialMap R M N where
  toFun' S _ _ := - f.toFun' S
  isCompat' φ := by
    ext t
    simp [isCompat_apply']

instance : Neg (PolynomialMap R M N) where
  neg := neg

@[simp]
theorem neg_def (f : PolynomialMap R M N)
    (S : Type u) [CommRing S] [Algebra R S] :
    (-f).toFun' S = - f.toFun' S := rfl

/- instance addCommGroup : AddCommGroup (PolynomialMap R M N)
    where
  add := Add.add
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero := Zero.zero
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f :=
    { toFun' := fun S _ _ => n • (f.toFun' S)
      isCompat' := fun φ => by
        ext m
        simp only [isCompat_apply', map_nsmul, Function.comp_apply, Pi.smul_apply] }
-/

instance addCommGroup : AddCommGroup (PolynomialMap R M N) where
  add := Add.add
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero := Zero.zero
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f :=by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := {
    toFun' := fun S _ _ => n • (f.toFun' S)
    isCompat' := fun φ => by
        ext m
        simp only [isCompat_apply', map_nsmul, Function.comp_apply, Pi.smul_apply] }
  nsmul_zero f := by ext; simp only [zero_smul, Pi.smul_apply]; rfl
  nsmul_succ n f := by
    ext
    simp only [Pi.smul_apply, add_def_apply, add_comm _ 1]
    simp only [add_smul, one_smul]
  neg := Neg.neg
  zsmul z f := {
    toFun' := fun S _ _ => z • (f.toFun' S)
    isCompat' := fun φ => by
        ext m
        simp only [isCompat_apply', map_zsmul, Function.comp_apply, Pi.smul_apply] }
  add_left_neg f := by
    ext; simp only [add_def_apply, neg_def, Pi.neg_apply, add_left_neg, zero_def, Pi.zero_apply]
  add_comm f g := by ext; simp only [add_def, add_comm]
  --sub := _
  --sub_eq_add_neg := _
  /- zsmul_zero' f := by ext; simp only [zero_smul, Pi.smul_apply]; rfl
  zsmul_succ' z f := by
    sorry
  zsmul_neg' := sorry -/



  #exit
  /- where
  add := Add.add
  add_assoc := sorry
  zero := Zero.zero
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  neg := Neg.neg
  zsmul := sorry
  add_left_neg := sorry
  add_comm := sorry -/

   /- where
  add := Add.add
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero := Zero.zero
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f :=
    { toFun' := fun S _ _ => n • (f.toFun' S)
      isCompat' := fun φ => by
        ext m
        simp only [isCompat_apply', map_nsmul, Function.comp_apply, Pi.smul_apply] }
  nsmul_zero f := by ext; simp only [zero_smul, Pi.smul_apply]; rfl
  nsmul_succ n f := by
    ext
    simp only [Pi.smul_apply, add_def_apply, add_comm _ 1]
    simp only [add_smul, one_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]
  add_left_neg f := by
    ext; simp only [add_def_apply, neg_def, Pi.neg_apply, add_left_neg, zero_def, Pi.zero_apply]
  zsmul z f := {
    toFun' := fun S _ _ => z • (f.toFun' S)
    isCompat' := fun φ => by
        ext m
        simp only [isCompat_apply', map_zsmul, Function.comp_apply, Pi.smul_apply]
  } -/
#align polynomial_map.add_comm_monoid PolynomialMap.addCommGroup

def smul (r : R) (f : PolynomialMap R M N) : PolynomialMap R M N where
  toFun' S _ _ := r • f.toFun' S
  isCompat' φ := by
    ext m
    simp only [Function.comp_apply, Pi.smul_apply, map_smul, isCompat_apply']
#align polynomial_map.smul PolynomialMap.smul

instance hasSmul : SMul R (PolynomialMap R M N) :=
  ⟨smul⟩
#align polynomial_map.has_smul PolynomialMap.hasSmul

theorem smul_def (f : PolynomialMap R M N)
    (r : R) (S : Type u) [CommRing S] [Algebra R S] :
    (r • f).toFun' S = r • f.toFun' S :=
  rfl
#align polynomial_map.smul_def PolynomialMap.smul_def

instance : MulAction R (PolynomialMap R M N) where
  one_smul f := by ext; simp only [smul_def, one_smul]
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

instance : DistribMulAction R (PolynomialMap R M N) where
  smul_zero a := rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]

instance module : Module R (PolynomialMap R M N) where
  add_smul a b f := by ext; simp only [smul_def, add_def, add_smul]
  zero_smul f := by ext; simp only [smul_def, zero_smul] ; rfl
#align polynomial_map.module PolynomialMap.module

end Module

section Comp

variable {R M N : Type _} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {P : Type _} [AddCommGroup P] [Module R P]

def comp (g : PolynomialMap R N P) (f : PolynomialMap R M N) :
  PolynomialMap R M P where
  toFun' S _ _ := (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']
#align polynomial_map.comp PolynomialMap.comp

theorem comp_toFun' (f : PolynomialMap R M N) (g : PolynomialMap R N P)
    (S : Type _) [CommRing S] [Algebra R S] :
  (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S) := rfl
#align polynomial_map.comp_to_fun PolynomialMap.comp_toFun'

theorem comp_apply (f : PolynomialMap R M N) (g : PolynomialMap R N P)
    (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
  (g.comp f).toFun' S m = (g.toFun' S) (f.toFun' S m) := rfl
#align polynomial_map.comp_apply PolynomialMap.comp_apply

variable {Q : Type _} [AddCommGroup Q] [Module R Q]

theorem comp_assoc (f : PolynomialMap R M N) (g : PolynomialMap R N P)
    (h : PolynomialMap R P Q) :
  h.comp (g.comp f) = (h.comp g).comp f := by
  ext; simp only [comp_toFun'] ; rfl
#align polynomial_map.comp_assoc PolynomialMap.comp_assoc

end Comp

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

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

def LocFinsupp {ι : Type*} (f : ι → PolynomialMap R M N) :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M),
    (Function.support fun i => (f i).toFun' S m).Finite
#align polynomial_map.locfinsupp PolynomialMap.LocFinsupp

def withLocFinsupp (ι : Type*) : Submodule R (ι → PolynomialMap R M N) where
  carrier := LocFinsupp
  add_mem' := by
    intro a b ha hb S _ _ m
    exact Set.Finite.subset (Set.finite_union.mpr ⟨ha S m, hb S m⟩)
      (Function.support_add _ _)
  zero_mem' := by
    simp only
    intro R _ _ _
    simp only [Pi.zero_apply, zero_def, Function.support_zero, Set.finite_empty]
  smul_mem' a f hf S _ _ m :=
    Set.Finite.subset (hf S m) (Function.support_smul_subset_right _ _)
#align polynomial_map.with_locfinsupp PolynomialMap.withLocFinsupp

example {ι : Type*} : Module R (withLocFinsupp ι : Submodule R (ι → PolynomialMap R M N)) :=
  inferInstance

namespace LocFinsupp

noncomputable def sum {ι : Type*} (f : ι → PolynomialMap R M N)
    (hf : LocFinsupp f) :
  PolynomialMap R M N where
  toFun' S _ _ m := (Finsupp.ofSupportFinite _ (hf S m)).sum fun _ m => m
  isCompat' {S _ _ S' _ _} φ := by
    ext m
    simp only [Function.comp_apply, map_finsupp_sum]
    rw [Finsupp.sum]
    suffices _ ⊆ (hf S m).toFinset by
      rw [Finsupp.sum_of_support_subset _ this]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.ofSupportFinite_coe, _root_.map_sum, isCompat_apply']
      · intro i _; rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply']
      intro hi
      rw [hi, map_zero]
#align polynomial_map.locfinsupp.sum PolynomialMap.LocFinsupp.sum

theorem sum_eq {ι : Type _} (f : ι → PolynomialMap R M N)
    (hf : LocFinsupp f)
    (S : Type _) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
  (LocFinsupp.sum f hf).toFun' S m =
    (Finsupp.ofSupportFinite _ (hf S m)).sum fun _ m => m := rfl
#align polynomial_map.locfinsupp.sum_eq PolynomialMap.LocFinsupp.sum_eq

end LocFinsupp

--TODO: I don't think this is in the right namespace, but I don't know how to rename it.
noncomputable def LinearMap.LocFinsupp.sum {ι : Type _} [DecidableEq ι] :
    (withLocFinsupp ι : Submodule R (ι → PolynomialMap R M N))
      →ₗ[R] PolynomialMap R M N where
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
variable {R : Type u} {M N : Type _} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {S' : Type u} [CommRing S'] [Algebra R' S']

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
  toFun' S' _ _ := by
    /- have : Algebra R S' := RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    let fS' := toFun' f S'
    let u := Algebra.TensorProduct.rid R' S' -/

    sorry
  isCompat' := sorry

end BaseChange


end PolynomialMap

end
