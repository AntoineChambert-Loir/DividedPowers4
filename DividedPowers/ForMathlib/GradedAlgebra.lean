/- Copyright 2022 ACL & MIdFF
! This file was ported from Lean 3 source module graded_algebra
-/
import Mathlib.Algebra.Module.GradedModule

section DirectSum

universe u v w

variable {ι : Type v} [DecidableEq ι]

section Mk

variable {β : ι → Type w} [∀ i : ι, AddCommMonoid (β i)]

theorem DirectSum.mk_apply_of_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι}
    (hn : n ∈ s) : DirectSum.mk β s f n = f ⟨n, hn⟩ := by
  dsimp only [Finset.coe_sort_coe, mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk, DFinsupp.mk_apply]
  rw [dif_pos hn]
#align direct_sum.mk_apply_of_mem DirectSum.mk_apply_of_mem

theorem DirectSum.mk_apply_of_not_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι}
    (hn : n ∉ s) : DirectSum.mk β s f n = 0 := by
  dsimp only [Finset.coe_sort_coe, mk, AddMonoidHom.coe_mk, ZeroHom.coe_mk, DFinsupp.mk_apply] 
  rw [dif_neg hn]
#align direct_sum.mk_apply_of_not_mem DirectSum.mk_apply_of_not_mem

end Mk

section Internal

variable {M : Type w} [DecidableEq M] [AddCommMonoid M]

theorem DirectSum.coeAddMonoidHom_eq_dfinsupp_sum {M : Type w} [DecidableEq M] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (x : DirectSum ι fun i => A i) :
    DirectSum.coeAddMonoidHom A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [DirectSum.coeAddMonoidHom, DirectSum.toAddMonoid, DFinsupp.liftAddHom, AddEquiv.coe_mk,
    Equiv.coe_fn_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [AddSubmonoidClass.coe_subtype]
#align direct_sum.coe_add_monoid_hom_eq_dfinsupp_sum DirectSum.coeAddMonoidHom_eq_dfinsupp_sum

theorem DirectSum.coeLinearMap_eq_dfinsupp_sum {R : Type u} [Semiring R] [Module R M]
    (A : ι → Submodule R M) (x : DirectSum ι fun i => A i) :
    DirectSum.coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk, 
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coeSubtype]
#align direct_sum.coe_linear_map_eq_dfinsupp_sum DirectSum.coeLinearMap_eq_dfinsupp_sum

theorem DirectSum.support_subset (A : ι → AddSubmonoid M) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑(DFinsupp.support x) :=
  by
  intro m
  rw [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not]
  intro hm'
  rw [hm', AddSubmonoid.coe_zero]
#align direct_sum.support_subset DirectSum.support_subset

theorem DirectSum.support_subset_submodule (R : Type _) [CommSemiring R] [Module R M]
    (A : ι → Submodule R M) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑(DFinsupp.support x) :=
  by
  intro m
  rw [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not]
  intro hm'
  simp only [hm', Submodule.coe_zero]
#align direct_sum.support_subset_submodule DirectSum.support_subset_submodule

theorem DirectSum.finite_support (A : ι → AddSubmonoid M) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)).Finite :=
  Set.Finite.subset (DFinsupp.support x : Set ι).toFinite (DirectSum.support_subset _ x)
#align direct_sum.finite_support DirectSum.finite_support

end Internal

end DirectSum

section

theorem LinearMap.map_finsum {α R S M N : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] {f : α → M} (g : M →ₛₗ[σ] N)
    (hf : (Function.support f).Finite) :
    g (finsum fun i : α => f i) = finsum fun i : α => g (f i) :=
  by
  rw [← LinearMap.toAddMonoidHom_coe]
  exact AddMonoidHom.map_finsum _ hf
#align linear_map.map_finsum LinearMap.map_finsum

end

noncomputable section

section DirectSum

open DirectSum

/- Given an R-algebra A and a family (ι → submodule R A) of submodules
parameterized by an additive monoid
and statisfying `set_like.graded_monoid M` (essentially, is multiplicative)
such that `direct_sum.is_internal M` (A is the direct sum of the M i),
we endow A with the structure of a graded algebra.
The submodules are the *homogeneous* parts -/
variable (R : Type _) [CommSemiring R] (A : Type _) [CommSemiring A] [Algebra R A]

variable (ι : Type _) [DecidableEq ι]

variable (M : ι → Submodule R A) [AddMonoid ι] [SetLike.GradedMonoid M]

variable {R A ι M}

-- The following lines were given on Zulip by Adam Topaz
def DirectSum.IsInternal.coeAlgIso (hM : DirectSum.IsInternal M) :
    (DirectSum ι fun i => ↥(M i)) ≃ₐ[R] A :=
  { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes' := fun r => by simp }
#align direct_sum.is_internal.coe_alg_iso DirectSum.IsInternal.coeAlgIso

def DirectSum.IsInternal.gradedAlgebra (hM : DirectSum.IsInternal M) : GradedAlgebra M :=
  {-- (coe_alg_iso_of_is_internal hM).symm,
    -- (coe_alg_iso_of_is_internal hM).symm.left_inv,
    -- (coe_alg_iso_of_is_internal hM).left_inv,
    (inferInstance :
      SetLike.GradedMonoid M) with
    decompose' := hM.coeAlgIso.symm
    left_inv := hM.coeAlgIso.symm.left_inv
    right_inv := hM.coeAlgIso.left_inv }
#align direct_sum.is_internal.graded_algebra DirectSum.IsInternal.gradedAlgebra

def DirectSum.Decomposition.gradedAlgebra (dM : DirectSum.Decomposition M) : GradedAlgebra M :=
  { (inferInstance : SetLike.GradedMonoid M) with toDecomposition := dM }
#align direct_sum.decomposition.graded_algebra DirectSum.Decomposition.gradedAlgebra

end DirectSum

