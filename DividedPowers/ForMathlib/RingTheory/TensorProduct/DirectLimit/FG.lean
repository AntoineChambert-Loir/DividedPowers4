import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Adjoin.FG
--import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.Algebra.DirectSum.Internal

/- # Tensor products and finitely generated submodules

* `Submodules_fg_equiv` proves that a module is the direct limit
of its finitely generated submodules, with respect to the inclusion maps

* `rTensor_fgEquiv` deduces that a tensor product `M ⊗[R] N`
is the direct limit of the modules `P ⊗[R] N`, for all finitely generated
submodules `P`, with respect to the maps deduced from the inclusions

## TODO

* Fix namespaces, add docstrings

* The results are valid in the context of `AddCommMonoid M` over a `Semiring`.
However,  tensor products in mathlib require commutativity of the scalars,
and direct limits of modules are restricted to modules over rings.

* Provide the analogous results for `lTensor`, and both sides at the same time.

-/

open Submodule LinearMap

section Semiring

universe u v
variable {R : Type u} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

--  In PR #26717
/- theorem Subalgebra.FG.sup {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {A A' : Subalgebra R S} (hA : Subalgebra.FG A) (hA' : Subalgebra.FG A') :
    Subalgebra.FG (A ⊔ A') :=
  let ⟨s, hs⟩ := Subalgebra.fg_def.1 hA
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hA'
  Subalgebra.fg_def.2 ⟨s ∪ s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩ -/

/-- The directed system of finitely generated submodules of `M` -/
def DirectedSystem.Submodule_fg :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (F := fun P ↦ P.val)
    (f := fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

instance : SemilatticeSup {P : Submodule R M // P.FG} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

instance : Inhabited {P : Submodule R M // P.FG} where
  default := ⟨⊥, fg_bot⟩

variable (R M) in
/-- Any module is the direct limit of its finitely generated submodules -/
noncomputable def Submodules_fg_equiv [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (ι := {P : Submodule R M // P.FG})
      (G := fun P ↦ P.val)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P ↦ P.val.subtype) (fun _ _ _ _ ↦ rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P ↦ Submodule.injective_subtype P.val),
      fun x ↦ ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩,
         by simp⟩⟩

end Semiring

section TensorProducts

open TensorProduct

universe u v

variable (R : Type u) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Given a directed system of `R`-modules, tensor it on the right gives a directed system -/
theorem DirectedSystem.rTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ (F i) ⊗[R] N) (fun _ _ h ↦ LinearMap.rTensor N (f h)) where
  map_self i t := by
    rw [← LinearMap.id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `P` ranges over finitely generated submodules of `M`,
  the modules of the form `P ⊗[R] N` form a directed system. -/
instance rTensor_fg_directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
    (fun ⦃_ _⦄ h ↦ LinearMap.rTensor N (Submodule.inclusion h)) :=
  DirectedSystem.rTensor R N DirectedSystem.Submodule_fg

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all finitely generated submodules of `M`. -/
noncomputable def rTensor_fg_equiv [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
      (fun ⦃P Q⦄ (h : P ≤ Q)  ↦ (Submodule.inclusion h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodules_fg_equiv R M).rTensor N)

theorem rTensor_fgEquiv_of  [DecidableEq {P : Submodule R M // P.FG}]
    {P : {P : Submodule R M // P.FG}} (u : P ⊗[R] N) :
    (rTensor_fg_equiv R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ (Submodule.inclusion h).rTensor N) P) u)
      = (LinearMap.rTensor N (Submodule.subtype P)) u := by
  suffices (rTensor_fg_equiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ LinearMap.rTensor N (Submodule.inclusion hPQ)) P)
      = LinearMap.rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [rTensor_fg_equiv, Submodules_fg_equiv]

theorem rTensor_fgEquiv_of' [DecidableEq {P : Submodule R M // P.FG}]
    (P : Submodule R M) (hP : Submodule.FG P) (u : P ⊗[R] N) :
    (rTensor_fg_equiv R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ LinearMap.rTensor N (Submodule.inclusion h)) ⟨P, hP⟩) u)
      = (LinearMap.rTensor N (Submodule.subtype P)) u :=
  by apply rTensor_fgEquiv_of

/-- Given a directed system of `R`-modules, tensor it on the left gives a directed system -/
theorem DirectedSystem.lTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ M ⊗[R] (F i)) (fun _ _ h ↦ LinearMap.lTensor M (f h)) where
  map_self i t := by
    rw [← LinearMap.id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `Q` ranges over finitely generated submodules of `N`,
  the modules of the form `M ⊗[R] Q` form a directed system. -/
instance lTensor_fg_directedSystem :
    DirectedSystem (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodule.inclusion hPQ)) :=
  DirectedSystem.lTensor R M DirectedSystem.Submodule_fg

noncomputable def lTensor_fgEquiv [DecidableEq {Q : Submodule R N // Q.FG}] :
    Module.DirectLimit (R := R) (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ (Submodule.inclusion hPQ).lTensor M) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodules_fg_equiv R N).lTensor M)

theorem lTensor_fgEquiv_of [DecidableEq {P : Submodule R N // P.FG}]
    (Q : {Q : Submodule R N // Q.FG}) (u : M ⊗[R] Q.val) :
    (lTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ (Submodule.inclusion hPQ).lTensor M) Q) u)
      = (LinearMap.lTensor M (Submodule.subtype Q.val)) u := by
  suffices (lTensor_fgEquiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodule.inclusion hPQ)) Q)
      = LinearMap.lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [lTensor_fgEquiv, Submodules_fg_equiv]

theorem lTensor_fgEquiv_of' [DecidableEq {Q : Submodule R N // Q.FG}]
    (Q : Submodule R N) (hQ : Q.FG) (u : M ⊗[R] Q) :
    (lTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodule.inclusion hPQ)) ⟨Q, hQ⟩) u)
      = (LinearMap.lTensor M (Submodule.subtype Q)) u :=
  lTensor_fgEquiv_of R M N ⟨Q, hQ⟩ u

/- @[simp] theorem Submodule.inclusion_refl {P : Submodule R M} :
      inclusion (le_refl P) = LinearMap.id := rfl

@[simp] theorem Submodule.inclusion_trans {P Q L : Submodule R M}
    (hPQ : P ≤ Q) (hQL : Q ≤ L) :
    Submodule.inclusion hQL ∘ₗSubmodule.inclusion hPQ = Submodule.inclusion (le_trans hPQ hQL) := rfl
-/

variable {R M N}

theorem TensorProduct.exists_of_fg [DecidableEq {P : Submodule R M // P.FG}] (t : M ⊗[R] N) :
    ∃ (P : Submodule R M), P.FG ∧ t ∈ LinearMap.range (LinearMap.rTensor N P.subtype) := by
  let ⟨P, u, hu⟩ := Module.DirectLimit.exists_of ((rTensor_fg_equiv R M N).symm t)
  use P.val, P.property, u
  rw [← rTensor_fgEquiv_of, hu, LinearEquiv.apply_symm_apply]

theorem TensorProduct.eq_of_fg_of_subtype_eq {P : Submodule R M} (hP : P.FG) (t t' : P ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hPQ) t' := by
  classical
  simp only [← rTensor_fgEquiv_of' R M N P hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

theorem TensorProduct.eq_zero_of_fg_of_subtype_eq_zero
    {P : Submodule R M} (hP : P.FG) (t : P ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = 0) :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t = 0 := by
  rw [← (LinearMap.rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP t _ h

theorem TensorProduct.eq_of_fg_of_subtype_eq'
    {P : Submodule R M} (hP : Submodule.FG P) (t : P ⊗[R] N)
    {P' : Submodule R M} (hP' : Submodule.FG P') (t' : P' ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P'.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q) (hP'Q : P' ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hP'Q) t' := by
  simp only [← Submodule.subtype_comp_inclusion _ _ (le_sup_left : _ ≤ P ⊔ P'),
    ← Submodule.subtype_comp_inclusion _ _ (le_sup_right : _ ≤ P ⊔ P'),
    LinearMap.rTensor_comp, LinearMap.coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') _ _ h
  use Q, le_trans le_sup_left hQ_le, le_trans le_sup_right hQ_le, hQ
  simpa [← LinearMap.comp_apply, ← LinearMap.rTensor_comp] using h

end TensorProducts

section Algebra

open TensorProduct

-- variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
--   [AddCommGroup N] [Module R N]

variable {R S N : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid N] [Module R N]

theorem TensorProduct.Algebra.exists_of_fg [DecidableEq {P : Submodule R S // P.FG}]
    (t : S ⊗[R] N) :
    ∃ (A : Subalgebra R S), Subalgebra.FG A ∧
      t ∈ LinearMap.range (LinearMap.rTensor N (Subalgebra.val A).toLinearMap) := by
  obtain ⟨P, hP, ht⟩ := TensorProduct.exists_of_fg t
  obtain ⟨s, hs⟩ := hP
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ Subalgebra.toSubmodule (Algebra.adjoin R (s : Set S)) := by
    simp only [← hs, Submodule.span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← Submodule.subtype_comp_inclusion P _ this, LinearMap.rTensor_comp] at ht
  exact LinearMap.range_comp_le_range _ _ ht

theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    {A : Subalgebra R S} (hA : Subalgebra.FG A) (t t' : A ⊗[R] N)
    (h : LinearMap.rTensor N (Subalgebra.val A).toLinearMap t
      = LinearMap.rTensor N (Subalgebra.val A).toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B), Subalgebra.FG B
      ∧ LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t' := by
  classical
  let ⟨P, hP, ⟨u, hu⟩⟩ := TensorProduct.exists_of_fg t
  let ⟨P', hP', ⟨u', hu'⟩⟩ := TensorProduct.exists_of_fg t'
  let P₁ := Submodule.map (Subalgebra.toSubmodule A).subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁
  let j : P →ₗ[R] P₁ := LinearMap.restrict (Subalgebra.toSubmodule A).subtype
      (fun p hp ↦ by
        simp only [Submodule.coe_subtype, Submodule.map_sup, P₁]
        apply Submodule.mem_sup_left
        use p; simp only [SetLike.mem_coe]; exact ⟨hp, rfl⟩)
  let j' : P' →ₗ[R] P₁ := LinearMap.restrict (Subalgebra.toSubmodule A).subtype
      (fun p hp ↦ by
        simp only [Submodule.coe_subtype, Submodule.map_sup, P₁]
        apply Submodule.mem_sup_right
        use p; simp only [SetLike.mem_coe]; exact ⟨hp, rfl⟩)
  -- we map u and u' to P₁ ⊗[R] N, getting u₁ and u'₁
  set u₁ := LinearMap.rTensor N j u with hu₁
  set u'₁ := LinearMap.rTensor N j' u' with hu'₁
  -- u₁ and u'₁ are equal in S ⊗[R] N
  have : LinearMap.rTensor N P₁.subtype u₁ = LinearMap.rTensor N P₁.subtype u'₁ := by
    rw [hu₁, hu'₁]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have hj₁ : P₁.subtype ∘ₗ j = (Subalgebra.val A).toLinearMap ∘ₗ P.subtype := by ext; rfl
    have hj'₁ : P₁.subtype ∘ₗ j' = (Subalgebra.val A).toLinearMap ∘ₗ P'.subtype := by ext; rfl
    rw [hj₁, hj'₁]
    simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [hu, hu', h]
  let ⟨P'₁, hP₁_le, hP'₁, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq hP₁ _ _ this
  let ⟨s, hs⟩ := hP'₁
  let ⟨w, hw⟩ := hA
  let B := Algebra.adjoin R ((s ∪ w : Finset S) : Set S)
  have hBA : A ≤ B := by
    simp only [B, ← hw]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use B, hBA, Subalgebra.fg_adjoin_finset _
  rw [← hu, ← hu']
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have hP'₁_le : P'₁ ≤ Subalgebra.toSubmodule B := by
    simp only [← hs, Finset.coe_union, Submodule.span_le, Subalgebra.coe_toSubmodule, B]
    exact subset_trans Set.subset_union_left Algebra.subset_adjoin
  have k : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P.subtype
    = Submodule.inclusion hP'₁_le ∘ₗ Submodule.inclusion hP₁_le ∘ₗ j := by ext; rfl
  have k' : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P'.subtype
    = Submodule.inclusion hP'₁_le ∘ₗ Submodule.inclusion hP₁_le ∘ₗ j' := by ext; rfl
  rw [k, k']
  simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [← hu₁, ← hu'₁, h]

theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq'
    {A : Subalgebra R S} (hA : Subalgebra.FG A) (t : A ⊗[R] N)
    {A' : Subalgebra R S} (hA' : Subalgebra.FG A') (t' : A' ⊗[R] N)
    (h : LinearMap.rTensor N (Subalgebra.val A).toLinearMap t
      = LinearMap.rTensor N (Subalgebra.val A').toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B) (hA'B : A' ≤ B), Subalgebra.FG B
      ∧ LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hA'B).toLinearMap t' := by
  have hj : (Subalgebra.val (A ⊔ A')).comp (Subalgebra.inclusion le_sup_left)
    = Subalgebra.val A := by ext; rfl
  have hj' : (Subalgebra.val (A ⊔ A')).comp (Subalgebra.inclusion le_sup_right)
    = Subalgebra.val A' := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.FG.sup hA hA') _ _ h
  use B, le_trans le_sup_left hB_le, le_trans le_sup_right hB_le, hB
  simpa only [← LinearMap.rTensor_comp, ← LinearMap.comp_apply] using h

-- [Mathlib.RingTheory.TensorProduct.Basic]
theorem LinearMap.rTensor_comp_baseChange_comm_apply
    {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {S : Type*} [Semiring S] [Algebra R S]
    {S' : Type*} [Semiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (t : S ⊗[R] M) (f : M →ₗ[R] N) :
    (φ.toLinearMap.rTensor N) (f.baseChange S t)  =
      (f.baseChange S') (φ.toLinearMap.rTensor M t) := by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply]

/-- Lift an element that maps to 0 -/
theorem Submodule.exists_fg_of_baseChange_eq_zero
    {R S M N : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (t : S ⊗[R] M) (ht : f.baseChange S t = 0) :
    ∃ (A : Subalgebra R S) (_ : A.FG) (u : A ⊗[R] M),
      f.baseChange A u = 0 ∧ A.val.toLinearMap.rTensor M u = t := by
  classical
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (f.baseChange _ u) 0
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseChange (↥A) u) = 0 := by
    rw [← ht, ← hu, rTensor_comp_baseChange_comm_apply]
  obtain ⟨B, hB, hAB, hu'⟩ := this hu'
  use B, hB, LinearMap.rTensor M (Subalgebra.inclusion hAB).toLinearMap u
  constructor
  · rw [← rTensor_comp_baseChange_comm_apply, hu']
  · rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← hu]
    congr

end Algebra
