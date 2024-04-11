import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
-- import DividedPowers.ForMathlib.LinearAlgebra.DirectSum.Finsupp
import DividedPowers.ForMathlib.RingTheory.TensorProduct.LinearEquiv

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

* Add the analogous results for algebras.
-/

open TensorProduct FreeAddMonoid

section Ring

variable {R : Type*} {M N : Type*}
  [Ring R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

example : Preorder {P : Submodule R M // P.FG } := inferInstance
  -- exact Subtype.preorder fun P => Submodule.FG P

variable (R M)
def Submodules_fg := { P : Submodule R M // P.FG }

instance : Nonempty (Submodules_fg R M) := by
  unfold Submodules_fg
  exact ⟨⊥, Submodule.fg_bot⟩

instance : PartialOrder (Submodules_fg R M) := by
  unfold Submodules_fg
  infer_instance

instance : Sup (Submodules_fg R M) where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩

instance : SemilatticeSup (Submodules_fg R M) where
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

example : IsDirected (Submodules_fg R M) (fun P Q ↦ P ≤ Q) := inferInstance

instance : Submodules_fg R M → Submodule R M := fun P ↦ P.val

example : Π (P : Submodules_fg R M), AddCommGroup P.val := inferInstance

example : Π (P : Submodules_fg R M), Module R P.val := inferInstance

def Submodules_fg_val :  Submodules_fg R M → Submodule R M :=
  fun P ↦ P.val

def Submodules_fg_inclusion :
    Π (P Q : Submodules_fg R M) (_ : P ≤ Q), P.val →ₗ[R] Q.val :=
  fun _ _ hPQ ↦ (Submodule.inclusion (Subtype.coe_le_coe.mpr hPQ))

theorem Submodules_fg.directedSystem :
    DirectedSystem (ι := Submodules_fg R M)
      (fun P ↦ P.val) (fun _ _ hPQ ↦ (Submodule.inclusion (Subtype.coe_le_coe.mpr hPQ))) where
  map_self' := fun _ _ _ ↦ rfl
  map_map' := fun _ _ _ ↦ rfl

open scoped Classical

noncomputable def Submodules_fg_map :
    Module.DirectLimit _ (Submodules_fg_inclusion R M) →ₗ[R] M :=
  Module.DirectLimit.lift (R := R) (ι := Submodules_fg R M)
    (G := fun P ↦ P.val)
    (f := _)
    (g := fun P ↦ P.val.subtype)
    (fun _ _ _ _ ↦ rfl)

noncomputable def Submodules_fg_equiv :
    Module.DirectLimit _ (Submodules_fg_inclusion R M) ≃ₗ[R] M := by
  apply LinearEquiv.ofBijective (Submodules_fg_map R M)
  constructor
  · apply Module.DirectLimit.lift_injective
    exact fun P ↦ Submodule.injective_subtype _
  · intro x
    let Px := (⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩ : Submodules_fg R M)
    use Module.DirectLimit.of R (Submodules_fg R M) (fun P ↦ P.val)
      (Submodules_fg_inclusion R M) Px ⟨x, Submodule.mem_span_singleton_self x⟩
    simp only [Submodules_fg_map, Module.DirectLimit.lift_of, Submodule.coeSubtype]

end Ring

section CommRing

open scoped Classical

variable {R : Type*} {M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

variable (R M N)
noncomputable def rTensor_fgEquiv : Module.DirectLimit (R := R) (ι := Submodules_fg R M)
    (fun P ↦ P.val ⊗[R] N)
    (fun P Q hPQ ↦ (Submodules_fg_inclusion R M P Q hPQ).rTensor N)
      ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodules_fg_equiv R M).rTensor N)

theorem rTensor_fgEquiv_of (P : Submodules_fg R M) (u : P.val ⊗[R] N) :
    (rTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R M) (fun P => P.val ⊗[R] N)
        (fun P Q hPQ => (Submodules_fg_inclusion R M P Q hPQ).rTensor N) P) u)
      = (LinearMap.rTensor N (Submodule.subtype P.val)) u := by
  suffices (rTensor_fgEquiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R (Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
        (fun P Q hPQ => LinearMap.rTensor N (Submodules_fg_inclusion R M P Q hPQ)) P)
      = LinearMap.rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [rTensor_fgEquiv]
  simp only [LinearEquiv.rTensor]
  simp only [congr_tmul, LinearEquiv.refl_apply]
  congr
  simp only [Submodules_fg_equiv, LinearEquiv.ofBijective_apply]
  simp only [Submodules_fg_map]
  simp only [Module.DirectLimit.lift_of]
  simp only [Submodule.coeSubtype]

def Submodules_fg_of {P : Submodule R M} (hP : Submodule.FG P) :
    Submodules_fg R M := ⟨P, hP⟩

theorem rTensor_fgEquiv_of' (P : Submodule R M) (hP : Submodule.FG P) (u : P ⊗[R] N) :
    (rTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R M) (fun P => P.val ⊗[R] N)
        (fun P Q hPQ => LinearMap.rTensor N (Submodules_fg_inclusion R M P Q hPQ)) ⟨P, hP⟩) u)
      = (LinearMap.rTensor N (Submodule.subtype P)) u :=
  rTensor_fgEquiv_of R M N ⟨P, hP⟩ u

theorem rTensor_fg_directedSystem :
    DirectedSystem (ι := Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
      (fun P Q hPQ ↦ LinearMap.rTensor N (Submodules_fg_inclusion R M P Q hPQ)) := {
  map_self' := fun P p hP ↦ by
    rw [← LinearMap.id_apply (R := R) p]
    apply DFunLike.congr_fun
    ext p n
    rfl -- needs some rw lemmas
  map_map' := fun {P Q R} hPQ hRQ p ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp
    rfl }

variable {R M N}

theorem TensorProduct.exists_of_fg (t : M ⊗[R] N) :
    ∃ (P : Submodule R M), P.FG ∧ t ∈ LinearMap.range (LinearMap.rTensor N P.subtype) := by
  let ⟨P, u, hu⟩ := Module.DirectLimit.exists_of ((rTensor_fgEquiv R M N).symm t)
  use P.val, P.property, u
  rw [← rTensor_fgEquiv_of, hu, LinearEquiv.apply_symm_apply]

theorem TensorProduct.eq_of_fg_of_subtype_eq {P : Submodule R M}
    (hP : Submodule.FG P) (t t' : P ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hPQ) t' := by
  rw [← sub_eq_zero, ← map_sub, ← rTensor_fgEquiv_of R M N ⟨P,hP⟩,
    LinearEquiv.map_eq_zero_iff] at h
  have := rTensor_fg_directedSystem R M N
  have := Module.DirectLimit.of.zero_exact h
  let ⟨Q, hPQ, h⟩ := this
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property
  simpa only [sub_eq_zero, map_sub] using h

theorem TensorProduct.eq_of_fg_of_subtype_eq'
    {P : Submodule R M} (hP : Submodule.FG P) (t : P ⊗[R] N)
    {P' : Submodule R M} (hP' : Submodule.FG P') (t' : P' ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P'.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q) (hP'Q : P' ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hP'Q) t' := by
  let P'' := P ⊔ P'
  let _hP_le := (le_sup_left : P ≤ P'')
  let _hP'_le := (le_sup_right : P' ≤ P'') -- otherwise lint complains it's unused
  rw [← Submodule.subtype_comp_inclusion _ _ _hP_le] at h
  rw [← Submodule.subtype_comp_inclusion _ _ _hP'_le] at h
  simp only [LinearMap.rTensor_comp, LinearMap.coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq
    (Submodule.FG.sup hP hP') _ _ h
  use Q, le_trans _hP_le hQ_le, le_trans _hP'_le hQ_le, hQ
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, Submodule.subtype_comp_inclusion] at h
  exact h

end CommRing

section Algebra

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N]

theorem TensorProduct.Algebra.exists_of_fg (t : S ⊗[R] N) :
    ∃ (A : Subalgebra R S), Subalgebra.FG A ∧
      t ∈ LinearMap.range (LinearMap.rTensor N (Subalgebra.val A).toLinearMap) := by
  let ⟨P, hP, ht⟩ := TensorProduct.exists_of_fg t
  obtain ⟨s, hs⟩ := hP
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ Subalgebra.toSubmodule (Algebra.adjoin R (s : Set S)) := by
    simp only [← hs, Submodule.span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← Submodule.subtype_comp_inclusion P _ this,
    LinearMap.rTensor_comp] at ht
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
        simp only [Submodule.coeSubtype, Submodule.map_sup, P₁]
        apply Submodule.mem_sup_left
        use p; simp only [SetLike.mem_coe]; exact ⟨hp, rfl⟩)
  let j' : P' →ₗ[R] P₁ := LinearMap.restrict (Subalgebra.toSubmodule A).subtype
      (fun p hp ↦ by
        simp only [Submodule.coeSubtype, Submodule.map_sup, P₁]
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
    exact subset_trans (Set.subset_union_left _ _) Algebra.subset_adjoin
  have k : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P.subtype
    = Submodule.inclusion hP'₁_le ∘ₗ Submodule.inclusion hP₁_le ∘ₗ j := by ext; rfl
  have k' : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P'.subtype
    = Submodule.inclusion hP'₁_le ∘ₗ Submodule.inclusion hP₁_le ∘ₗ j' := by ext; rfl
  rw [k, k']
  simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [← hu₁, ← hu'₁, h]

theorem Subalgebra.FG.sup
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {A A' : Subalgebra R S} (hA : Subalgebra.FG A) (hA' : Subalgebra.FG A') :
    Subalgebra.FG (A ⊔ A') :=
  let ⟨s, hs⟩ := Subalgebra.fg_def.1 hA
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hA'
  Subalgebra.fg_def.2 ⟨s ∪ s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩

theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq'
    {A : Subalgebra R S} (hA : Subalgebra.FG A) (t : A ⊗[R] N)
    {A' : Subalgebra R S} (hA' : Subalgebra.FG A') (t' : A' ⊗[R] N)
    (h : LinearMap.rTensor N (Subalgebra.val A).toLinearMap t
      = LinearMap.rTensor N (Subalgebra.val A').toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B) (hA'B : A' ≤ B), Subalgebra.FG B
      ∧ LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hA'B).toLinearMap t' := by
  let A'' := A ⊔ A'
  let hA_le := (le_sup_left : A ≤ A'')
  let hA'_le := (le_sup_right : A' ≤ A'')
  have hj : (Subalgebra.val A'').comp (Subalgebra.inclusion hA_le)
    = Subalgebra.val A := by ext; rfl
  have hj' : (Subalgebra.val A'').comp (Subalgebra.inclusion hA'_le)
    = Subalgebra.val A' := by ext; rfl
  rw [← hj, ← hj'] at h
  simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.FG.sup hA hA') _ _ h
  use B, le_trans hA_le hB_le, le_trans hA'_le hB_le, hB
  simp only [← LinearMap.rTensor_comp, ← LinearMap.comp_apply] at h
  exact h

end Algebra
