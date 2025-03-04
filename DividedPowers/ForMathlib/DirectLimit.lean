import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Adjoin.FG

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

open TensorProduct FreeAddMonoid

section Semiring

variable {R : Type*} {M N : Type*}
  [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

example : Preorder {P : Submodule R M // P.FG } := inferInstance
  -- exact Subtype.preorder fun P ↦ Submodule.FG P

variable (R M)
abbrev Submodules_fg := { P : Submodule R M // P.FG }

-- def Submodules_fg_of {P : Submodule R M} (hP : Submodule.FG P) :
--     Submodules_fg R M := ⟨P, hP⟩

instance : Inhabited (Submodules_fg R M) := ⟨⊥, Submodule.fg_bot⟩

example : PartialOrder (Submodules_fg R M) := inferInstance

/- instance : Max (Submodules_fg R M) where
  max := fun P Q ↦ ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩ -/

instance : SemilatticeSup (Submodules_fg R M) where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

example : IsDirected (Submodules_fg R M) (fun P Q ↦ P ≤ Q) := inferInstance

instance : Submodules_fg R M → Submodule R M := fun P ↦ P.val

example : Π (P : Submodules_fg R M), AddCommMonoid P.val := inferInstance

example : Π (P : Submodules_fg R M), Module R P.val := inferInstance

def Submodules_fg_val :  Submodules_fg R M → Submodule R M :=
  fun P ↦ P.val

variable {R M} in
/-- The inclusion of two finitely generated submodules, as a linear map between the submodules -/
def Submodules_fg_inclusion ⦃P Q : Submodules_fg R M⦄ (h : P ≤ Q) :
    P.val →ₗ[R] Q.val :=
  Submodule.inclusion (Subtype.coe_le_coe.mpr h)

theorem Submodules_fg.directedSystem :
    DirectedSystem (ι := Submodules_fg R M) (fun P ↦ P.val)
      (fun _ _ hPQ ↦ (Submodule.inclusion (Subtype.coe_le_coe.mpr hPQ))) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

open scoped Classical

variable {R M} in
noncomputable def Submodules_fg_map :
    Module.DirectLimit (fun P : Submodules_fg R M ↦ ↥P.val) (Submodules_fg_inclusion) →ₗ[R] M :=
  Module.DirectLimit.lift (R := R) (ι := Submodules_fg R M)
    (G := fun P ↦ P.val)
    (f := Submodules_fg_inclusion)
    (g := fun P ↦ P.val.subtype)
    (fun _ _ _ _ ↦ rfl)

variable {R M} in
theorem Submodules_fg_map_injective :
    Function.Injective (Submodules_fg_map (R := R) (M := M)) := by
  apply Module.DirectLimit.lift_injective _ _
    (fun P : Submodules_fg R M ↦ Submodule.injective_subtype P.val)

variable {R M} in
theorem Submodules_fg_map_surjective :
    Function.Surjective (Submodules_fg_map (R := R) (M := M)) := fun x ↦ by
  let Px := (⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩ : Submodules_fg R M)
  use Module.DirectLimit.of R (Submodules_fg R M) (fun P ↦ P.val)
    Submodules_fg_inclusion Px ⟨x, Submodule.mem_span_singleton_self x⟩
  simp only [Submodules_fg_map, Module.DirectLimit.lift_of, Submodule.coe_subtype]

/-- Any module is the direct limit of its finitely generated submodules -/
noncomputable def Submodules_fg_equiv :
    Module.DirectLimit _ (Submodules_fg_inclusion (R := R) (M := M)) ≃ₗ[R] M :=
  LinearEquiv.ofBijective Submodules_fg_map
    ⟨Submodules_fg_map_injective, Submodules_fg_map_surjective⟩

end Semiring

section CommSemiring

open scoped Classical

variable (R : Type*) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all finitely generated submodules of `M`. -/
noncomputable def rTensor_fgEquiv :
    Module.DirectLimit (R := R) (ι := Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
      (fun _ _ hPQ ↦ (Submodules_fg_inclusion hPQ).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodules_fg_equiv R M).rTensor N)

theorem rTensor_fgEquiv_of (P : Submodules_fg R M) (u : P.val ⊗[R] N) :
    (rTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ (Submodules_fg_inclusion hPQ).rTensor N) P) u)
      = (LinearMap.rTensor N (Submodule.subtype P.val)) u := by
  suffices (rTensor_fgEquiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R (Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ LinearMap.rTensor N (Submodules_fg_inclusion hPQ)) P)
      = LinearMap.rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [rTensor_fgEquiv, Submodules_fg_equiv, Submodules_fg_map]

theorem rTensor_fgEquiv_of' (P : Submodule R M) (hP : Submodule.FG P) (u : P ⊗[R] N) :
    (rTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ LinearMap.rTensor N (Submodules_fg_inclusion hPQ)) ⟨P, hP⟩) u)
      = (LinearMap.rTensor N (Submodule.subtype P)) u :=
  rTensor_fgEquiv_of R M N ⟨P, hP⟩ u

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
    simp [LinearMap.rTensor_comp, D.map_map]

example : DirectedSystem (ι := Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
      (fun _ _ hPQ ↦ LinearMap.rTensor N (Submodules_fg_inclusion hPQ)) := by
  apply DirectedSystem.rTensor
  exact Submodules_fg.directedSystem R M

-- Should this be generalized to DirectSystem.rTensor
-- Should this be an instance?
/-- When `P` ranges over finitely generated submodules of `P`,
  the modules of the form `P ⊗[R] N` form a directed system. -/
theorem rTensor_fg_directedSystem :
    DirectedSystem (ι := Submodules_fg R M) (fun P ↦ P.val ⊗[R] N)
      (fun _ _ hPQ ↦ LinearMap.rTensor N (Submodules_fg_inclusion hPQ)) where
  map_self P p := by
    rw [← LinearMap.id_apply (R := R) p]
    apply DFunLike.congr_fun
    ext p n
    rfl
  map_map {P Q R} hPQ hRQ p := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    rfl

noncomputable def lTensor_fgEquiv :
    Module.DirectLimit (R := R) (ι := Submodules_fg R N) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ (Submodules_fg_inclusion hPQ).lTensor M) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodules_fg_equiv R N).lTensor M)

theorem lTensor_fgEquiv_of (Q : Submodules_fg R N) (u : M ⊗[R] Q.val) :
    (lTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R N) (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ (Submodules_fg_inclusion hPQ).lTensor M) Q) u)
      = (LinearMap.lTensor M (Submodule.subtype Q.val)) u := by
  suffices (lTensor_fgEquiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R (Submodules_fg R N) (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodules_fg_inclusion hPQ)) Q)
      = LinearMap.lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [lTensor_fgEquiv, Submodules_fg_equiv, Submodules_fg_map]

theorem lTensor_fgEquiv_of' (Q : Submodule R N) (hQ : Q.FG) (u : M ⊗[R] Q) :
    (lTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R N) (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodules_fg_inclusion hPQ)) ⟨Q, hQ⟩) u)
      = (LinearMap.lTensor M (Submodule.subtype Q)) u :=
  lTensor_fgEquiv_of R M N ⟨Q, hQ⟩ u

theorem lTensor_fg_directedSystem :
    DirectedSystem (ι := Submodules_fg R N) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodules_fg_inclusion hPQ)) where
  map_self P p := by
    rw [← LinearMap.id_apply (R := R) p]
    apply DFunLike.congr_fun
    ext p n
    rfl -- needs some rw lemmas
  map_map {P Q R} hPQ hRQ p := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    rfl

variable {R M N}

theorem TensorProduct.exists_of_fg (t : M ⊗[R] N) :
    ∃ (P : Submodule R M), P.FG ∧ t ∈ LinearMap.range (LinearMap.rTensor N P.subtype) := by
  let ⟨P, u, hu⟩ := Module.DirectLimit.exists_of ((rTensor_fgEquiv R M N).symm t)
  use P.val, P.property, u
  rw [← rTensor_fgEquiv_of, hu, LinearEquiv.apply_symm_apply]

theorem TensorProduct.eq_of_fg_of_subtype_eq {P : Submodule R M} (hP : P.FG) (t t' : P ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hPQ) t' := by
  have := rTensor_fg_directedSystem R M N -- should this be an instance?
  simp only [← rTensor_fgEquiv_of R M N ⟨P, hP⟩, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property
  simpa only [sub_eq_zero, map_sub] using h

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

end CommSemiring

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

theorem Subalgebra.FG.sup {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
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
  simp only [Subalgebra.inclusion_inclusion, A'',
    ← LinearMap.rTensor_comp, ← LinearMap.comp_apply] at h
  exact h

end Algebra
