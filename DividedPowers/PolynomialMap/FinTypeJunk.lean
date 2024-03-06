import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct
import DividedPowers.PolynomialMap.Basic
import Mathlib.Algebra.Module.DirectLimitAndTensorProduct


open TensorProduct FreeAddMonoid

section Ring

variable {R : Type u} {M N : Type*}
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

variable {R : Type u} {M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

variable (R M N)
noncomputable def rTensor_fgEquiv : Module.DirectLimit (R := R) (ι := Submodules_fg R M)
    (fun P ↦ P.val ⊗[R] N)
    (fun P Q hPQ ↦ LinearMap.rTensor N (Submodules_fg_inclusion R M P Q hPQ))
      ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans (LinearEquiv.rTensor N (Submodules_fg_equiv R M))

theorem rTensor_fgEquiv_of (P : Submodules_fg R M) (u : P.val ⊗[R] N) :
    (rTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R (Submodules_fg R M) (fun P => P.val ⊗[R] N)
        (fun P Q hPQ => LinearMap.rTensor N (Submodules_fg_inclusion R M P Q hPQ)) P) u)
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



#exit

section FG

open TensorProduct FreeAddMonoid

variable {R : Type u} {M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

example (N P : Submodule R M) (h : N ≤ P) : N →ₗ[R] P := by
  exact Submodule.inclusion h

def TensorProduct.mem_map_subtype_of_FG (x : M ⊗[R] N) :
    ∃ M₀, Submodule.FG M₀ ∧ ∃ N₀, Submodule.FG N₀ ∧
    x ∈ LinearMap.range
        (TensorProduct.map (Submodule.subtype M₀) (Submodule.subtype N₀)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    use ⊥, Submodule.fg_bot, ⊥, Submodule.fg_bot
    apply zero_mem
  | tmul m n =>
    use Submodule.span R {m}, Submodule.fg_span_singleton m
    use Submodule.span R {n}, Submodule.fg_span_singleton n
    use ⟨m, Submodule.mem_span_singleton_self m⟩ ⊗ₜ ⟨n, Submodule.mem_span_singleton_self n⟩
    simp only [map_tmul, Submodule.coeSubtype]
  | add t t' ht ht' =>
    obtain ⟨M₀, hM₀, N₀, hN₀, ht⟩ := ht
    obtain ⟨M'₀, hM'₀, N'₀, hN'₀, ht'⟩ := ht'
    use M₀ ⊔ M'₀, Submodule.FG.sup hM₀ hM'₀
    use N₀ ⊔ N'₀, Submodule.FG.sup hN₀ hN'₀
    apply add_mem
    · suffices h : LinearMap.range _ ≤ LinearMap.range _ by refine h ht
      simp only [← Submodule.subtype_comp_inclusion M₀ (M₀ ⊔ M'₀) le_sup_left]
      simp only [← Submodule.subtype_comp_inclusion N₀ (N₀ ⊔ N'₀) le_sup_left]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range
    · suffices h : LinearMap.range _ ≤ LinearMap.range _ by refine h ht'
      simp only [← Submodule.subtype_comp_inclusion M'₀ (M₀ ⊔ M'₀) le_sup_right]
      simp only [← Submodule.subtype_comp_inclusion N'₀ (N₀ ⊔ N'₀) le_sup_right]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range

def TensorProduct.le_map_subtype_of_FG (P : Submodule R (M ⊗[R] N)) (hP : Submodule.FG P) :
    ∃ M₀, Submodule.FG M₀ ∧ ∃ N₀, Submodule.FG N₀ ∧
      P ≤ LinearMap.range
        (TensorProduct.map (Submodule.subtype M₀) (Submodule.subtype N₀)) := by
  apply Submodule.fg_induction _ _ _ _ _ P hP
  · intro x
    simp only [Submodule.span_singleton_le_iff_mem, LinearMap.mem_range]
    apply TensorProduct.mem_map_subtype_of_FG
  · rintro P₁ P₂ ⟨M₁, hM₁, N₁, hN₁, hP₁⟩ ⟨M₂, hM₂, N₂, hN₂, hP₂⟩
    use M₁ ⊔ M₂, Submodule.FG.sup hM₁ hM₂
    use N₁ ⊔ N₂, Submodule.FG.sup hN₁ hN₂
    simp only [sup_le_iff]
    constructor
    · apply le_trans hP₁
      simp only [← Submodule.subtype_comp_inclusion M₁ (M₁ ⊔ M₂) le_sup_left]
      simp only [← Submodule.subtype_comp_inclusion N₁ (N₁ ⊔ N₂) le_sup_left]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range
    · apply le_trans hP₂
      simp only [← Submodule.subtype_comp_inclusion M₂ (M₁ ⊔ M₂) le_sup_right]
      simp only [← Submodule.subtype_comp_inclusion N₂ (N₁ ⊔ N₂) le_sup_right]
      rw [TensorProduct.map_comp]
      apply LinearMap.range_comp_le_range

theorem Subalgebra.exists_fg_le_eq_rTensor_inclusion
    (S : Type v) [CommSemiring S] [Algebra R S] (t : S ⊗[R] M) :
    ∃ S₀, Subalgebra.FG S₀ ∧ ∃ t₀ : S₀ ⊗[R] M,
      t = LinearMap.rTensor M (Subalgebra.val S₀).toLinearMap t₀ := by
  obtain ⟨P, hP, Q, _, ⟨t, rfl⟩⟩ := TensorProduct.mem_map_subtype_of_FG t
  obtain ⟨s, hs⟩ := hP
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ Subalgebra.toSubmodule (Algebra.adjoin R (s : Set S)) := by
    simp only [← hs, Submodule.span_le, coe_toSubmodule]
    exact Algebra.subset_adjoin
  use TensorProduct.map (Submodule.inclusion this) (Submodule.subtype Q) t
  simp only [LinearMap.rTensor]
  apply congr_fun
  change _ = (TensorProduct.map _ _) ∘ (TensorProduct.map _ _)
  rw [← LinearMap.coe_comp, ← TensorProduct.map_comp]
  apply congr_arg₂ _ rfl
  apply congr_arg₂ _ rfl
  simp only [LinearMap.id_comp]

lemma TensorProduct.map_lift_eq {R : Type*} [CommSemiring R] {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (sx : FreeAddMonoid (M × N)) :
    (AddCon.mk' (addConGen (TensorProduct.Eqv R M' N'))
      (FreeAddMonoid.map (Prod.map f g) sx) : TensorProduct R M' N')
      = TensorProduct.map f g (AddCon.mk' (addConGen (TensorProduct.Eqv R M N)) sx : TensorProduct R M N) := by
  induction sx using FreeAddMonoid.recOn with
  | h0 => simp only [map_zero]
  | ih x y ih =>
    simp only [AddCon.coe_mk'] at ih
    simp only [map_add, FreeAddMonoid.map_of, Prod_map, AddCon.coe_mk', ih]
    apply congr_arg₂ _ _ rfl
    rfl

theorem FreeAddMonoid.mem_of_fg (x : FreeAddMonoid (M × N)) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
      ∃ (N' : Submodule R N), Submodule.FG N' ∧
        ∃ x' : FreeAddMonoid (M' × N'),
          x = FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype)) x' := by
  induction x using FreeAddMonoid.recOn with
  | h0 =>
    use ⊥, Submodule.fg_bot, ⊥, Submodule.fg_bot, 0
    simp
  | ih x y ih =>
    obtain ⟨M', hM', N', hN', y', rfl⟩ := ih
    rcases x with ⟨m, n⟩
    let M'₁ := Submodule.span R {m} ⊔ M'
    let N'₁ := Submodule.span R {n} ⊔ N'
    use M'₁, Submodule.FG.sup (Submodule.fg_span_singleton m) hM'
    use N'₁, Submodule.FG.sup (Submodule.fg_span_singleton n) hN'
    let m' := (⟨m, le_sup_left (b := M') (Submodule.mem_span_singleton_self m)⟩ : M'₁)
    let n' := (⟨n, le_sup_left (b := N') (Submodule.mem_span_singleton_self n)⟩ : N'₁)
    use FreeAddMonoid.of (m', n') +
      FreeAddMonoid.map
        (Prod.map
          (Submodule.inclusion (le_sup_right (a := Submodule.span R {m})))
          (Submodule.inclusion (le_sup_right (a := Submodule.span R {n})))) y'
    simp only [map_add, FreeAddMonoid.map_of, Prod_map, add_right_inj]
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp]
    simp only [Prod.map_comp_map]
    simp only [← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    exact rfl

def List.toProp {α : Type*} (p : α → Prop) (l : List α) : Prop :=
  match l with
  | nil => True
  | cons a l => p a ∧ (l.toProp p)

lemma List.toProp_nil {α : Type*} {p : α → Prop} :
    nil.toProp p = True := rfl

lemma List.toProp_cons {α : Type*} {p : α → Prop}
    {a : α} {l : List α} :
    (a :: l).toProp p ↔ (p a) ∧ (l.toProp p) := by
  simp only [List.toProp]

def FreeAddMonoid.toProp {α : Type*} (p : α → Prop) (x : FreeAddMonoid α) :
    Prop := by
  induction x using FreeAddMonoid.recOn with
  | h0 => exact True
  | ih a _ hx => exact (p a ∧ hx)

@[simp]
lemma FreeAddMonoid.toProp_zero {α : Type*} {p : α → Prop} :
    (0 : FreeAddMonoid α).toProp p = True := rfl

@[simp]
lemma FreeAddMonoid.toProp_of_add {α : Type*} {p : α → Prop}
    {a : α} {x : FreeAddMonoid α} :
    (of a + x).toProp p ↔ (p a) ∧ (x.toProp p) := by
  simp only [toProp, recOn_of_add]

@[simp]
lemma FreeAddMonoid.toProp_of {α : Type*} {p : α → Prop} {a : α}:
    (of a).toProp p ↔ p a := by
  rw [← add_zero (of a), toProp_of_add, toProp_zero, and_true]

@[simp]
lemma FreeAddMonoid.toProp_add_iff {α : Type*} (p : α → Prop)
    {x y : FreeAddMonoid α} :
    (x+y).toProp p ↔ (x.toProp p ∧ y.toProp p) := by
  constructor
  · intro h
    constructor
    · induction x using FreeAddMonoid.recOn generalizing y with
      | h0 => simp only [toProp_zero]
      | ih a x ih =>
        rw [add_assoc, toProp_of_add] at h
        rw [toProp_of_add]
        exact ⟨h.1, ih h.2⟩
    · induction x using FreeAddMonoid.recOn generalizing y with
      | h0 => simpa only [zero_add] using h
      | ih a x ih =>
        simp only [add_assoc, toProp_of_add] at h
        exact ih h.2
  · rintro ⟨hx, hy⟩
    induction x using FreeAddMonoid.recOn generalizing y with
    | h0 =>
      simp
      exact hy
    | ih a x ih =>
      rw [add_assoc, toProp_of_add]
      rw [toProp_of_add] at hx
      exact ⟨hx.1, ih hx.2 hy⟩

theorem toProp_imp {α : Type*} {p q : α → Prop} (hpq : ∀ {a}, p a → q a)
    {x : FreeAddMonoid α} (hx : x.toProp p) : x.toProp q := by
  induction x using FreeAddMonoid.recOn with
  | h0 => simp only [toProp_zero]
  | ih a x ih =>
    simp only [toProp_add_iff, toProp_of] at hx ⊢
    exact ⟨hpq hx.1, ih hx.2⟩

theorem toProp_iff {α : Type*} {p q : α → Prop} (hpq : ∀ {a}, p a ↔ q a)
    {x : FreeAddMonoid α} : x.toProp p ↔ x.toProp q :=
  ⟨toProp_imp hpq.mp, toProp_imp hpq.mpr⟩

def h (M' : Submodule R M) (N' : Submodule R N) : (M × N) → Prop :=
  fun ⟨m, n⟩ ↦ m ∈ M' ∧ n ∈ N'

theorem h_mono {M' M'' : Submodule R M} {N' N'' : Submodule R N}
    (hM : M' ≤ M'') (hN : N' ≤ N'') {x : M × N} (hx : (h M' N') x) :
    h M'' N'' x := ⟨hM hx.1, hN hx.2⟩

theorem mem_mrange_of {M' : Submodule R M} {N' : Submodule R N}
    {x : FreeAddMonoid (M × N)} (hx : x.toProp (h M' N')) :
    x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype)) := by
  induction x using FreeAddMonoid.recOn with
  | h0 => apply zero_mem
  | ih a x ih =>
    rcases a with ⟨m, n⟩
    simp only [toProp_add_iff, toProp_of, h] at hx
    refine add_mem ?_ (ih hx.2)
    simp only [Submodule.coeSubtype, AddMonoidHom.mem_mrange]
    use of (⟨⟨m, hx.1.1⟩, ⟨n, hx.1.2⟩⟩ : M' × N')
    simp only [map_of, Prod_map]

theorem toProp_h_iff_mem_mrange {M' : Submodule R M} {N' : Submodule R N}
    {x : FreeAddMonoid (M × N)} :
    x.toProp (h M' N') ↔
      x ∈ AddMonoidHom.mrange
        (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype)) := by
  constructor
  exact mem_mrange_of
  intro hx
  induction x using FreeAddMonoid.recOn with
  | h0 =>
    simp only [toProp_zero]
  | ih a x ih =>
    simp only [toProp_add_iff, toProp_of]
    simp only [Submodule.coeSubtype, AddMonoidHom.mem_mrange] at hx
    obtain ⟨y', hy'⟩ := hx
    suffices ∃ (a' : M' × N') (x' : FreeAddMonoid (M' × N')), of a' + x' = y' by
      obtain ⟨a', x', rfl⟩ := this
      simp only [map_add, map_of, Prod_map] at hy'
      rw [← toList.injective.eq_iff] at hy'
      simp only [toList_add, toList_of, List.singleton_append, List.cons.injEq,
        EmbeddingLike.apply_eq_iff_eq] at hy'
      constructor
      · rw [← hy'.1]
        exact ⟨Submodule.coe_mem a'.1, Submodule.coe_mem a'.2⟩
      · exact ih (Exists.intro x' hy'.2)
    induction y' using FreeAddMonoid.casesOn with
    | h0 =>
      rw [map_zero, ← toList.injective.eq_iff] at hy'
      simp only [toList_zero, toList_add, toList_of, List.singleton_append] at hy'
    | ih a' x' => use a', x'

theorem mem_of_exists_fg (x : FreeAddMonoid (M × N)) :
    ∃ (M' : Submodule R M), M'.FG ∧
      ∃ (N' : Submodule R N), N'.FG ∧
        x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype)) := by
  simp only [← toProp_h_iff_mem_mrange]
  induction x using FreeAddMonoid.recOn with
  | h0 =>
    use ⊥, Submodule.fg_bot
    use ⊥, Submodule.fg_bot
    simp only [toProp_zero]
  | ih a x ih =>
    rcases a with ⟨m, n⟩
    obtain ⟨M', hM', N', hN', ih⟩ := ih
    use M' ⊔ Submodule.span R {m},
      Submodule.FG.sup hM' (Submodule.fg_span_singleton m)
    use N' ⊔ Submodule.span R {n},
    Submodule.FG.sup hN' (Submodule.fg_span_singleton n)
    simp only [toProp_of_add]
    constructor
    · apply h_mono le_sup_right le_sup_right
      exact ⟨Submodule.mem_span_singleton_self m,
        Submodule.mem_span_singleton_self n⟩
    · exact toProp_imp (h_mono le_sup_left le_sup_left) ih

theorem FreeAddMonoid.of_add_neq_zero {α : Type*} (a : α) (x : FreeAddMonoid α) :
    ¬ (of a + x = 0) := by
  exact List.cons_ne_nil a x

theorem FreeAddMonoid.neq_zero_iff_exists {α : Type*} {x : FreeAddMonoid α} :
    ¬ (x = 0) ↔ ∃ a y, x = of a + y := by
  constructor
  · intro h
    obtain ⟨a, y, rfl⟩ := List.exists_cons_of_ne_nil h
    use a, y
    rfl
  · rintro ⟨a, y, rfl⟩
    apply List.cons_ne_nil

theorem FreeAddMonoid.of_add_eq_iff {α : Type*} {a b : α} {x y : FreeAddMonoid α} :
    of a + x = of b + y ↔ a = b ∧ x = y := List.cons_eq_cons

theorem FreeAddMonoid.of_add_eq_of_iff {α : Type*} {a b : α} {x : FreeAddMonoid α} :
    of a + x = of b ↔ a = b ∧ x = 0 := by
  rw [← add_zero (of b), of_add_eq_iff]

theorem FreeAddMonoid.map_eq_zero_iff {α β : Type*} {f : α → β}
    {x : FreeAddMonoid α} :
    (FreeAddMonoid.map f x = 0) ↔ (x = 0) :=
  List.map_eq_nil

theorem FreeAddMonoid.map_eq_of_add_iff_exists {α β : Type*} {f : α → β}
    {x : FreeAddMonoid α} {b : β} {y : FreeAddMonoid β} :
    (FreeAddMonoid.map f x = of b + y) ↔
      ∃ a z, f a = b ∧ FreeAddMonoid.map f z = y ∧ x = of a + z := by
  constructor
  · intro h
    induction x using FreeAddMonoid.recOn generalizing y with
    | h0 =>
      rw [map_zero] at h
      exact False.elim (of_add_neq_zero _ _ h.symm)
    | ih a z _ =>
      rw [map_add, map_of, of_add_eq_iff] at h
      exact ⟨a, z, h.1, h.2, rfl⟩
  · rintro ⟨a, z, rfl, rfl, rfl⟩
    simp only [map_add, map_of]

theorem FreeAddMonoid.map_eq_of_iff_exists {α β : Type*} {f : α → β}
    {x : FreeAddMonoid α} {b : β} :
    (FreeAddMonoid.map f x = of b) ↔
      ∃ a, f a = b ∧ x = of a := by
  rw [← add_zero (of b), map_eq_of_add_iff_exists]
  simp only [exists_and_left]
  constructor
  · rintro ⟨a, rfl, x, hx, rfl⟩
    use a, rfl
    simp only [of_add_eq_of_iff, true_and]
    simpa only [map_eq_zero_iff] using hx
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨a, rfl, 0, by simp only [map_zero, add_zero, and_self]⟩

theorem FreeAddMonoid.map_eq_add_iff_exists {α β : Type*} {f : α → β}
  {x : FreeAddMonoid α} {y₁ y₂ : FreeAddMonoid β} :
    FreeAddMonoid.map f x = y₁ + y₂ ↔
    ∃ x₁ x₂, x = x₁ + x₂ ∧ FreeAddMonoid.map f x₁ = y₁ ∧ FreeAddMonoid.map f x₂ = y₂ := by
  constructor
  · exact List.map_eq_append_split
  · rintro ⟨x₁, x₂, rfl, rfl, rfl⟩
    rw [map_add]

theorem FreeAddMonoid.map_injective_iff {α β : Type*} {f : α → β} :
    (Function.Injective (FreeAddMonoid.map f)) ↔ Function.Injective f :=
  List.map_injective_iff

theorem TensorProduct.Eqv_subtype_injective
    {M' : Submodule R M} {N' : Submodule R N} :
    Function.Injective (FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype))) := by
  rw [FreeAddMonoid.map_injective_iff]
  simp only [Prod.map_injective]
  exact ⟨Submodule.injective_subtype M', Submodule.injective_subtype N'⟩

theorem Eqv_subtype_iff {M' : Submodule R M} {N' : Submodule R N}
    {x y : FreeAddMonoid (M' × N')} :
    (Eqv R M' N') x y ↔
      (Eqv R M N)
        (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype) x)
        (FreeAddMonoid.map (Prod.map M'.subtype N'.subtype) y) := by
  constructor
  · intro h
    induction h with
    | of_zero_left n => apply Eqv.of_zero_left
    | of_zero_right m => apply Eqv.of_zero_right
    | of_add_left m₁ m₂ n => apply Eqv.of_add_left
    | of_add_right m n₁ n₂ => apply Eqv.of_add_right
    | of_smul r m n => apply Eqv.of_smul
    | add_comm x y =>
      simp only [Submodule.coeSubtype, map_add]
      apply Eqv.add_comm
  · intro h
    generalize hx' : ((FreeAddMonoid.map (Prod.map ⇑(Submodule.subtype M') ⇑(Submodule.subtype N'))) x) = x'
    generalize hy' : ((FreeAddMonoid.map (Prod.map ⇑(Submodule.subtype M') ⇑(Submodule.subtype N'))) y) = y'
    rw [hx', hy'] at h
    induction h with
    | of_zero_left n =>
      obtain ⟨⟨m', n'⟩, h, rfl⟩ := map_eq_of_iff_exists.mp hx'
      simp only [Submodule.coeSubtype, Prod_map, Prod.mk.injEq, ZeroMemClass.coe_eq_zero] at h
      rw [FreeAddMonoid.map_eq_zero_iff] at hy'
      rw [h.1, hy']
      apply Eqv.of_zero_left n'

    | of_zero_right m =>
      obtain ⟨⟨m', n'⟩, h, rfl⟩ := map_eq_of_iff_exists.mp hx'
      simp only [Submodule.coeSubtype, Prod_map, Prod.mk.injEq, ZeroMemClass.coe_eq_zero] at h
      rw [FreeAddMonoid.map_eq_zero_iff] at hy'
      rw [h.2, hy']
      apply Eqv.of_zero_right m'

    | of_add_left m₁ m₂ n =>
      rw [map_eq_of_add_iff_exists] at hx'
      obtain ⟨⟨m'₁, n'₁⟩, x', h1, hx', rfl⟩ := hx'
      simp only [map_add, map_of, Prod_map, of_add_eq_iff,
        map_eq_of_iff_exists] at hx'
      obtain ⟨⟨m'₂, n'₂⟩, h2, rfl⟩ := hx'
      rw [map_eq_of_iff_exists] at hy'
      obtain ⟨⟨m'₃, n'₃⟩, h3, rfl⟩ := hy'
      simp only [Submodule.coeSubtype, map_of, Prod_map, of_injective.eq_iff, Prod.mk.injEq] at h1 h2 h3
      have : n'₂ = n'₁ ∧ n'₃ = n'₁ := by
        simp only [← Subtype.coe_injective.eq_iff]
        simp_rw [h2.2, h1.2, h3.2, and_self]
      rw [this.1, this.2]
      have : m'₃ = m'₁ + m'₂ := by
        apply Subtype.coe_injective
        simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
        simp_rw [h3.1, h1.1, h2.1]
      rw [this]
      apply Eqv.of_add_left

    | of_add_right m n₁ n₂ =>
      rw [map_eq_of_add_iff_exists] at hx'
      obtain ⟨⟨m'₁, n'₁⟩, x', h1, hx', rfl⟩ := hx'
      simp only [map_add, map_of, Prod_map, of_add_eq_iff,
        map_eq_of_iff_exists] at hx'
      obtain ⟨⟨m'₂, n'₂⟩, h2, rfl⟩ := hx'
      rw [map_eq_of_iff_exists] at hy'
      obtain ⟨⟨m'₃, n'₃⟩, h3, rfl⟩ := hy'
      simp only [Submodule.coeSubtype, map_of, Prod_map, of_injective.eq_iff, Prod.mk.injEq] at h1 h2 h3
      have : m'₂ = m'₁ ∧ m'₃ = m'₁ := by
        simp only [← Subtype.coe_injective.eq_iff]
        simp_rw [h2.1, h1.1, h3.1, and_self]
      rw [this.1, this.2]
      have : n'₃ = n'₁ + n'₂ := by
        apply Subtype.coe_injective
        simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
        simp only [h3.2, h1.2, h2.2]
      rw [this]
      apply Eqv.of_add_right

    | of_smul r m n =>
      simp only [map_eq_of_iff_exists] at hx' hy'
      obtain ⟨⟨m'₁, n'₁⟩, hx', rfl⟩ := hx'
      obtain ⟨⟨m'₂, n'₂⟩, hy', rfl⟩ := hy'
      simp only [Submodule.coeSubtype, map_of, Prod_map, of_injective.eq_iff, Prod.mk.injEq] at hx' hy'
      have : m'₁ = r • m'₂ := by
        apply Subtype.coe_injective
        simp only [hx'.1, SetLike.val_smul, hy'.1]
      rw [this]
      have : n'₂ = r • n'₁ := by
        apply Subtype.coe_injective
        simp only [hx'.2, SetLike.val_smul, hy'.2]
      rw [this]
      apply Eqv.of_smul

    | add_comm a b =>
      rw [map_eq_add_iff_exists] at hx' hy'
      obtain ⟨a', b', rfl, ha', hb'⟩ := hx'
      obtain ⟨c', d', rfl, hc', hd'⟩ := hy'
      have : c' = b' := by
        apply TensorProduct.Eqv_subtype_injective
        rw [hc', hb']
      rw [this]
      have : d' = a' := by
        apply TensorProduct.Eqv_subtype_injective -- nom pourri
        rw [ha', hd']
      rw [this]
      apply Eqv.add_comm

theorem addConGen_Eqv_mono
    {M' M'' : Submodule R M} {N' N'' : Submodule R N}
    (hM : M' ≤ M'') (hN : N' ≤ N'')
    {x y : FreeAddMonoid (M' × N')}
    (hxy : addConGen (Eqv R M' N') x y) :
    (addConGen (Eqv R M'' N''))
        (FreeAddMonoid.map (Prod.map (Submodule.inclusion hM) (Submodule.inclusion hN)) x)
        (FreeAddMonoid.map (Prod.map (Submodule.inclusion hM) (Submodule.inclusion hN)) y) := by
  induction hxy with
  | of x y h =>
    apply AddConGen.Rel.of
    rw [Eqv_subtype_iff]
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
      Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    rw [← Eqv_subtype_iff]
    exact h
  | refl x => exact AddConGen.Rel.refl _
  | symm _ ih => exact AddConGen.Rel.symm ih
  | trans _ _ ih ih' => exact AddConGen.Rel.trans ih ih'
  | add h h' ih ih' =>
    simp only [map_add]
    exact AddConGen.Rel.add ih ih'

theorem exists_fg_of_Eqv {sx sy : FreeAddMonoid (M × N)}
    (hxy : (Eqv R M N) sx sy) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
    ∃ (N' : Submodule R N), Submodule.FG N' ∧
    ∃ (sx' : FreeAddMonoid (M' × N')) (sy' : FreeAddMonoid (M' × N')),
    FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) sx' = sx
      ∧ FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) sy' = sy
      ∧ (Eqv R M' N') sx' sy' := by
  obtain ⟨M', hM', N', hN', hx⟩ := mem_of_exists_fg (R := R) sx
  obtain ⟨M'', hM'', N'', hN'', hy⟩ := mem_of_exists_fg (R := R) sy
  use M' ⊔ M'', Submodule.FG.sup hM' hM''
  use N' ⊔ N'', Submodule.FG.sup hN' hN''
  have hx : sx.toProp (h (M' ⊔ M'') (N' ⊔ N'')) := by
    rw [← toProp_h_iff_mem_mrange] at hx
    exact toProp_imp (h_mono le_sup_left le_sup_left) hx
  have hy : sy.toProp (h (M' ⊔ M'') (N' ⊔ N'')) := by
    rw [← toProp_h_iff_mem_mrange] at hy
    exact toProp_imp (h_mono le_sup_right le_sup_right) hy
  rw [toProp_h_iff_mem_mrange] at hx hy
  obtain ⟨sx', rfl⟩ := hx
  obtain ⟨sy', rfl⟩ := hy
  use sx', sy'
  simp only [Submodule.coeSubtype, true_and]
  rw [← Eqv_subtype_iff] at hxy
  exact hxy


theorem exists_fg_of_addConGenEqv {x y : FreeAddMonoid (M × N)}
    (hxy : addConGen (Eqv R M N) x y) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
    ∃ (N' : Submodule R N), Submodule.FG N' ∧
    ∃ (x' : FreeAddMonoid (M' × N')) (y' : FreeAddMonoid (M' × N')),
    FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) x' = x
      ∧ FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) y' = y
      ∧ (addConGen (Eqv R M' N')) x' y' := by
  classical
  induction hxy with
  | of x y hxy =>
    obtain ⟨M', hM', N', hN', x', y', hx', hy', h⟩ := exists_fg_of_Eqv hxy
    use M', hM', N', hN', x', y', hx', hy'
    exact AddConGen.Rel.of x' y' h
  | refl x =>
    obtain ⟨M', hM', N', hN', x', hx'⟩ := mem_of_fg (R := R) x
    use M', hM', N', hN', x', x', hx'.symm, hx'.symm
    exact AddConGen.Rel.refl x'
  | symm _ ih =>
    obtain ⟨M', hM', N', hN', x', y', rfl, rfl, h'⟩ := ih
    use M', hM', N', hN', y', x', rfl, rfl
    exact AddConGen.Rel.symm h'
  | trans h h' ih ih' =>
    obtain ⟨M', hM', N', hN', x', y', rfl, rfl, ih⟩ := ih
    obtain ⟨M'', hM'', N'', hN'', x'', y'', hx''y', rfl, ih'⟩ := ih'
    let P := M' ⊔ M''
    use P, Submodule.FG.sup hM' hM''
    let Q := N' ⊔ N''
    use Q, Submodule.FG.sup hN' hN''
    let x := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) x' : FreeAddMonoid (P × Q))
    let y := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) y' : FreeAddMonoid (P × Q))
    let y2 := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) x'' : FreeAddMonoid (P × Q))
    let z := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) y'' : FreeAddMonoid (P × Q))
    use x, z
    constructor
    simp only [x,
      ← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
      Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    constructor
    simp only [z,
      ← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
      Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    have : y2 = y := by
      apply TensorProduct.Eqv_subtype_injective
      simp only [y, y2,
        ← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp,
        Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
      exact hx''y'
    suffices addConGen (Eqv R P Q) x y ∧ addConGen (Eqv R P Q) y z by
      apply AddConGen.Rel.trans this.1 this.2
    constructor
    · simp only [x, y]
      exact addConGen_Eqv_mono _ _ ih
    · simp only [← this, y2, z]
      exact addConGen_Eqv_mono _ _ ih'

  | add h h' ih ih' =>
    obtain ⟨M', hM', N', hN', x', y', rfl, rfl, ih⟩ := ih
    obtain ⟨M'', hM'', N'', hN'', x'', y'', rfl, rfl, ih'⟩ := ih'
    let P := M' ⊔ M''
    use P, Submodule.FG.sup hM' hM''
    let Q := N' ⊔ N''
    use Q, Submodule.FG.sup hN' hN''
    let x := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) x' : FreeAddMonoid (P × Q)) +
      (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) x'' : FreeAddMonoid (P × Q))
    let y := (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_left)
          (Submodule.inclusion le_sup_left)) y' : FreeAddMonoid (P × Q)) +
      (FreeAddMonoid.map (Prod.map
          (Submodule.inclusion le_sup_right)
          (Submodule.inclusion le_sup_right)) y'' : FreeAddMonoid (P × Q))
    use x, y
    constructor
    · simp only [x, map_add]
      simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    constructor
    · simp only [y, map_add]
      simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    · simp only [x, y]
      apply AddConGen.Rel.add
      exact addConGen_Eqv_mono _ _ ih
      exact addConGen_Eqv_mono _ _ ih'

theorem Submodule.exists_le_fg_of_map_eq
    (M₁ : Submodule R M) (hM₁ : Submodule.FG M₁)
    (N₁ : Submodule R N) (hN₁ : Submodule.FG N₁)
    (x y : M₁ ⊗[R] N₁)
    (h : TensorProduct.map (Submodule.subtype M₁) (Submodule.subtype N₁) x = TensorProduct.map (Submodule.subtype M₁) (Submodule.subtype N₁) y) :
    ∃ M₀, Submodule.FG M₀ ∧ ∃ (hM : M₁ ≤ M₀),
      ∃ N₀, Submodule.FG N₀ ∧ ∃ (hN : N₁ ≤ N₀),
        TensorProduct.map (Submodule.inclusion hM) (Submodule.inclusion hN) x =
        TensorProduct.map (Submodule.inclusion hM) (Submodule.inclusion hN) y := by
  obtain ⟨sx, rfl⟩ := AddCon.mk'_surjective x
  obtain ⟨sy, rfl⟩ := AddCon.mk'_surjective y
  rw [← TensorProduct.map_lift_eq (Submodule.subtype M₁) (Submodule.subtype N₁) sx,
    ← TensorProduct.map_lift_eq (Submodule.subtype M₁) (Submodule.subtype N₁) sy] at h
  erw [← AddCon.ker_apply, AddCon.mk'_ker] at h
  obtain ⟨M₂, hM₂, N₂, hN₂, sx', sy', hsx, hsy, h⟩ :=
    exists_fg_of_addConGenEqv h
  let M' := M₁ ⊔ M₂
  use M', FG.sup hM₁ hM₂, le_sup_left
  let N' := N₁ ⊔ N₂
  use N', FG.sup hN₁ hN₂, le_sup_left
  simp only [← TensorProduct.map_lift_eq]
  rw [← AddCon.ker_apply (f := (AddCon.mk' (addConGen (Eqv R ↥(M₁ ⊔ M₂) ↥(N₁ ⊔ N₂))))), AddCon.mk'_ker]
  have : (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_left : M₁ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_left : N₁ ≤ N₁ ⊔ N₂)))) sx =
    (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_right : M₂ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_right : N₂ ≤ N₁ ⊔ N₂)))) sx'  := by
    apply TensorProduct.Eqv_subtype_injective
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    exact hsx.symm
  rw [this]
  have : (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_left : M₁ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_left : N₁ ≤ N₁ ⊔ N₂)))) sy =
    (FreeAddMonoid.map (Prod.map ⇑(inclusion (le_sup_right : M₂ ≤ M₁ ⊔ M₂)) ⇑(inclusion (le_sup_right : N₂ ≤ N₁ ⊔ N₂)))) sy'  := by
    apply TensorProduct.Eqv_subtype_injective
    simp only [← AddMonoidHom.comp_apply, ← FreeAddMonoid.map_comp, Prod.map_comp_map, ← LinearMap.coe_comp, Submodule.subtype_comp_inclusion]
    exact hsy.symm
  rw [this]
  exact addConGen_Eqv_mono _ _ h

theorem Subalgebra.subtype_comp_inclusion
    {S : Type*} [Semiring S] [Algebra R S]{A B : Subalgebra R S} (h : A ≤ B) :
    AlgHom.comp (val B) (Subalgebra.inclusion h) = val A := by
  ext a
  rfl

example [Semiring R] [Module R M]
    (P : Submodule R M) (Q : Submodule R P) : Submodule R M :=
  Submodule.map (P.subtype) Q

theorem Subalgebra.exists_le_fg_of_map_eq
    (S : Type v) [CommSemiring S] [Algebra R S]
    (S₁ : Subalgebra R S) (hS₁ : Subalgebra.FG S₁)
    (x y : S₁ ⊗[R] M)
    (hxy : LinearMap.rTensor M (Subalgebra.val S₁).toLinearMap x =
      LinearMap.rTensor M (Subalgebra.val S₁).toLinearMap y) :
    ∃ S₀, Subalgebra.FG S₀ ∧ ∃ (hS : S₁ ≤ S₀),
        LinearMap.rTensor M (Subalgebra.inclusion hS).toLinearMap x =
        LinearMap.rTensor M (Subalgebra.inclusion hS).toLinearMap y := by
  classical
  -- the tensors x and y live on fin. gen. Px ⊗[R] Qx and Py ⊗[R] Qy
  obtain ⟨Px, hPx, Qx, hQx, ⟨x', hx'⟩⟩ := TensorProduct.mem_map_subtype_of_FG x
  obtain ⟨Py, hPy, Qy, hQy, ⟨y', hy'⟩⟩ := TensorProduct.mem_map_subtype_of_FG y
  -- they both live on the fin gen P ⊗[R] Q
  -- P is a submodule of S which is contained in S₁
  let P := Submodule.map (Subalgebra.toSubmodule S₁).subtype (Px ⊔ Py)
  have hP : Submodule.FG P := Submodule.FG.map _ (Submodule.FG.sup hPx hPy)
  let Q := Qx ⊔ Qy
  have hQ : Submodule.FG Q := Submodule.FG.sup hQx hQy
  -- the canonical injections from Px and Py to P
  let jx : Px →ₗ[R] P :=
    LinearMap.restrict (Subalgebra.toSubmodule S₁).subtype (fun p hp => by
      simp only [Submodule.coeSubtype, Submodule.map_sup]
      apply Submodule.mem_sup_left
      use p
      simp only [SetLike.mem_coe]
      exact ⟨hp, rfl⟩)
  let jy : Py →ₗ[R] P :=
    LinearMap.restrict (Subalgebra.toSubmodule S₁).subtype (fun p hp => by
      simp only [Submodule.coeSubtype, Submodule.map_sup]
      apply Submodule.mem_sup_right
      use p
      simp only [SetLike.mem_coe]
      exact ⟨hp, rfl⟩)
  -- we map x' and y' to P ⊗[R] Q, getting xPQ and yPQ
  set xPQ := TensorProduct.map jx (Submodule.inclusion (le_sup_left : Qx ≤ Q)) x' with hxPQ
  set yPQ := TensorProduct.map jy (Submodule.inclusion (le_sup_right : Qy ≤ Q)) y' with hyPQ
  -- xPQ and yPQ are equal in S ⊗[R] M
  have : TensorProduct.map P.subtype Q.subtype xPQ
    = TensorProduct.map P.subtype Q.subtype yPQ := by
    rw [hxPQ, hyPQ]
    have jkx : P.subtype ∘ₗ jx = (val S₁).toLinearMap ∘ₗ Px.subtype := by
      ext p
      rfl
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, jkx]
    have jky : P.subtype ∘ₗ jy = (val S₁).toLinearMap ∘ₗ Py.subtype := by
      ext p
      rfl
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, jky]
    simp only [Submodule.subtype_comp_inclusion]
    rw [← LinearMap.id_comp (Submodule.subtype Qx)]
    rw [← LinearMap.id_comp (Submodule.subtype Qy)]
    simp only [TensorProduct.map_comp, LinearMap.comp_apply]
    simp only [LinearMap.rTensor] at hxy
    rw [hx', hy']
    exact hxy
  -- xPQ and yPQ are equal in a finitely generated P' ⊗[R] Q'
  obtain ⟨P', hP', P_le_P', Q', _, Q_le_Q', h⟩ :=
    Submodule.exists_le_fg_of_map_eq P hP Q hQ xPQ yPQ this
  obtain ⟨s, hs⟩ := hP'
  obtain ⟨t, ht⟩ := hS₁
  -- We define S₀, a fin generated algebra that contains S₁ and P'
  let S₀ := Algebra.adjoin R ((s ∪ t : Finset S) : Set S)
  use S₀, Subalgebra.fg_adjoin_finset _
  have hS₁_le_S₀ : S₁ ≤ S₀ := by
    simp only [S₀, ← ht]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use hS₁_le_S₀
  have hS₁_le_S₀' : (Subalgebra.toSubmodule S₁ : Submodule R S) ≤ Subalgebra.toSubmodule S₀ := hS₁_le_S₀
  have hk : AlgHom.toLinearMap (Subalgebra.inclusion hS₁_le_S₀) = Submodule.inclusion hS₁_le_S₀' := by
    ext s
    rfl
  -- We factor the tensor products as S₁ → S₀ → M
  simp only [LinearMap.rTensor]
  rw [← hx', ← hy', hk]
  simp only [← LinearMap.comp_apply, ← LinearMap.coe_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
  -- we factor the map Px → S₁ → S₀ via Px → P → P' → S₀
  -- Px → S₁ is Px.subtype
  -- Px → P is jx
  -- P → P' is Submodule.inclusion (P_le_P')
  -- Define P' → S₀
  have P'_le_S₀ : P' ≤ Subalgebra.toSubmodule S₀ := by
    simp only [← hs, Submodule.span_le, Finset.coe_union, coe_toSubmodule]
    exact le_trans (Set.subset_union_left _ _) (Algebra.subset_adjoin)
  have hkx : (Submodule.inclusion hS₁_le_S₀') ∘ₗ Px.subtype
    = Submodule.inclusion (R := R) (P'_le_S₀)  ∘ₗ (Submodule.inclusion (R := R) P_le_P') ∘ₗ jx := by
    ext p
    rfl
  have hky : (Submodule.inclusion hS₁_le_S₀') ∘ₗ Py.subtype
    = Submodule.inclusion (R := R) (P'_le_S₀)  ∘ₗ (Submodule.inclusion (R := R) P_le_P') ∘ₗ jy := by
    ext p
    rfl
  rw [hkx, hky]
  rw [← LinearMap.id_comp (Submodule.subtype Qx),
    ← LinearMap.id_comp (Submodule.subtype Qy)]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  apply congr_arg
  -- Now we have x' and y' pushed in P' ⊗[R] M
  -- We know that x' and y' pushed to P ⊗[R] Q  give xPQ and yPQ
  rw [← Submodule.subtype_comp_inclusion _ _ (le_sup_left : Qx ≤ Q)]
  rw [← Submodule.subtype_comp_inclusion _ _ (le_sup_right : Qy ≤ Q)]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  rw [TensorProduct.map_comp, LinearMap.comp_apply]
  rw [← hxPQ, ← hyPQ]
  -- Now we have xPQ and yPQ pushed in P' ⊗[R] M
  -- They coincide in P' ⊗[R] Q'
  rw [← Submodule.subtype_comp_inclusion _ _ Q_le_Q']
  rw [← LinearMap.id_comp (Submodule.inclusion P_le_P')]
  rw [TensorProduct.map_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h]
  done

end FG

section Lift

namespace AlgHom

variable {R : Type u} [CommSemiring R]
    {S : Type v} [Semiring S] [Algebra R S]
    {T : Type w} [Semiring T] [Algebra R T]

theorem range_top_iff_surjective {f : S →ₐ[R] T} :
    f.range = (⊤ : Subalgebra R T) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans (by rw [coe_range, Algebra.coe_top]) Set.range_iff_surjective

theorem range_top_of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.range = ⊤ :=
  range_top_iff_surjective.2 hf

lemma LiftDown_of_FiniteType  {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (B : Subalgebra R S) [hFT : Algebra.FiniteType R B] :
    ∃ (A : Type u), ∃ (hCR : CommRing A), ∃ (hAlg : Algebra R A),
    ∃ (_ : A ≃ₐ[R] B), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    (Ideal.quotientKerEquivRange f).trans (range_top_of_surjective f hf ▸ Subalgebra.topEquiv),
    trivial⟩

end AlgHom

end Lift

section PolynomialMap

  -- (f : PolynomialMap R M N)

open TensorProduct

variable {R : Type u} [CommSemiring R]
  {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (f : Π (S : Type u) (_ : CommSemiring S) (_ : Algebra R S) (_ : S ⊗[R] M),
    S ⊗[R] N)
  (S : Type*) [CommSemiring S] [Algebra R S]

theorem hasLift (x : S ⊗[R] M) :
    ∃ (S' : Type u) (_: CommSemiring S') (_ : Algebra R S') (j : S' →ₐ[R] S) (x' : S' ⊗[R] M),
    LinearMap.rTensor M j.toLinearMap x' = x := by
  sorry

theorem isLiftUnique
    (S' : Type u) [CommSemiring S'] [Algebra R S'] (j' : S' →ₐ[R] S)
    (x' : S' ⊗[R] M)
    (S'' : Type u) [CommSemiring S''] [Algebra R S''] (j'' : S'' →ₐ[R] S)
    (x'' : S'' ⊗[R] M)
    (h : LinearMap.rTensor M j'.toLinearMap x' = LinearMap.rTensor M j''.toLinearMap x'') :
    ∃ (T : Type u) (_ : CommSemiring T) (_ : Algebra R T) (j : T →ₐ[R] S)
      (k' : S' →ₐ[R] T) (k'' : S'' →ₐ[R] T),
      j.comp k' = j' ∧ j.comp k'' =j'' ∧
      LinearMap.rTensor M k'.toLinearMap x' = LinearMap.rTensor M k''.toLinearMap x'' := by
  sorry

noncomputable def liftAux (x : S⊗[R] M)
  (S' : Type u) (hC : CommSemiring S') (hA : Algebra R S') (j : S' →ₐ[R] S) (x' : S' ⊗[R] M) (_ : LinearMap.rTensor M j.toLinearMap x' = x) : S ⊗[R] N :=
  LinearMap.rTensor N j.toLinearMap (f S' hC hA x')

noncomputable example (f : PolynomialMap R M N) (S : Type*) [CommSemiring S] [Algebra R S] :
  { F : S ⊗[R] M → S ⊗[R] N //
    ∀ (S' : Type u) (hCS' : CommSemiring S') (hAS' : Algebra R S')
      (x' : S' ⊗[R] M), F S' hCS' hAS' x' = f.toFun S' x' } := by
  sorry
  -- intro x
  choose S' hC hA j x' hx' using hasLift S x
  exact LinearMap.rTensor N j.toLinearMap (f S' hC hA x')

noncomputable def lift (x : S ⊗[R] M) : S ⊗[R] N := by
    let S' := (hasLift S x).choose
    let hCS' : CommSemiring S' := (hasLift S x).choose_spec.choose
    let hAS' : Algebra R S' := (hasLift S x).choose_spec.choose_spec.choose
    let j : S' →ₐ[R] S := (hasLift S x).choose_spec.choose_spec.choose_spec.choose
    let x' : S' ⊗[R] M  := (hasLift S x).choose_spec.choose_spec.choose_spec.choose_spec.choose
    let hx' := (hasLift S x).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    exact liftAux f S x S' hCS' hAS' j x' hx'





noncomputable example (S : Type*) [CommSemiring S] [Algebra R S]
  (S' : Type u) [CommSemiring S'] [Algebra R S']
  (j : S' →ₐ[R] S) (y : S' ⊗[R] M) : S ⊗[R] N :=
  j.toLinearMap.rTensor N (f.toFun S' y)

def liftFG_unique (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] M)
    (S' : Type u) [CommSemiring S'] [Algebra R S'] (j : S' →ₐ[R] S)
    (y' : S' ⊗[R] M)
    (h : LinearMap.rTensor M j.toLinearMap y = LinearMap.rTensor M j.toLinearMap y') :
    j.toLinearMap.rTensor N (f.toFun S' y) = j.toLinearMap.rTensor N (f.toFun S' y') := by
  obtain ⟨S₀, hS₀, h⟩ := Subalgebra.exists_le_fg_of_map_eq S S'
  sorry

end PolynomialMap


#exit
theorem TensorProduct.map_comp_Quotient
  {M' : Type*} [AddCommMonoid M'] [Module R M']
  {N' : Type*} [AddCommMonoid N'] [Module R N']
  (f : M →ₗ[R] M') (g : N →ₗ[R] N') (l : FreeAddMonoid (M × N)) :
  (TensorProduct.map f g) ⟦l⟧ = ⟦FreeAddMonoid.map (fun ⟨m, n⟩ ↦ ⟨f m, g n⟩) l⟧ := by
  change (TensorProduct.map f g) (AddCon.toQuotient l) =
    AddCon.toQuotient (FreeAddMonoid.map (fun ⟨m,n⟩ ↦ ⟨f m, g n⟩) l)
  induction l using FreeAddMonoid.recOn with
  | h0 => simp only [map_zero, AddCon.coe_zero]; rfl
  | ih x y hy =>
    simp [AddCon.coe_add, LinearMap.map_add, map_add, FreeAddMonoid.map_of]
    apply congr_arg₂ _ _ hy
    change TensorProduct.map f g (x.1 ⊗ₜ[R] x.2) = _
    rw [TensorProduct.map_tmul]
    rfl

theorem LinearMap.rTensor_comp_AddCon
    {M' : Type*} [AddCommMonoid M'] [Module R M']
    (h : M →ₗ[R] M') (l : FreeAddMonoid (M × N)) :
    (LinearMap.rTensor N h) ⟦l⟧ = ⟦FreeAddMonoid.map (fun ⟨m, n⟩ ↦ ⟨h m, n⟩) l⟧ :=
  TensorProduct.map_comp_Quotient h _ l

def mem_fg' (P : Submodule R (M ⊗[R] N)) (hP : Submodule.FG P) :
    ∃ (M₀ : Submodule R M) (hM₀ : Submodule.FG M₀) (N₀ : Submodule R N) (hN₀ : Submodule.FG N₀),
      P ≤ LinearMap.range
        (TensorProduct.map (Submodule.subtype M₀) (Submodule.subtype N₀)) := by
  sorry

def mem_fg
    (S : Type v) [CommSemiring S] [Algebra R S]
    (t : S ⊗[R] M) :
     ∃ (S₀ : Subalgebra R S)
        (hFG : Subalgebra.FG S₀),
            t ∈ LinearMap.range (LinearMap.rTensor M (Subalgebra.val S₀).toLinearMap) := by
  sorry

def FAM_liftMap (f : PolynomialMap R M N)
    (S : Type v) [CommSemiring S] [Algebra R S]
    (t : S ⊗[R] M) :
     ∃ (B : Type u)
      (hCommSemiring : CommSemiring B)
        (hAlgRB : Algebra R B)
          (hBS : B →ₐ[R] S),
            t ∈ LinearMap.range (LinearMap.rTensor M hBS.toLinearMap) := by
  classical
  let ⟨l, hl⟩ := Quotient.exists.mp (Exists.intro t rfl)
  let A : Subalgebra R S := Algebra.adjoin R ((l.toList.map (fun (s, _) ↦ s)).toFinset : Set S)
  have : Algebra.FiniteType R A :=
    (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset _)
  let ⟨B, hCommSemiring, hAlgRB, hBA, _⟩ := UnivDown A
  have hl_mem : ∀ sm ∈ FreeAddMonoid.toList l, sm.1 ∈ A := fun sm ↦ by
    simp only [List.coe_toFinset, List.mem_map, Prod.exists, exists_and_right, exists_eq_right]
    exact fun hsm ↦ Algebra.subset_adjoin ⟨sm.2, hsm⟩
  let h₁ : S → B := fun s ↦ if hs : s ∈ A then hBA.symm ⟨s, hs⟩ else 0
  set l' : FreeAddMonoid (B × M) := FreeAddMonoid.map (fun ⟨s, m⟩ ↦ ⟨h₁ s, m⟩) l
    with hl'
  -- let t' : B ⊗[R] M := AddCon.toQuotient l'
  use B, hCommSemiring, hAlgRB
  let h := (Subalgebra.val A).comp hBA.toAlgHom
  use h
  use AddCon.toQuotient l'
  have : t = AddCon.toQuotient l := by rw [hl]; rfl
  rw [this]
  convert LinearMap.rTensor_comp_AddCon (R := R) h.toLinearMap l'
  rw [hl']
  change l = (AddMonoidHom.comp (FreeAddMonoid.map _) (FreeAddMonoid.map _)) l
  rw [← FreeAddMonoid.map_comp]
  apply symm
  -- hypothèse trop forte, parce que h₁ n'est pas l'inverse de h partout,
  -- juste sur l'algèbre engendrée par les valeurs de l…
  convert DFunLike.congr_fun FreeAddMonoid.map_id l
  sorry

def FAM_liftMap' (f : PolynomialMap R M N) (S : Type v) [CommSemiring S] [Algebra R S] :
    FreeAddMonoid (S × M) → S ⊗[R] N := by
  classical
  intro l
  let A : Subalgebra R S := Algebra.adjoin R ((l.toList.map (fun (s, _) ↦ s)).toFinset : Set S)
  have : Algebra.FiniteType R A :=
    (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset _)
  set B := (UnivDown A).choose
  let hCommSemiringB : CommSemiring B := (UnivDown A).choose_spec.choose
  let hAlgebraRB : Algebra R B := (UnivDown A).choose_spec.choose_spec.choose
  let hBA : B ≃ₐ[R] A := (UnivDown A).choose_spec.choose_spec.choose_spec.choose
  have hl_mem : ∀ sm ∈ FreeAddMonoid.toList l, sm.1 ∈ A := fun sm ↦ by
    simp only [List.coe_toFinset, List.mem_map, Prod.exists, exists_and_right, exists_eq_right]
    exact fun hsm ↦ Algebra.subset_adjoin ⟨sm.2, hsm⟩
  let l' : FreeAddMonoid (B × M) := (List.attach (FreeAddMonoid.toList l)).map
    (fun ⟨x, hx⟩ ↦ ⟨hBA.symm (⟨x.1, hl_mem x hx⟩ : A), x.2⟩)
  let t' : B ⊗[R] M := AddCon.toQuotient l'
  let u' := f.toFun B t'
  have hBS : B →ₐ[R] S := (Subalgebra.val A).comp hBA.toAlgHom
  exact (LinearMap.rTensor N hBS.toLinearMap) u'





example (f : PolynomialMap R M N) (S : Type v) [CommSemiring S] [Algebra R S] :
    S ⊗[R] M → S ⊗[R] N := by
  apply Quotient.lift


#exit


def Subalgebra.subtype {R S : Type} [CommSemiring R] [Semiring S] [Algebra R S]
  (A : Subalgebra R S) : A →ₐ[R] S := val A

namespace AlgHom

section range

variable {R : Type u} [CommSemiring R]
    {S : Type v} [Semiring S] [Algebra R S]
    {T : Type w} [Semiring T] [Algebra R T]

theorem range_top_iff_surjective {f : S →ₐ[R] T} :
    f.range = (⊤ : Subalgebra R T) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans (by rw [coe_range, Algebra.coe_top]) Set.range_iff_surjective

theorem range_top_of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.range = ⊤ :=
  range_top_iff_surjective.2 hf

example {S T : Type*} [Ring S] [Ring T] (f : S →+* T) (hf : Function.Surjective f) :
    RingHom.range f ≃+* T :=
  (RingHom.range_top_of_surjective f hf) ▸ Subring.topEquiv

example (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.range ≃ₐ[R] T :=
  (range_top_of_surjective f hf) ▸ Subalgebra.topEquiv

def rangeS (f : S →ₐ[R] T) : Subalgebra R T :=
{ f.toRingHom.rangeS with
  algebraMap_mem' := fun r => ⟨algebraMap R S r, f.commutes r⟩ }

theorem mem_rangeS {f : S →ₐ[R] T} {y : T} :
    y ∈ f.rangeS ↔ ∃ x, f x = y :=
  { mp := fun a => a, mpr := fun a => a }

def rangeSRestrict (f : S →ₐ[R] T) : S →ₐ[R] f.rangeS :=
  AlgHom.codRestrict f f.rangeS (fun x ↦ ⟨x, rfl⟩)

theorem ker_rangeSRestrict (f : S →ₐ[R] T) :
    RingHom.ker f.rangeRestrict = RingHom.ker f :=
  RingHom.ker_rangeSRestrict f.toRingHom

theorem rangeSRestrict_surjective (f : S →ₐ[R] T):
    Function.Surjective (f.rangeSRestrict) :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := hy
  ⟨x, SetCoe.ext hx⟩

theorem rangeS_top_iff_surjective {f : S →ₐ[R] T} :
    f.range = (⊤ : Subalgebra R T) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, Algebra.coe_top]) Set.range_iff_surjective

theorem rangeS_top_of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.rangeS = ⊤ :=
  rangeS_top_iff_surjective.2 hf

end range

section FIT

variable {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [Semiring T] [Algebra R T]

/-- The **first isomorphism theorem** for commutative algebras, surjective case. -/
noncomputable example {f : S →ₐ[R] T} (hf : Function.Surjective f) :
    (S ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] T  :=
  Ideal.quotientKerAlgEquivOfSurjective hf

/-- The **first isomorphism theorem** for commutative algebras (`AlgHom.range` version). -/
noncomputable example (f : S →ₐ[R] T) : (S ⧸ RingHom.ker f) ≃ₐ[R] f.range :=
  Ideal.quotientKerEquivRange f

/-
/-- The **first isomorphism theorem** for commutative algebras (`AlgHom.rangeS` version). -/
noncomputable def quotientKerEquivRangeS (f : S →ₐ[R] T) :
    (S ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] f.rangeS :=
  (Ideal.quotientEquivAlgOfEq R f.ker_rangeSRestrict.symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective f.rangeSRestrict_surjective
-/

end FIT

variable {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [Semiring T] [Algebra R T]


example  {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [hFT : Algebra.FiniteType R S] :
    ∃ (A : Type u), ∃ (hCR : CommRing A), ∃ (hAlg : Algebra R A),
    ∃ (_ : A ≃ₐ[R] S), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  have : f.range ≃ₐ[R] S :=
    (range_top_of_surjective f hf) ▸ Subalgebra.topEquiv
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    (Ideal.quotientKerEquivRange f).trans this, trivial⟩

/-
example {R : Type u} [CommRing R]
  (S : Type v) [CommSemiring S] [Algebra R S] [hFT : Algebra.FiniteType R S] :
  ∃ (A : Type u), ∃ (_ : CommRing A), ∃ (_ : Algebra R A),
  ∃ (_ : A ≃ₐ[R] S), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  have : f.rangeS ≃ₐ[R] S :=
    (rangeS_top_of_surjective f hf) ▸ Subalgebra.topEquiv
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    (Ideal.quotientKerEquivRangeS f).trans this, trivial⟩
-/

example  {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (B : Subalgebra R S) [hFT : Algebra.FiniteType R B] :
    ∃ (A : Type u), ∃ (hCR : CommRing A), ∃ (hAlg : Algebra R A),
    ∃ (_ : A ≃ₐ[R] B), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    (Ideal.quotientKerEquivRange f).trans (range_top_of_surjective f hf ▸ Subalgebra.topEquiv),
    trivial⟩

end AlgHom


namespace a
variable {α β γ : Type*} (c : β → Sort) {p : β → α}

variable (f : Π b, c b → γ)
  (has_lift : ∀ a : α, ∃ b : β, c b ∧ p b = a)
  (lift_indep : ∀ b b' (hb : c b) (hb' : c b') (_ :  p b = p b'), f b hb = f b' hb')

#check Sigma c

end a

namespace b

variable {α β γ : Type*} {c : β → Type*} {p : β → α}
#check c
#check Π b, c b
#check Σ b, c b
#check fun (b : β) (hb : c b) ↦ (⟨b, hb⟩ : Σ b, c b)


/- def r {α β : Type*} (c : β → Prop) (p : β → α) :
    { b // c b} → { b // c b} → Prop :=
  fun ⟨b, hb⟩ ⟨b', hb'⟩ ↦ p b = p b'
-/

#check c
#check Σ b, c b
#check Sigma c
#check Sigma


def r : (Σ b, c b) → (Σ b, c b) → Prop :=
  fun ⟨b, _⟩ ⟨b', _⟩ ↦ p b = p b'

end b

namespace c

variable {α β γ : Type*} (c : β → Type*) (p : β → α)
  (f : Π b, c b → γ)
  (has_lift : ∀ a : α, ∃ (b : β) (_ : c b), p b = a)
  (lift_indep : ∀ {b b'} {hb : c b} {hb' : c b'} (_ :  p b = p b'), f b hb = f b' hb')

noncomputable def G : { g : α → γ // ∀ (b : β) (hb : c b), g (p b) = f b hb } := by
  choose lift cond_lift proj_lift using has_lift
  use fun a ↦ f (lift a) (cond_lift a), fun b hb ↦ lift_indep (proj_lift (p b))

def r : (Σ b, c b) → (Σ b, c b) → Prop := fun ⟨b, hb⟩ ⟨b', hb'⟩ ↦ p b = p b'

def gQ : Quot (r c p) → γ := by
  apply Quot.lift (fun ⟨b, hb⟩ ↦ f b hb : (Σ b, c b) → γ)
  rintro ⟨b, hb⟩ ⟨b', hb'⟩ H
  exact lift_indep H

def e : Quot (r c p) ≃ α := {
  toFun := Quot.lift (fun ⟨b, hb⟩ ↦ p b : (Σ b, c b) → α) (fun ⟨b, hb⟩ ⟨b', hb'⟩ H ↦ H)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry }

def g : α → γ := (gQ c p f lift_indep) ∘ (e c p).symm

theorem g_comp_p (b : β) (hb : c b) : (g c p f lift_indep) (p b) = f b hb := by

  suffices (g c p f lift_indep) ∘ (fun ⟨b, hb⟩ ↦ p b) =
    fun (⟨b, hb⟩ : Σ b, c b) ↦ f b hb by
    exact congr_fun this ⟨b, hb⟩
  simp only [g, gQ]
  sorry




end c

namespace d

#check Quot.lift (fun ⟨b, hb⟩ ↦ f b hb : (Σ b, c b) → γ)
example : Quot (r c p) → γ := by
  sorry

def g (a : α) : γ := by sorry

noncomputable def g (a : α) : γ := by
  let b := (has_lift a).choose
  let ⟨hb, _⟩ := (has_lift a).choose_spec
  exact f b hb

example (b : β) (hb : c b) : f b hb = g f has_lift (p b) := by
  let a := p b
  let b₁ := (has_lift a).choose
  let ⟨hb₁, hpb₁⟩ := (has_lift a).choose_spec
  have : g f has_lift (p b) = f b₁ hb₁ := by
    simp only [b₁, hb₁, hpb₁, g]

  rw [this]
  apply lift_indep b b₁ hb hb₁
  exact hpb₁.symm

end d

namespace e
theorem FreeAddMonoid.of_mem_of_add_left_mem (x : (M × N)) (y : FreeAddMonoid (M × N))
    (M' : Submodule R M) (N' : Submodule R N)
    (h : y + of x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype)))) :
    x ∈ Set.range (Prod.map (M'.subtype) (N'.subtype)) := by
  obtain ⟨z', hz'⟩ := h
  induction z' using FreeAddMonoid.recOn with
  | h0 =>
    simp only [Submodule.coeSubtype, map_zero] at hz'
    rw [← toList.injective.eq_iff] at hz'
    simp only [toList_zero, toList_add, toList_of, List.nil_eq_append, and_false] at hz'
  | ih a z ih =>
    simp only [Submodule.coeSubtype, Set.range_prod_map, Subtype.range_coe_subtype, Set.mem_prod,
      Set.mem_setOf_eq] at ih
    simp only [Submodule.coeSubtype, map_add, map_of, Prod_map] at hz'
    rw [← FreeAddMonoid.toList.injective.eq_iff] at hz'
    simp only [toList_add, toList_of, List.cons_append, List.nil_append] at hz'
    exact Exists.intro a hz'.1


theorem FreeAddMonoid.of_mem_of_add_right_mem (x : (M × N)) (y : FreeAddMonoid (M × N))
    (M' : Submodule R M) (N' : Submodule R N)
    (h : of x + y ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype)))) :
    x ∈ Set.range (Prod.map (M'.subtype) (N'.subtype)) := by
  obtain ⟨z', hz'⟩ := h
  induction z' using FreeAddMonoid.recOn with
  | h0 =>
    simp only [Submodule.coeSubtype, map_zero] at hz'
    simpa only [toList_of, List.singleton_append] using FreeAddMonoid.toList.injective hz'
  | ih a z ih =>
    simp only [Submodule.coeSubtype, Set.range_prod_map, Subtype.range_coe_subtype, Set.mem_prod,
      Set.mem_setOf_eq] at ih
    simp only [Submodule.coeSubtype, map_add, map_of, Prod_map] at hz'
    rw [← FreeAddMonoid.toList.injective.eq_iff] at hz'
    simp only [toList_add, toList_of, List.singleton_append,
      List.cons.injEq, EmbeddingLike.apply_eq_iff_eq] at hz'
    exact Exists.intro a hz'.1

theorem FreeAddMonoid.mem_of_add_right_mem (x y : FreeAddMonoid (M × N))
    (M' : Submodule R M) (N' : Submodule R N)
    (h : x + y ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype)))) :
    x ∈ AddMonoidHom.mrange (FreeAddMonoid.map (Prod.map (M'.subtype) (N'.subtype))) := by
  obtain ⟨z', hz'⟩ := h
  induction y using FreeAddMonoid.recOn generalizing x with
  | h0 => sorry
  | ih a z ih =>
    rw [← add_assoc] at hz'
    specialize ih (x + of a) hz'
    sorry

theorem exists_fg_of_rel' {sx sy : FreeAddMonoid (M × N)}
    (hxy : (Eqv' R M N) sx sy) :
    ∃ (M' : Submodule R M), Submodule.FG M' ∧
    ∃ (N' : Submodule R N), Submodule.FG N' ∧
    ∃ (sx' : FreeAddMonoid (M' × N')) (sy' : FreeAddMonoid (M' × N')),
    FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) sx' = sx
      ∧ FreeAddMonoid.map (Prod.map (Submodule.subtype M') (Submodule.subtype N')) sy' = sy
      ∧ (addConGen (Eqv R M' N')) sx' sy' := by
  sorry

variable (R M N)
/-- The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive Eqv' : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv' (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv' (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv' (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv' (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv' (.of (r • m, n)) (.of (m, r • n))


variable {R M N}

example (P : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop)
    (hP_Eqv : ∀ {x y : FreeAddMonoid (M × N)} (_ : (Eqv' R M N) x y), P x y)
    (hP_add : ∀ {x y : FreeAddMonoid (M × N)}, P x y ↔ P y x)
    {x y : FreeAddMonoid (M × N)} (hxy : (Eqv R M N) x y) : P x y := by
  induction hxy with
  | of_zero_left n => exact hP_Eqv (Eqv'.of_zero_left n)
  | of_zero_right m => exact hP_Eqv (Eqv'.of_zero_right m)
  | of_add_left m₁ m₂ n => exact hP_Eqv (Eqv'.of_add_left m₁ m₂ n)
  | of_add_right m n₁ n₂ => exact hP_Eqv (Eqv'.of_add_right m n₁ n₂)
  | of_smul r m n => exact hP_Eqv (Eqv'.of_smul r m n)
  | add_comm x y => sorry

end e
