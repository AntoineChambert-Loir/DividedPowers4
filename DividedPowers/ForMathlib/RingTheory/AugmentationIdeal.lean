/- copyright ACL @ MIdFF 2024 -/

import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Augmentation ideals

* `Ideal.IsAugmentation` :  An ideal `I` of an `A`-algebra `S`
is an augmentation ideal if it is a complement of `⊥ : Subalgebra A S`.

* `Ideal.isAugmentation_baseChange`: if `R` is a commring and an `A`-algebra,
then the ideal `R ⊗[A] I` of `R ⊗[A] S` is an augmentation ideal.

## Remark

* There is a weaker version that holds for general commutative rings
and would just assert that the quotient map `R →+* R ⧸ I` has a section
which is a ring homomorphism (possibly with the variant “with data” that
keeps track of the choice of one such section).

## TODO

Golf, dispatch

 -/

section DistribLattice
variable    {α : Type*} [DistribLattice α] [BoundedOrder α] {a b c : α}

theorem DistribLattice.isCompl_assoc_of_disjoint
  (hab : Disjoint a b) (h : IsCompl (a ⊔ b) c) : IsCompl a (b ⊔ c) := by
  rcases h with ⟨hd, hc⟩
  apply IsCompl.mk
  · intro x hx hx'
    refine hd (le_trans hx le_sup_left) ?_
    rw [← left_eq_inf, inf_sup_left] at hx'
    rw [hx']
    simp only [sup_le_iff, inf_le_right, and_true]
    convert bot_le
    rw [eq_bot_iff]
    apply hab (inf_le_of_left_le hx) inf_le_right
  · simp only [Codisjoint, sup_le_iff, and_imp]
    intro x hxa hxb hxc
    exact hc (by simp only [sup_le_iff, hxa, hxb, and_self]) hxc

end DistribLattice

variable (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A)

section restrictScalars

variable
    (A : Type*) [CommSemiring A]
    {R : Type*} [Semiring R] [Algebra A R]
    {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower A R M]
    (M₁ M₂ : Submodule R M)

theorem Submodule.sup_restrictScalars :
   (M₁ ⊔ M₂).restrictScalars A = M₁.restrictScalars A ⊔ (M₂.restrictScalars A) := by
  apply Submodule.toAddSubmonoid_injective
  simp only [Submodule.toAddSubmonoid_restrictScalars, Submodule.sup_toAddSubmonoid]

theorem Submodule.codisjoint_restrictScalars_iff :
    Codisjoint (M₁.restrictScalars A) (M₂.restrictScalars A) ↔
      Codisjoint M₁ M₂ := by
  simp only [codisjoint_iff, ← Submodule.sup_restrictScalars, Submodule.restrictScalars_eq_top_iff]

theorem Submodule.disjoint_restrictScalars_iff :
    Disjoint (M₁.restrictScalars A) (M₂.restrictScalars A) ↔
      Disjoint M₁ M₂ := by
  simp only [Submodule.disjoint_def, Submodule.restrictScalars_mem]

theorem Submodule.isCompl_restrictScalars_iff  :
    IsCompl (M₁.restrictScalars A) (M₂.restrictScalars A) ↔ IsCompl M₁ M₂ := by
  simp only [isCompl_iff, Submodule.disjoint_restrictScalars_iff, Submodule.codisjoint_restrictScalars_iff]

end restrictScalars

section bot

variable {A : Type*} [CommSemiring A]
    {R : Type*} [CommSemiring R] [Algebra A R]
    (S : Subalgebra A R) (r : R)

theorem Subalgebra.mem_bot_iff :
    r ∈ (⊥ : Subalgebra S R) ↔ r ∈ S := by
  simp only [Algebra.mem_bot, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hr
    exact ⟨r, hr, rfl⟩

theorem Subalgebra.restrictScalars_toSubmodule_bot :
    Submodule.restrictScalars A (Subalgebra.toSubmodule (⊥ : Subalgebra S R))
      = Subalgebra.toSubmodule S := by
  rw [← Subalgebra.restrictScalars_toSubmodule A]
  congr
  ext x
  simp only [Subalgebra.mem_restrictScalars, Subalgebra.mem_bot_iff]

theorem Subalgebra.codisjoint_bot_iff (I : Ideal R) :
    Codisjoint (Subalgebra.toSubmodule (⊥ : Subalgebra S R)) (I.restrictScalars S) ↔
    Codisjoint (Subalgebra.toSubmodule S) (I.restrictScalars A) := by
  rw [← Submodule.codisjoint_restrictScalars_iff A, Subalgebra.restrictScalars_toSubmodule_bot]
  exact Iff.rfl

theorem Subalgebra.disjoint_bot_iff (I : Ideal R) :
    Disjoint (Subalgebra.toSubmodule (⊥ : Subalgebra S R)) (I.restrictScalars S) ↔
    Disjoint (Subalgebra.toSubmodule S) (I.restrictScalars A) := by
  rw [← Submodule.disjoint_restrictScalars_iff A,
    Subalgebra.restrictScalars_toSubmodule_bot]
  exact Iff.rfl

end bot

open AlgHom RingHom Submodule Ideal.Quotient

open TensorProduct LinearMap

theorem LinearMap.ker_lTensor_of_linearProjOfIsCompl
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂)
    (Q : Type*) [AddCommGroup Q] [Module A Q] :
    ker (lTensor Q (linearProjOfIsCompl _ _ hM)) = range (lTensor Q M₂.subtype) := by
  rw [← exact_iff]
  apply lTensor_exact
  simp only [exact_iff, range_subtype, linearProjOfIsCompl_ker]
  simp only [← range_eq_top, linearProjOfIsCompl_range]

theorem LinearMap.ker_baseChange_of_linearProjOfIsCompl
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂)
    (R : Type*) [CommRing R] [Algebra A R] :
    ker (baseChange R (linearProjOfIsCompl _ _ hM)) = range (baseChange R M₂.subtype) := by
  simpa only [← exact_iff] using ker_lTensor_of_linearProjOfIsCompl hM R

theorem LinearMap.isCompl_lTensor
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂)
    (Q : Type*) [AddCommGroup Q] [Module A Q] :
    IsCompl (range (lTensor Q M₁.subtype)) (range (lTensor Q M₂.subtype)) := by
  have hq :
    M₁.subtype.comp (linearProjOfIsCompl _ _ hM)
      + M₂.subtype.comp (linearProjOfIsCompl _ _ hM.symm) = id := by
    ext x
    simp only [add_apply, coe_comp, coeSubtype, Function.comp_apply,
      id_coe, id_eq]
    rw [linear_proj_add_linearProjOfIsCompl_eq_self]
  apply IsCompl.mk
  · rw [disjoint_def]
    intro x h h'
    rw [← id_apply x (R := A), ← lTensor_id, ← hq]
    simp only [lTensor_add, lTensor_comp,
      LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← ker_lTensor_of_linearProjOfIsCompl hM Q] at h'
    rw [← ker_lTensor_of_linearProjOfIsCompl hM.symm Q] at h
    rw [mem_ker] at h h'
    simp only [h', _root_.map_zero, h, add_zero]
  · rw [codisjoint_iff]
    rw [eq_top_iff]
    intro x _
    rw [← lTensor_id_apply Q _ x, ← hq]
    simp only [lTensor_add, lTensor_comp, add_apply, coe_comp, Function.comp_apply]
    exact Submodule.add_mem _
      (mem_sup_left (LinearMap.mem_range_self _ _))
      (mem_sup_right (LinearMap.mem_range_self _ _))

theorem Submodule.disjoint_map
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : Disjoint M₁ M₂)
    {N : Type*} [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Injective f):
    Disjoint (M₁.map f) (M₂.map f) := by
  rw [Submodule.disjoint_def] at hM ⊢
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hy'⟩
  rw [hf hy'] at hy
  rw [hM x hx hy, LinearMap.map_zero]

theorem Submodule.codisjoint_map
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : Codisjoint M₁ M₂)
    {N : Type*} [AddCommGroup N] [Module A N]
    {f : M →ₗ[A] N} (hf : Function.Surjective f):
    Codisjoint (M₁.map f) (M₂.map f) := by
  rw [codisjoint_iff, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.exists_add_eq_of_codisjoint hM x
  rw [LinearMap.map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (mem_map_of_mem hy))
    (Submodule.mem_sup_right (mem_map_of_mem hz))

theorem Submodule.isCompl_map
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂)
    {N : Type*} [AddCommGroup N] [Module A N]
    (f : M ≃ₗ[A] N) :
    IsCompl (M₁.map f) (M₂.map f) := by
  apply IsCompl.mk
  · exact Submodule.disjoint_map hM.disjoint f.injective
  · exact Submodule.codisjoint_map hM.codisjoint f.surjective

theorem LinearMap.isCompl_rTensor
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂)
    (Q : Type*) [AddCommGroup Q] [Module A Q] :
    IsCompl (range (rTensor Q M₁.subtype)) (range (rTensor Q M₂.subtype)) := by
  simp only [← comm_comp_lTensor_comp_comm_eq]
  simp only [LinearMap.range_comp]
  apply Submodule.isCompl_map
  simp only [LinearEquiv.range, Submodule.map_top]
  exact LinearMap.isCompl_lTensor hM Q

theorem LinearMap.isCompl_baseChange
    {M : Type*} [AddCommGroup M] [Module A M]
    {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂)
    (R : Type*) [CommRing R] [Algebra A R] :
    IsCompl (range (baseChange R M₁.subtype)) (range (baseChange R M₂.subtype)) := by
  rw [← isCompl_restrictScalars_iff A]
  exact isCompl_lTensor hM R

theorem Algebra.baseChange_bot {R S : Type*} [CommRing R] [Algebra A R] [CommRing S] [Algebra A S] :
    Subalgebra.toSubmodule ⊥ =
    LinearMap.range (LinearMap.baseChange R (Subalgebra.toSubmodule (⊥ : Subalgebra A S)).subtype) := by
  ext x
  simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot]
  simp only [Set.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y ⊗ₜ[A] ⟨1, (Subalgebra.mem_toSubmodule ⊥).mpr (one_mem ⊥)⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
      use 0
      simp only [zero_tmul, LinearMap.map_zero]
      simp
    | tmul r s =>
      rcases s with ⟨s, hs⟩
      simp only [Subalgebra.mem_toSubmodule] at hs
      obtain ⟨a, rfl⟩ := hs
      use a • r
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
        toRingHom_eq_coe, coe_coe, baseChange_tmul, coeSubtype]
      simp only [smul_tmul]
      rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      use x' + y'
      simp only [add_tmul, hx, hy, map_add]

theorem Algebra.TensorProduct.map_includeRight_eq_range_baseChange
    {S : Type*} [CommRing S] [Algebra A S] {I : Ideal S}
    (R : Type*) [CommRing R] [Algebra A R]  :
    Submodule.restrictScalars R (I.map Algebra.TensorProduct.includeRight)
    = LinearMap.range (LinearMap.baseChange R (Submodule.restrictScalars A I).subtype) := by
  ext x
  simp only [restrictScalars_mem, LinearMap.mem_range]
  constructor
  · intro hx
    apply Submodule.span_induction hx
      (p := fun x ↦ ∃ y, (LinearMap.baseChange R (Submodule.restrictScalars A I).subtype) y = x )
    · rintro x ⟨s, hs, rfl⟩; use 1 ⊗ₜ[A] ⟨s, hs⟩; rfl
    · use 0; simp only [_root_.map_zero]
    · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; use x + y; simp only [map_add]
    · rintro a _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => use 0; simp only [_root_.map_zero, smul_eq_mul, mul_zero]
      | tmul r s =>
        induction a using TensorProduct.induction_on with
        | zero =>
          use 0
          simp only [_root_.map_zero, baseChange_tmul, coeSubtype, smul_eq_mul, zero_mul]
        | tmul u v =>
          use (u * r) ⊗ₜ[A] (v • s)
          simp only [baseChange_tmul, coeSubtype, smul_eq_mul,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [Submodule.coe_smul, smul_eq_mul]
        | add u v hu hv =>
          obtain ⟨x, hx⟩ := hu
          obtain ⟨y, hy⟩ := hv
          use x + y
          rw [LinearMap.map_add, add_smul, hx, hy]
      | add x y hx hy =>
        obtain ⟨x', hx⟩ := hx
        obtain ⟨y', hy⟩ := hy
        use x' + y'
        simp only [map_add, hx, smul_eq_mul, hy, mul_add]
  · rintro ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero, Submodule.zero_mem]
    | tmul r s =>
      rcases s with ⟨s, hs⟩
      simp only [restrictScalars_mem] at hs
      simp only [baseChange_tmul, coeSubtype]
      rw [← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      rw [← IsScalarTower.algebraMap_smul (R ⊗[A] S) r, smul_eq_mul]
      apply Ideal.mul_mem_left
      exact Ideal.mem_map_of_mem Algebra.TensorProduct.includeRight hs
    | add x y hx hy =>
      simp only [map_add]
      exact Ideal.add_mem _ hx hy

/-- An ideal `J` of a commutative `R`-algebra `A` is an augmentation ideal
  if this ideal is a complement to `⊥ : Subalgebra R A` -/
def Ideal.IsAugmentation (R : Type*) [CommSemiring R]
    {A : Type*} [CommSemiring A] [Algebra R A] (J : Ideal A) : Prop :=
  IsCompl (Subalgebra.toSubmodule (⊥ : Subalgebra R A)) (J.restrictScalars R)

/-- The base change of an algebra with an augmentation ideal -/
theorem Ideal.isAugmentation_baseChange
    {S : Type*} [CommRing S] [Algebra A S]
    {I : Ideal S}
    (hI : IsCompl (Subalgebra.toSubmodule (⊥ : Subalgebra A S)) (I.restrictScalars A))
    {R : Type*} [CommRing R] [Algebra A R] :
    Ideal.IsAugmentation R (Ideal.map Algebra.TensorProduct.includeRight I :
      Ideal (R ⊗[A] S)) := by
  unfold Ideal.IsAugmentation
  rw [Algebra.baseChange_bot]
  rw [Algebra.TensorProduct.map_includeRight_eq_range_baseChange]
  exact isCompl_baseChange hI R

theorem Ideal.isAugmentation_subalgebra_iff (A : Type*) [CommSemiring A]
    {R : Type*} [CommSemiring R] [Algebra A R]
    {S : Subalgebra A R} {I : Ideal R} :
    I.IsAugmentation S ↔
    IsCompl (Subalgebra.toSubmodule S) (I.restrictScalars A) := by
  unfold Ideal.IsAugmentation
  rw [← Submodule.isCompl_restrictScalars_iff A, Subalgebra.restrictScalars_toSubmodule_bot]
  exact Iff.rfl

theorem Ideal.isAugmentation_tensorProduct
    (A : Type*) [CommRing A]
    {R : Type*} [CommRing R] [Algebra A R] {R₀ : Subalgebra A R} {I : Ideal R} (hI : I.IsAugmentation R₀)
    {S : Type*} [CommRing S] [Algebra A S] {S₀ : Subalgebra A S} {J : Ideal S} (hJ : J.IsAugmentation S₀) :
    let K : Ideal (R ⊗[A] S) := Ideal.map (Algebra.TensorProduct.includeLeft (S := A)) I ⊔ Ideal.map Algebra.TensorProduct.includeRight J
    let T₀ : Subalgebra A (R ⊗[A] S) := Subalgebra.map (Algebra.TensorProduct.map R₀.val S₀.val) ⊤
    K.IsAugmentation T₀ := by
  intro K T₀
  rw [Ideal.isAugmentation_subalgebra_iff] at hI hJ ⊢
  have hIS := LinearMap.isCompl_rTensor hI S
  have hJ' := codisjoint_iff.mp hJ.codisjoint
  -- Utiliser hJ' pour écrire une somme et appliquer DistribLattice.isCompl_assoc_of_disjoint
--  have hK : Submodule.restrictScalars A K = Submodule.restrictScalars A

/- mathématiquement, on dirait
   R = R₀ ⊕ I, S = S₀ ⊕ J,
   R ⊗ S = R₀ ⊗ S ⊕ I ⊗ S
        = (R₀ ⊗ S₀ ⊕ R₀ ⊗ J) ⊕ I ⊗ S
   DistribLattice.isCompl_assoc

   -/
#exit
-- OLD VERSION
/-- An ideal J of a commutative ring A is an augmentation ideal
if `Ideal.Quotient.mk J` has a right inverse which is a `RingHom` -/
def IsAugmentation : Prop :=
  ∃ g : A ⧸ J →+* A, Function.RightInverse g (Ideal.Quotient.mk J)

/-- An ideal `J` of a commutative `R`-algebra `A` is an augmentation ideal
if `Ideal.Quotient.mkₐ R J` has a right inverse which is an `AlgHom` -/
def IsAugmentationₐ (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A) : Prop :=
  ∃ g : A ⧸ J →ₐ[R] A, Function.RightInverse g (Ideal.Quotient.mkₐ R J)

theorem isAugmentationₐ_iff :
    J.IsAugmentationₐ R ↔
    ∃ (A₀ : Subalgebra R A), IsCompl (Subalgebra.toSubmodule A₀) (Submodule.restrictScalars R J) := by
  constructor
  · rintro ⟨f, hf⟩
    use f.range
    apply IsCompl.mk
    · rw [Submodule.disjoint_def]
      rintro x ⟨y, rfl⟩
      simp only [toRingHom_eq_coe, coe_coe, restrictScalars_mem]
      intro hy
      rw [← hf y, mkₐ_eq_mk]
      convert AlgHom.map_zero _
      rw [← mem_ker, mk_ker]
      exact hy
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have : x = f (mkₐ R J x) + (x - f (mkₐ R J x)) := by ring
      rw [this]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_left
        simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range, exists_apply_eq_apply]
      · apply Submodule.mem_sup_right
        simp only [Submodule.restrictScalars_mem]
        suffices x - f x ∈ ker (mkₐ R J) by
          convert this
          exact mk_ker.symm
        rw [mem_ker, map_sub, ← mkₐ_eq_mk R, hf, sub_self]
  · rintro ⟨A₀, ⟨hd, hc⟩⟩
    let u : A₀ →ₐ[R] A ⧸ J := (Ideal.Quotient.mkₐ R J).comp (Subalgebra.val A₀)
    suffices hu : Function.Bijective u by
      let u' : A₀ ≃ₐ[R] A ⧸ J := AlgEquiv.ofBijective u hu
      use (Subalgebra.val A₀).comp u'.symm
      rintro x
      rcases hu.surjective x with ⟨y, rfl⟩
      simp only [AlgHom.coe_comp, Subalgebra.coe_val, AlgHom.coe_coe, Function.comp_apply]
      -- Something like AlgEquiv.symm_apply_eq is missing
      suffices u y = u' y by
        rw [this]
        rw [AlgEquiv.leftInverse_symm]
        simp only [AlgEquiv.coe_ofBijective, AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val,
          Function.comp_apply, u', u]
      simp only [AlgEquiv.coe_ofBijective, u']
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x
      simp only [RingHom.mem_ker, mem_bot]
      simp only [Submodule.disjoint_def] at hd
      specialize hd x x.property
      simp only [Submodule.restrictScalars_mem, ZeroMemClass.coe_eq_zero] at hd
      intro hx
      apply hd
      simpa only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply, u, ← RingHom.mem_ker, mk_ker] using hx
    · -- missing RingHomClass argument for RingHom.range_top_iff_surjective
      intro x
      rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
      simp only [codisjoint_iff, eq_top_iff] at hc
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp (hc (show x ∈ ⊤ by exact trivial))
      use ⟨x, hx⟩
      rw [map_add]
      convert (add_zero _).symm
      rwa [← RingHom.mem_ker, mk_ker]

/-- If J is an `R`-algebra augmentation ideal, then S ⊗[R] J
  is a `S`-algebra augmentation ideal -/
theorem IsAugmentationₐ.baseChange
    (hJ : J.IsAugmentationₐ R)
    (S : Type*) [CommRing S] [Algebra R S] [Algebra A S] [IsScalarTower R A S] :
    Ideal.IsAugmentationₐ S (J.map Algebra.TensorProduct.includeRight : Ideal (S ⊗[R] A)) := by
  obtain ⟨f, hf⟩ := hJ
  have that : RingHom.ker (mkₐ R J) = J := mkₐ_ker R J
  let g : S ⊗[R] A ⧸ (Ideal.map Algebra.TensorProduct.includeRight J : Ideal (S ⊗[R] A)) →ₐ[S] S ⊗[R] (A ⧸ J) := {
    toRingHom := by
      apply Quotient.lift (Ideal.map Algebra.TensorProduct.includeRight J)
        ((Algebra.TensorProduct.map (AlgHom.id R S) (mkₐ R J)))
      intro a ha
      rwa [← that, ← Algebra.TensorProduct.lTensor_ker _ (mkₐ_surjective R J), mem_ker] at ha
    commutes' := fun s ↦ by
      have : algebraMap S ((S ⊗[R] A) ⧸ (map Algebra.TensorProduct.includeRight J : Ideal (S ⊗[R] A))) s = mkₐ S _ (s ⊗ₜ[R] 1) := by
        rw [mkₐ_eq_mk, ← mk_algebraMap, Algebra.TensorProduct.algebraMap_apply,
          Algebra.id.map_eq_self]
      simp [this] }
  -- let g := Ideal.kerLiftAlg (Algebra.TensorProduct.map (AlgHom.id A S) (mkₐ A I))
  -- rw [Algebra.TensorProduct.lTensor_ker _ (mkₐ_surjective A I), that] at g
  -- it seems unusable
  let g' : S ⊗[R] (A ⧸ J) →ₐ[S] S ⊗[R] A := Algebra.TensorProduct.map (AlgHom.id S S) f
  use g'.comp g
  intro x
  rcases mkₐ_surjective A _ x with ⟨x, rfl⟩
  simp only [mkₐ_eq_mk, AlgHom.coe_mk, coe_coe, AlgHom.coe_comp, Function.comp_apply, liftₐ_apply,
    Quotient.lift_mk, g]
  induction x using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul s r =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, mkₐ_eq_mk, g'] --  hf r]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← TensorProduct.tmul_sub]
    rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    rw [← algebraMap_smul (S ⊗[R] A), smul_eq_mul]
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight)
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply hf
  | add x y hx hy => simp only [map_add, hx, hy]
