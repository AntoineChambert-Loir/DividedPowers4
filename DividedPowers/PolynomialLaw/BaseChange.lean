import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import DividedPowers.PolynomialLaw.Basic2
import DividedPowers.PolynomialLaw.Coeff

/-! # Base change of polynomial maps

This file defines a base change map
  `PolynomialLaw R M N →ₗ[R] PolynomialLaw R' (R' ⊗[R] M) (R' ⊗[R] N)``
when M and N are R-modules and R' is an R-algebra (commutative)

## Work in progress

This requires to simplify the tensor product
  `S' ⊗[R'] (R' ⊗[R] M)`
to
  `S' ⊗[R] M`
using an S'-isomorphism — something Mathlib doesn't know (yet)
because TensorProduct.assoc lacks some heteronomy.
This is done in a first part.

Then the base change is defined as a map.

## TODO

- Compare ground
- Extend `PolynomialMap.baseChange` to a linear map.
- Prove that coeff, multiCoeff, biCoeff, commute with base change,
as well as for divided (partial) differentials

-/

namespace Set

theorem prod_eq_iff_of_nonempty {α β : Type*} {s s' : Set α} {t t' : Set β}
    (hs : s.Nonempty) (ht : t.Nonempty) :
    s ×ˢ t = s' ×ˢ t' ↔ (s = s' ∧ t = t') := by
  constructor
  · intro h
    suffices hss' : s = s' by
      refine ⟨hss', ?_⟩
      ext b
      obtain ⟨a, ha⟩ := hs
      have ha' : a ∈ s' := by rwa [← hss']
      constructor
      · intro hb
        have hst : (a, b) ∈ s ×ˢ t := by simp [Set.mem_prod, ha, hb]
        rw [h, Set.mem_prod] at hst
        exact hst.2
      · intro hb
        have hst : (a, b) ∈ s' ×ˢ t' := by simp [Set.mem_prod, ha', hb]
        rw [← h, Set.mem_prod] at hst
        exact hst.2
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := ht
      have h' : (a, b) ∈ s ×ˢ t := by simp [Set.mem_prod, ha, hb]
      rw [h, Set.mem_prod] at h'
      exact h'.1
    · intro ha
      have : t'.Nonempty := by
        by_contra! ht'
        simp only [ht', Set.prod_empty, Set.prod_eq_empty_iff] at h
        cases h with
        | inl h => simp [h] at hs
        | inr h => simp [h] at ht
      obtain ⟨b, hb⟩ := this
      have h' : (a, b) ∈ s' ×ˢ t' := by simp [Set.mem_prod, ha, hb]
      rw [← h, Set.mem_prod] at h'
      exact h'.1
  · rintro ⟨rfl, rfl⟩; rfl

end Set

namespace TensorProduct

variable {R : Type*} [CommSemiring R]
  {M : Type*}  [AddCommMonoid M] [Module R M]

variable {R' : Type*} [CommSemiring R'] [Algebra R R']
variable {S' : Type*} [CommSemiring S'] [Algebra R' S']
variable {S'' : Type*} [CommSemiring S''] [Algebra R' S'']
variable (φ : S' →ₐ[R'] S'')

variable [Algebra R S'] [IsScalarTower R R' S']
variable [Algebra R S''] [IsScalarTower R R' S'']

/-- an auxiliary map -/
def baseChangeEquiv' : (S' ⊗[R'] R') ⊗[R] M ≃ₗ[S'] S' ⊗[R] M := {
  toAddEquiv := (LinearEquiv.rTensor M ((TensorProduct.rid R' S').restrictScalars R)).toAddEquiv
  map_smul' r' srm := by
    induction srm using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearEquiv.coe_rTensor, smul_add, AddHom.toFun_eq_coe, map_add,
        LinearMap.coe_toAddHom, RingHom.id_apply]
      congr
    | tmul sr m =>
      simp
      rw [smul_tmul']
      simp
      congr
      induction sr using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul s r =>
        rw [← LinearEquiv.eq_symm_apply]
        simp only [rid_tmul, smul_eq_mul, Algebra.mul_smul_comm, map_smul, rid_symm_apply]
        rw [smul_tmul', smul_eq_mul]
        simp [← tmul_smul] }

def baseChangeEquiv :
    S' ⊗[R'] R' ⊗[R] M ≃ₗ[S'] S' ⊗[R] M :=
  (AlgebraTensorModule.assoc R R' S' S' R' M).symm.trans baseChangeEquiv'

theorem baseChangeEquiv_rTensor_baseChangeEquivSymm (y : S' ⊗[R] M) :
    baseChangeEquiv
      ((LinearMap.rTensor (R' ⊗[R] M) φ.toLinearMap) ((baseChangeEquiv (R' := R')).symm y)) =
      LinearMap.rTensor M ((φ.restrictScalars R).toLinearMap) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s n => simp [baseChangeEquiv, baseChangeEquiv']

theorem baseChangeEquiv_rTensor_eq_baseChangeEquivSymm_rTensor (x : S' ⊗[R'] R' ⊗[R] M) :
    baseChangeEquiv ((LinearMap.rTensor (R' ⊗[R] M) φ.toLinearMap) x) =
      LinearMap.rTensor M ((φ.restrictScalars R).toLinearMap) (baseChangeEquiv x) := by
  set y := baseChangeEquiv x with hy
  rw [← LinearEquiv.eq_symm_apply] at hy
  rw [hy, baseChangeEquiv_rTensor_baseChangeEquivSymm]

theorem baseChangeEquiv_one_tmul (m : R' ⊗[R] M) :
    baseChangeEquiv ((1 : R') ⊗ₜ[R'] m) = m := by
   simp [baseChangeEquiv, baseChangeEquiv']
   induction m using TensorProduct.induction_on with
   | zero => simp
   | add x y hx hy => simp [tmul_add, hx, hy]
   | tmul s m => simp

theorem baseChangeEquiv_lid (m : R' ⊗[R] M) :
    (baseChangeEquiv ((TensorProduct.lid R' (R' ⊗[R] M)).symm m)) = m :=  by
  simp [lid_symm_apply, baseChangeEquiv, baseChangeEquiv']
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [tmul_add, hx, hy]
  | tmul s m => simp

def baseChangeEquiv_comp_lid_symm :
    R' ⊗[R] M ≃ₗ[R'] R' ⊗[R] M :=
    (TensorProduct.lid R' _).symm.trans baseChangeEquiv

end TensorProduct

namespace PolynomialLaw

open TensorProduct

universe u v w
variable {R : Type u} [CommSemiring R]
  {M : Type*}  [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]

variable (R' : Type v) [CommSemiring R'] [Algebra R R']

/-- The base change of a polynomial law. -/
noncomputable def baseChange (f : M →ₚₗ[R] N) :
    (R' ⊗[R] M) →ₚₗ[R'] (R' ⊗[R] N) where
  toFun' S' _ _ srm := by
    let algRS' : Algebra R S' :=
      RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    have istRR'S' : @IsScalarTower R R' S' _ _ algRS'.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    exact baseChangeEquiv (R' := R').symm (f.toFun S' (baseChangeEquiv srm))
  isCompat' {S' _ _ S'' _ _} φ := by
    let algRS' : Algebra R S' :=
      RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    have istRR'S' : @IsScalarTower R R' S' _ _ algRS'.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    let algRS'' : Algebra R S'' :=
      RingHom.toAlgebra ((algebraMap R' S'').comp (algebraMap R R'))
    have istRR'S'' : @IsScalarTower R R' S'' _ _ algRS''.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    ext srm
    dsimp only
    symm
    simp only [Function.comp_apply]
    rw [LinearEquiv.symm_apply_eq]
    rw [baseChangeEquiv_rTensor_eq_baseChangeEquivSymm_rTensor]
    rw [baseChangeEquiv_rTensor_baseChangeEquivSymm]
    rw [← f.isCompat_apply]

theorem baseChangeEquiv_tmul_tmul {R M R' S' : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [CommSemiring R'] [Algebra R R']
    [CommSemiring S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S']
    (s' : S') (r' : R') (m : M) :
    baseChangeEquiv (s' ⊗ₜ[R'] r' ⊗ₜ[R] m) = (r' • s') ⊗ₜ[R] m := by
  simp [baseChangeEquiv, baseChangeEquiv']

/- -- doesn't work for instances reasons
theorem baseChangeEquiv_congr {R : Type u} {M : Type*} {R' : Type u} {S' : Type u}
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₚₗ[R] N)
    [CommSemiring R'] [Algebra R R']
    [CommSemiring S'] [Algebra R' S']
    [alg1 : Algebra R S'] [ist1 : IsScalarTower R R' S']
    [alg2 : Algebra R S'] [ist2 : IsScalarTower R R' S']
    (srm : S' ⊗[R'] R' ⊗[R] M) :
    let j1 := @baseChangeEquiv R _ M _ _ R' _ _ S' _ _ alg1 ist1
    let j2 := @baseChangeEquiv R _ M _ _ R' _ _ S' _ _ alg2 ist2
    @f.toFun' S' _ alg1 (j1 srm) = @f.toFun' S' _ alg2 (j2 srm) := by
    sorry
-/

-- generalize to `toFun`, with `S'` in an arbitrary universe
theorem baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum
    (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R')
    {S' : Type v} [CommSemiring S'] [Algebra R' S'] (s : ι → S') :
    (f.baseChange R').toFun' S' (∑ i, s i ⊗ₜ[R'] r i ⊗ₜ[R] m i) =
      (((coeff m) f).sum fun k n ↦  ((∏ i, s i ^ k i) ⊗ₜ[R'] (∏ i, r i ^ k i) ⊗ₜ[R] n))  := by
  simp only [baseChange, map_sum, baseChangeEquiv_tmul_tmul]
  rw [toFun_sum_tmul_eq_coeff_sum]
  rw [map_finsuppSum]
  apply congr_arg
  ext k n
  rw [LinearEquiv.symm_apply_eq]
  simp_rw [Algebra.smul_def, mul_pow]
  rw [Finset.prod_mul_distrib]
  simp_rw [← map_pow, ← map_prod, ← Algebra.smul_def]
  let algRS' : Algebra R S' :=
    RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
  have istRR'S' : @IsScalarTower R R' S' _ _ algRS'.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
  rw [← baseChangeEquiv_tmul_tmul]

theorem  TensorProduct.exists_nonempty_finset {R M N : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (x : M ⊗[R] N) :
    ∃ (s : Finset (M × N)) (_ : s.Nonempty), x = ∑ j ∈ s, j.1 ⊗ₜ[R] j.2 := by
  obtain ⟨s, hxs⟩ := TensorProduct.exists_finset x
  by_cases hs : s.Nonempty
  · exact ⟨s, hs, hxs⟩
  · use {(0, 0)}
    simp only [Finset.not_nonempty_iff_eq_empty] at hs ⊢
    simp [hxs, hs]

-- Doesn't work yet
theorem exists_eq_sum_tmul_tmul'
      {R S M N P: Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid P] [Module R P]
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommMonoid M] [Module S M]
    (x : M ⊗[S] N ⊗[R] P) :
    ∃ (ι : Type*) (hι : Fintype ι) (m : ι → M) (n : ι → N) (p : ι → P),
      x = ∑ i, m i ⊗ₜ[S] n i ⊗ₜ[R] p i := by
  sorry


-- Doesn't work yet
theorem exists_eq_sum_tmul_tmul
      {R S M N P: Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid P] [Module R P]
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommMonoid M] [Module S M]
    (x : M ⊗[S] N ⊗[R] P) :
    ∃ (ξ : Finset (M × N × P)),
      x = ξ.sum (fun mnp ↦ mnp.1 ⊗ₜ[S] mnp.2.1 ⊗ₜ[R] mnp.2.2) := by

  obtain ⟨x1, h1⟩ := TensorProduct.exists_finset x
  have (i : x1) := TensorProduct.exists_finset i.val.2
  set x2 := fun (i : x1) ↦ (TensorProduct.exists_finset i.val.2).choose
  have hx2 (i : x1) : i.val.2 = ∑ j ∈ x2 i, j.1 ⊗ₜ[R] j.2 :=
    (TensorProduct.exists_finset i.val.2).choose_spec

  classical
  let f : M × N ⊗[R] P → Finset (M × N × P) :=
    fun mnp ↦ Finset.product {mnp.1} (TensorProduct.exists_finset mnp.2).choose

  have hf (m : M) (np : N ⊗[R] P) :
      (TensorProduct.exists_finset np).choose = Finset.image Prod.snd (f (m, np)) :=
    (Finset.product_image_snd (Finset.singleton_nonempty m)).symm
  have hf' (m : M) (np : N ⊗[R] P) :
      np = ∑ x ∈ ((f (m, np)).image Prod.snd), x.1 ⊗ₜ[R] x.2 := by
    rw [← hf]
    exact (TensorProduct.exists_finset _).choose_spec

  let jf : M × N ⊗[R] P ↪ Finset (M × N × P) := {
    toFun := f
    inj' := fun ⟨m, np⟩ ⟨m', np'⟩ h ↦ by
      suffices m = m' by
        ext
        · exact this
        have k := hf' m np
        rwa [h, ← hf' m' np'] at k
      by_cases hnp : np = 0
      · sorry
      · have H1 (m : M) (np : N ⊗[R] P) (hnp : np ≠ 0) :
            {m} = Finset.image Prod.fst (f (m, np)) := by
          symm
          apply Finset.product_image_fst
          by_contra! hm'
          apply hnp
          simp only [Finset.not_nonempty_iff_eq_empty] at hm'
          rw [hf' m np]
          have that := hf m np
          rw [hm'] at that
          simp [← that]
        have hm := H1 m np hnp
        rw [h] at hm
        rw [← H1 m' np' ?_] at hm
        · simpa using hm
        intro hnp'
        apply hnp
        rwa [hf' m np, h, ← hf'] }
  sorry

example (s t : Finset ℕ) : Finset (ℕ × ℕ) := Finset.product s t

theorem baseChange_apply (f : M →ₚₗ[R] N)
    {R' : Type u} [CommSemiring R'] [Algebra R R']
    {S' : Type u} [CommSemiring S']
    [algR'S' : Algebra R' S'] [algRS' : Algebra R S'] [istRR'S' : IsScalarTower R R' S']
    (srm : S' ⊗[R'] R' ⊗[R] M) :
    (f.baseChange R').toFun S' srm = baseChangeEquiv.symm (f.toFun S' (baseChangeEquiv srm)) := by
  obtain ⟨ι, hι, s, r, m, rfl⟩ := exists_eq_sum_tmul_tmul' srm
  classical
  rw [toFun_eq_toFun']
  rw [baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum]
  rw [map_sum]
  simp_rw [baseChangeEquiv_tmul_tmul]
  rw [f.toFun_sum_tmul_eq_coeff_sum]
  rw [map_finsuppSum]
  congr
  ext k n
  rw [LinearEquiv.eq_symm_apply]
  rw [baseChangeEquiv_tmul_tmul]
  congr
  simp_rw [smul_pow, Algebra.smul_def, Finset.prod_mul_distrib,
    ← map_prod]



/- à guche :
 @baseChangeEquiv R inst✝⁸ N inst✝⁵ inst✝⁴ R' inst✝³ inst✝² S' inst✝¹ algR'S'
  ((algebraMap R' S').comp (algebraMap R R')).toAlgebra ⋯ : S' ⊗[R'] R' ⊗[R] N ≃ₗ[S'] S' ⊗[R] N

à droite :

@baseChangeEquiv R inst✝⁸ N inst✝⁵ inst✝⁴ R' inst✝³ inst✝² S' inst✝¹ algR'S' algRS' inst✝ : S' ⊗[R'] R' ⊗[R] N ≃ₗ[S'] S' ⊗[R] N


-/
  have H1 : ((algebraMap R' S').comp (algebraMap R R')).toAlgebra = algRS' := by
    ext r s
    change (algebraMap R' S').comp (algebraMap R R') r • s = r • s
    simp [← Algebra.smul_def]
  have H2 : @IsScalarTower R R' S' _ _ algRS'.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ by simp only [← H1]; rfl)
  suffices @baseChangeEquiv R _ N _ _ R' _ _ S' _ algR'S' algRS' H2
    = @baseChangeEquiv R _ N _ _ R' _ _ S' _ algR'S' ((algebraMap R' S').comp (algebraMap R R')).toAlgebra sorry by
      sorry
  congr 1
  · congr
    simp [this]
  · congr
  · apply Function.hfunext
    congr
    intro x y h
    congr
  · sorry
  · sorry
  · sorry

theorem toFun_baseChangeEquiv_one_tmul (f : M →ₚₗ[R] N) (m : R' ⊗[R] M) :
    f.toFun R' (baseChangeEquiv ((1 : R') ⊗ₜ[R'] m)) = baseChangeEquiv ((1 : R') ⊗ₜ[R'] f.toFun R' m) := by
  simp [baseChangeEquiv_one_tmul]

theorem baseChange_ground (f : M →ₚₗ[R] N) :
    (f.baseChange R').ground = f.toFun R' := by
  ext m
  simp only [ground, Function.comp_apply]
  simp only [← LinearEquiv.eq_symm_apply, lid_symm_apply]
  simp only [baseChange, LinearEquiv.symm_apply_eq]


  simp only [ground, baseChange, Function.comp_apply]
  simp only [← LinearEquiv.eq_symm_apply, lid_symm_apply]
  have h1 : f.toFun R' (baseChangeEquiv (1 ⊗ₜ[R'] m)) = f.toFun R' m := by
    rw [baseChangeEquiv_one_tmul]
  have h2 : f.toFun R' m = baseChangeEquiv (1 ⊗ₜ[R'] f.toFun R' m) := by
    rw [baseChangeEquiv_one_tmul]
  simp only [LinearEquiv.symm_symm]
  have h := h1.trans h2
  convert h
  · ext r s
    change (algebraMap R' R').comp (algebraMap R R') r • s = _
    simp [Algebra.smul_def]
  · ext r s
    change (algebraMap R' R').comp (algebraMap R R') r • s = _
    simp [Algebra.smul_def]
  · congr
    sorry
  · sorry


noncomputable def baseChange_linearMap : (M →ₚₗ[R] N) →ₗ[R] RestrictScalars R R' ((R' ⊗[R] M) →ₚₗ[R'] (R' ⊗[R] N)) where
  toFun := baseChange R'
  map_add' f g := by
    change baseChange R' (f + g) = baseChange R' f + baseChange R' g
    ext S' _ _ srm
    simp [baseChange, add_toFun]
  map_smul' r f := by
    change baseChange R' (r • f) = algebraMap R R' r • baseChange R' f
    ext S' _ _ srm
    let _ : Algebra R S' := RingHom.toAlgebra
      ((algebraMap R' S').comp (algebraMap R R'))
    have _ : IsScalarTower R R' S' := sorry
    simp only [baseChange, smul_toFun, Pi.smul_apply, smul_def, algebraMap_smul]
    rw [← algebraMap_smul S' r (f.toFun S' (baseChangeEquiv srm))]
    rw [← algebraMap_smul S' r]
    rw [map_smul]


end PolynomialLaw
