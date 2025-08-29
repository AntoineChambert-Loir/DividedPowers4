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

namespace Finset

noncomputable def biUnion₂ {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) : Finset (α × β) :=
  Finset.biUnion s (fun a ↦ {a} ×ˢ t a)

@[to_additive]
theorem prod_biUnion₂ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [CommMonoid γ]
    {s : Finset α} {t : α → Finset β} {f : α → β → γ} :
    ∏ a ∈ s, ∏ b ∈ t a, f a b =
      ∏ x ∈ Finset.biUnion₂ s t, f x.1 x.2 := by
  simp only [Finset.biUnion₂]
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro a ha
    simp only [Finset.singleton_product, Finset.prod_map, Function.Embedding.coeFn_mk]
  · intro a _ a' _ h
    simp only [Function.onFun, ← Finset.disjoint_coe, Finset.singleton_product, Finset.coe_map, Function.Embedding.coeFn_mk]
    rw [Set.disjoint_iff_forall_ne]
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' H
    apply h
    simp only [Set.mem_image, Finset.mem_coe, Prod.mk.injEq, exists_eq_right_right] at hxy hxy'
    simp only [Prod.mk.injEq] at H
    rw [hxy.2, H.1, hxy'.2]

end Finset

namespace Multiset

variable {α β γ M : Type*}
    [CommMonoid M]
  -- [DecidableEq α] [DecidableEq β] [DecidableEq γ]

@[to_additive]
theorem map_fst_prod (n : Multiset γ) (g : α → γ → M) (a : α) :
    (map (g a) n).prod = (map (fun x ↦ g x.1 x.2) (({a} : Multiset α).product n)).prod := by
  induction n using Multiset.induction_on with
  | empty => rfl
  | cons b n hn =>
    simp [Multiset.map_cons, Multiset.prod_cons, hn,
      show ({a} : Multiset α).product (b ::ₘ n) = (a, b) ::ₘ ({a} : Multiset α).product n from Multiset.product_cons b {a} n]

/--  ∏ (a, b) ∈ m, ∏ c ∈ f b, g a c = ∏ (a, c) ∈ (m.map ?_), g a c -/
@[to_additive]
theorem map_prod_map_prod
    (m : Multiset (α × β)) (f : β → Multiset γ) (g : α → γ → M) :
    (m.map (fun x ↦ ((f x.2).map (g x.1)).prod)).prod =
      ((Multiset.map (fun x ↦ Multiset.product {x.1} (f x.2)) m).sum.map (fun x ↦ g x.1 x.2)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m hm =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.map_add,
      Multiset.prod_add]
    congr 1
    apply map_fst_prod

example [DecidableEq α] (m : Multiset α) (f : α → M) :
    (m.map f).prod = ∏ a ∈ m.toFinset, f a ^ m.count a := by
  exact Finset.prod_multiset_map_count m f

-- example (m : Multiset α) (f : α → β) (g : β → γ) : g (m.map f).prod
end Multiset

namespace TensorProduct

variable {R : Type*} [CommSemiring R]
  {M : Type*}  [AddCommMonoid M] [Module R M]
  {N : Type*}  [AddCommMonoid N] [Module R N]

theorem multiset_sum_tmul (m : Multiset M) (n : N) :
    m.sum ⊗ₜ[R] n = (m.map (fun x ↦ x ⊗ₜ[R] n)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a n has => simp [has, add_tmul]

theorem tmul_multiset_sum (m : M) (n : Multiset N) :
    m ⊗ₜ[R] n.sum = (n.map (fun y ↦ m ⊗ₜ[R] y)).sum := by
  induction n using Multiset.induction_on with
  | empty => simp
  | cons a n has => simp [has, tmul_add]

theorem exists_nonempty_finset (x : M ⊗[R] N) :
    ∃ (s : Finset (M × N)), s.Nonempty ∧ x = ∑ j ∈ s, j.1 ⊗ₜ[R] j.2 := by
  obtain ⟨s, hxs⟩ := TensorProduct.exists_finset x
  by_cases hs : s.Nonempty
  · exact ⟨s, hs, hxs⟩
  · use {(0, 0)}
    simp only [Finset.not_nonempty_iff_eq_empty] at hs ⊢
    simp [hxs, hs]

theorem exists_multiset_eq_sum_tmul_tmul {S P: Type*}
    [CommSemiring S] [Algebra R S]
    [Module S N] [IsScalarTower R S N]
    [AddCommMonoid P] [Module S P]
    (x : M ⊗[R] N ⊗[S] P) :
    ∃ (ξ : Multiset (M × N × P)),
      x = (ξ.map (fun x ↦ x.1 ⊗ₜ[R] x.2.1 ⊗ₜ[S] x.2.2)).sum := by
  obtain ⟨m1, hx⟩ := TensorProduct.exists_multiset x
  let m2 (y : N ⊗[S] P) := (TensorProduct.exists_multiset y).choose
  use (m1.map (fun x ↦ ({x.1} : Multiset M).product (m2 x.2))).sum
  have hx' : x = (m1.map
    fun i ↦ (((m2 i.2).map (fun z ↦ z.1 ⊗ₜ[S] z.2)).map (fun y ↦ i.1 ⊗ₜ[R] y)).sum
      ).sum := by
    rw [hx]
    apply congr_arg
    apply congr_arg₂ _ _ rfl
    ext ⟨m, np⟩
    dsimp only
    simp_rw [← tmul_multiset_sum m _]
    congr
    apply (TensorProduct.exists_multiset _).choose_spec
  simp only [Multiset.map_map, Function.comp_apply] at hx'
  classical
  rwa [Multiset.map_sum_map_sum m1 m2 (g := fun x y ↦ x ⊗ₜ[R] y.1 ⊗ₜ[S] y.2)] at hx'

theorem exists_multiset_eq_sum_tmul_tmul' {R S M N P: Type*}
    [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module S N]
    [AddCommMonoid P] [Module S P]
    [Algebra S R] [Module R N] [IsScalarTower S R N]
    (x : M ⊗[R] N ⊗[S] P) :
    ∃ (ξ : Multiset (M × N × P)),
      x = (ξ.map (fun x ↦ x.1 ⊗ₜ[R] x.2.1 ⊗ₜ[S] x.2.2)).sum := by
  obtain ⟨m1, hx⟩ := TensorProduct.exists_multiset x
  let m2 (y : N ⊗[S] P) := (TensorProduct.exists_multiset y).choose
  use (m1.map (fun x ↦ ({x.1} : Multiset M).product (m2 x.2))).sum
  have hx' : x = (m1.map
    fun i ↦ (((m2 i.2).map (fun z ↦ z.1 ⊗ₜ[S] z.2)).map (fun y ↦ i.1 ⊗ₜ[R] y)).sum
      ).sum := by
    rw [hx]
    apply congr_arg
    apply congr_arg₂ _ _ rfl
    ext ⟨m, np⟩
    dsimp only
    simp_rw [← tmul_multiset_sum m _]
    congr
    apply (TensorProduct.exists_multiset _).choose_spec
  simp only [Multiset.map_map, Function.comp_apply] at hx'
  classical
  rwa [Multiset.map_sum_map_sum m1 m2 (g := fun x y ↦ x ⊗ₜ[R] y.1 ⊗ₜ[S] y.2)] at hx'

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

-- Not working
/-- The coefficients of a base change of a polynomial law. -/
example (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R') (k : ι →₀ ℕ) :
    coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k =
      (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k := by
  nth_rewrite 1 [coeff]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  simp only [MvPolynomial.scalarRTensor, finsuppScalarLeft]
  simp [finsuppLeft]
  rw [← LinearEquiv.eq_symm_apply, lid_symm_apply]
  simp [finsuppLEquivDirectSum, finsuppLequivDFinsupp]
  have : MvPolynomial ι R' ⊗[R'] R' ⊗[R] N
    ≃ₗ[R'] MvPolynomial ι R' ⊗[R] N := by
      exact AlgebraTensorModule.cancelBaseChange R R' R' (MvPolynomial ι R') N
  have : (generize fun i ↦ r i ⊗ₜ[R] m i) (baseChange R' f)
   = (AlgebraTensorModule.cancelBaseChange R R' R' (MvPolynomial ι R') N).symm (generize' m r f) := by
     rw [generize'_eq_generize]
     simp [baseChange, baseChangeEquiv, baseChangeEquiv']
     sorry
  sorry

-- Todo
theorem baseChange_toFun_smul_tmul_tmul_eq_coeff_sum
    (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R')
    {S' : Type*} [CommSemiring S'] [Algebra R' S'] (s : ι → S') :
    (f.baseChange R').toFun S' (∑ i, s i ⊗ₜ[R'] r i ⊗ₜ[R] m i) =
      (((coeff m) f).sum fun k n ↦  ((∏ i, s i ^ k i) ⊗ₜ[R'] (∏ i, r i ^ k i) ⊗ₜ[R] n))  := by
  sorry

theorem baseChange_apply (f : M →ₚₗ[R] N)
    {R' : Type u} [CommSemiring R'] [Algebra R R']
    {S' : Type u} [CommSemiring S']
    [algR'S' : Algebra R' S'] [algRS' : Algebra R S'] [istRR'S' : IsScalarTower R R' S']
    (srm : S' ⊗[R'] R' ⊗[R] M) :
    (f.baseChange R').toFun S' srm = baseChangeEquiv.symm (f.toFun S' (baseChangeEquiv srm)) := by
  obtain ⟨m, rfl⟩ := exists_multiset_eq_sum_tmul_tmul' srm
  classical
  rw [toFun_eq_toFun']
  erw [Finset.sum_multiset_map_count]
  simp_rw [smul_tmul']
  rw [← Finset.sum_attach, ← Finset.sum_coe_sort_eq_attach]
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

theorem toFun_baseChangeEquiv_one_tmul (f : M →ₚₗ[R] N) (m : R' ⊗[R] M) :
    f.toFun R' (baseChangeEquiv ((1 : R') ⊗ₜ[R'] m)) = baseChangeEquiv ((1 : R') ⊗ₜ[R'] f.toFun R' m) := by
  simp [baseChangeEquiv_one_tmul]

theorem baseChange_ground (f : M →ₚₗ[R] N) :
    (f.baseChange R').ground = f.toFun R' := by
  ext m
  simp only [ground, Function.comp_apply]
  simp only [← LinearEquiv.eq_symm_apply, lid_symm_apply]
  simp only [baseChange, LinearEquiv.symm_apply_eq]
  sorry


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
    have _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    simp only [baseChange, smul_toFun, Pi.smul_apply, smul_def, algebraMap_smul]
    rw [← algebraMap_smul S' r (f.toFun S' (baseChangeEquiv srm))]
    rw [← algebraMap_smul S' r]
    rw [map_smul]

end PolynomialLaw
