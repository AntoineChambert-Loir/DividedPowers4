/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.PolynomialLaw.Coeff
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Base change of polynomial laws

This file defines a base change map
  `PolynomialLaw R M N →ₗ[R] PolynomialLaw R' (R' ⊗[R] M) (R' ⊗[R] N)`
when `M` and `N` are `R`-modules and `R'` is a (commutative) `R`-algebra.

This requires to simplify the tensor product `S' ⊗[R'] (R' ⊗[R] M)`
to `S' ⊗[R] M` using an `S'`-isomorphism — something Mathlib doesn't know (yet)
because TensorProduct.assoc lacks some heteronomy.
This is done in the first part of the file.

Then the base change is defined as a map.

## Main definitions

* `TensorProduct.baseChangeEquiv`: the natural `S'`-linear isomorphism from the triple tensor
  product `S' ⊗[R'] (R' ⊗[R] M)` to `S' ⊗[R] M`.

* `PolynomialLaw.baseChange`: the base change of a polynomial law.

* `PolynomialLaw.baseChangeHom`: the base change of a polynomial law, as a linear map.

## Main results

* `PolynomialLaw.coeff_baseChange_tmul`: the coefficients of the base change of a polynomial law
  satisfy the formula
  `coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k = (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k`.

* `PolynomialLaw.baseChange_ground`: for any `f : M →ₚₗ[R] N)`, one has
  `(f.baseChange R').ground = f.toFun R'`.

## TODO
- Prove that `coeff`, `multiCoeff`, `biCoeff`, commute with base change,
and that the same is true for divided (partial) differentials.

-/

namespace Finset

/-- `Finset.biUnion₂ s t` the union of `{a} ×ˢ t a` over `a ∈ s`. -/
noncomputable def biUnion₂ {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) : Finset (α × β) :=
  Finset.biUnion s (fun a ↦ {a} ×ˢ t a)

@[to_additive]
theorem prod_biUnion₂ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [CommMonoid γ]
    {s : Finset α} {t : α → Finset β} {f : α → β → γ} :
    ∏ a ∈ s, ∏ b ∈ t a, f a b = ∏ x ∈ Finset.biUnion₂ s t, f x.1 x.2 := by
  rw [Finset.biUnion₂, Finset.prod_biUnion]
  · exact Finset.prod_congr rfl (fun _ _ ↦ by simp)
  · intro a _ a' _ h
    simp only [Function.onFun, ← Finset.disjoint_coe, Finset.singleton_product, Finset.coe_map,
      Function.Embedding.coeFn_mk]
    rw [Set.disjoint_iff_forall_ne]
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' H
    apply h
    simp only [Set.mem_image, Finset.mem_coe, Prod.mk.injEq, exists_eq_right_right] at hxy hxy'
    simp only [Prod.mk.injEq] at H
    rw [hxy.2, H.1, hxy'.2]

end Finset

namespace Multiset

variable {α β γ M : Type*} [CommMonoid M]

@[to_additive]
theorem map_fst_prod (n : Multiset γ) (g : α → γ → M) (a : α) :
    (map (g a) n).prod = (map (fun x ↦ g x.1 x.2) (({a} : Multiset α).product n)).prod := by
  induction n using Multiset.induction_on with
  | empty => rfl
  | cons b n hn =>
    simp [Multiset.map_cons, Multiset.prod_cons, hn, show ({a} : Multiset α).product (b ::ₘ n) =
      (a, b) ::ₘ ({a} : Multiset α).product n from Multiset.product_cons b {a} n]

@[to_additive]
theorem map_prod_map_prod (m : Multiset (α × β)) (f : β → Multiset γ) (g : α → γ → M) :
    (m.map (fun x ↦ ((f x.2).map (g x.1)).prod)).prod =
      ((Multiset.map (fun x ↦ Multiset.product {x.1} (f x.2)) m).sum.map
        (fun x ↦ g x.1 x.2)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m hm =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.map_add,
      Multiset.prod_add]
    congr 1
    apply map_fst_prod

end Multiset

namespace TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

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

theorem exists_multiset_eq_sum_tmul_tmul {S P: Type*} [CommSemiring S] [Algebra R S]
    [Module S N] [IsScalarTower R S N] [AddCommMonoid P] [Module S P] (x : M ⊗[R] (N ⊗[S] P)) :
    ∃ (ξ : Multiset (M × N × P)), x = (ξ.map (fun x ↦ x.1 ⊗ₜ[R] (x.2.1 ⊗ₜ[S] x.2.2))).sum := by
  obtain ⟨m1, hx⟩ := TensorProduct.exists_multiset x
  let m2 (y : N ⊗[S] P) := (TensorProduct.exists_multiset y).choose
  use (m1.map (fun x ↦ ({x.1} : Multiset M).product (m2 x.2))).sum
  have hx' : x = (m1.map
      fun i ↦ (((m2 i.2).map (fun z ↦ z.1 ⊗ₜ[S] z.2)).map (fun y ↦ i.1 ⊗ₜ[R] y)).sum).sum := by
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
  rwa [Multiset.map_sum_map_sum m1 m2 (g := fun x y ↦ x ⊗ₜ[R] (y.1 ⊗ₜ[S] y.2))] at hx'

theorem exists_multiset_eq_sum_tmul_tmul' {R S M N P : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N] [AddCommMonoid P] [Module S P]
    [Algebra S R] [Module R N] [IsScalarTower S R N] (x : M ⊗[R] (N ⊗[S] P)) :
    ∃ (ξ : Multiset (M × N × P)), x = (ξ.map (fun x ↦ x.1 ⊗ₜ[R] (x.2.1 ⊗ₜ[S] x.2.2))).sum := by
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
  rwa [Multiset.map_sum_map_sum m1 m2 (g := fun x y ↦ x ⊗ₜ[R] (y.1 ⊗ₜ[S] y.2))] at hx'

variable {R' S' S'' : Type*} [CommSemiring R'] [Algebra R R'] [CommSemiring S'] [Algebra R' S']
  [CommSemiring S''] [Algebra R' S''] (φ : S' →ₐ[R'] S'') [Algebra R S'] [IsScalarTower R R' S']
  [Algebra R S''] [IsScalarTower R R' S'']

/-- An auxiliary linear equiv for the construction of the base change. -/
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

/-- The natural `S'`-linear isomorphism from the triple tensor product `S' ⊗[R'] (R' ⊗[R] M)`
  to `S' ⊗[R] M`. -/
def baseChangeEquiv : S' ⊗[R'] (R' ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M :=
  (AlgebraTensorModule.assoc R R' S' S' R' M).symm.trans baseChangeEquiv'

theorem baseChangeEquiv_rTensor_baseChangeEquivSymm (y : S' ⊗[R] M) :
    baseChangeEquiv
      ((LinearMap.rTensor (R' ⊗[R] M) φ.toLinearMap) ((baseChangeEquiv (R' := R')).symm y)) =
      LinearMap.rTensor M ((φ.restrictScalars R).toLinearMap) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s n => simp [baseChangeEquiv, baseChangeEquiv']

theorem baseChangeEquiv_rTensor_eq_baseChangeEquivSymm_rTensor (x : S' ⊗[R'] (R' ⊗[R] M)) :
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

def baseChangeEquiv_comp_lid_symm : R' ⊗[R] M ≃ₗ[R'] R' ⊗[R] M :=
  (TensorProduct.lid R' _).symm.trans baseChangeEquiv

theorem baseChangeEquiv_tmul_tmul (s' : S') (r' : R') (m : M) :
    baseChangeEquiv (s' ⊗ₜ[R'] (r' ⊗ₜ[R] m)) = (r' • s') ⊗ₜ[R] m := by
  simp [baseChangeEquiv, baseChangeEquiv']

end TensorProduct

namespace PolynomialLaw

open TensorProduct

universe u v

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

variable (R' : Type v) [CommSemiring R'] [Algebra R R']

/- **The definition of the base change of a polynomial law.**

We start from $R$-modules $M$ and $N$, and a polynomial law $f \in \mathscr P_R(M;N)$.
We wish to consider the base change $g$ of $f$ to an $R$-algebra $R'$, as a polynomial law in
$\mathscr P_S(R'\otimes_R M; R' \otimes_R N)$.
So we have to define, for any $R'$-algebra $S'$, a map
$g_{S'} \colon S' \otimes_{R'} (R' \otimes_R M) \to S' \otimes_{R'} (R' \otimes_R N)$.
Consider the isomorphism $\alpha_M \colon S' \otimes_{R'} (R'\otimes_R M)
\simeq S'\otimes_R M$ deduced from associativity of tensor product
and the $S'$-linear isomorphism $S'\otimes_{R'} R'\simeq S'$, and its analogue for $N$.
Up to the isomorphisms~$\alpha_M$ and~$\alpha_N$, the polynomial law $g$ evaluates on $S'$ as
the map $S' \otimes_R M \to S'\otimes_R N$ given by $f_{S'}$.
In other words, $g_{S'} = \alpha_N \circ f_{S'} \circ \alpha_M^{-1}$.

But writing the isomorphisms~$\alpha_M$ and~$\alpha_N$ requires to consider $S'$ as an $R$-algebra,
which is done by composition of the algebra morphisms $R\to R'\to S'$.

-/

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
    letI algRS' : Algebra R S' :=
      RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    haveI istRR'S' : @IsScalarTower R R' S' _ _ algRS'.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    letI algRS'' : Algebra R S'' :=
      RingHom.toAlgebra ((algebraMap R' S'').comp (algebraMap R R'))
    haveI istRR'S'' : @IsScalarTower R R' S'' _ _ algRS''.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    ext srm
    simp only [Function.comp_apply]
    rw [eq_comm, LinearEquiv.symm_apply_eq, baseChangeEquiv_rTensor_eq_baseChangeEquivSymm_rTensor,
      baseChangeEquiv_rTensor_baseChangeEquivSymm, ← f.isCompat_apply]

/-- The base change of a polynomial law, as a linear map. -/
noncomputable def baseChangeHom :
    (M →ₚₗ[R] N) →ₗ[R] RestrictScalars R R' ((R' ⊗[R] M) →ₚₗ[R'] (R' ⊗[R] N)) where
  toFun := baseChange R'
  map_add' f g := by
    change baseChange R' (f + g) = baseChange R' f + baseChange R' g
    ext S' _ _ srm
    simp [baseChange, add_toFun]
  map_smul' r f := by
    change baseChange R' (r • f) = algebraMap R R' r • baseChange R' f
    ext S' _ _ srm
    letI _ : Algebra R S' := RingHom.toAlgebra
      ((algebraMap R' S').comp (algebraMap R R'))
    have _ : IsScalarTower R R' S' :=
      IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    simp only [baseChange, smul_toFun, Pi.smul_apply, smul_def, algebraMap_smul]
    rw [← algebraMap_smul S' r (f.toFun S' (baseChangeEquiv srm)), ← algebraMap_smul S' r, map_smul]

theorem baseChangeEquiv_tmul_tmul {R' S' : Type*} [CommSemiring R'] [Algebra R R'] [CommSemiring S']
    [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] (s' : S') (r' : R') (m : M) :
    baseChangeEquiv (s' ⊗ₜ[R'] (r' ⊗ₜ[R] m)) = (r' • s') ⊗ₜ[R] m := by
  simp [baseChangeEquiv, baseChangeEquiv']

-- TODO: generalize to `toFun`, with `S'` in an arbitrary universe
theorem baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (m : ι → M) (r : ι → R')
    {S' : Type v} [CommSemiring S'] [Algebra R' S'] (s : ι → S') :
    (f.baseChange R').toFun' S' (∑ i, s i ⊗ₜ[R'] (r i ⊗ₜ[R] m i)) =
      (((coeff m) f).sum fun k n ↦  ((∏ i, s i ^ k i) ⊗ₜ[R'] ((∏ i, r i ^ k i) ⊗ₜ[R] n)))  := by
  simp only [baseChange, map_sum, baseChangeEquiv_tmul_tmul]
  rw [toFun_sum_tmul_eq_coeff_sum]
  rw [map_finsuppSum]
  apply congr_arg
  ext k n
  rw [LinearEquiv.symm_apply_eq]
  simp_rw [Algebra.smul_def, mul_pow]
  rw [Finset.prod_mul_distrib]
  simp_rw [← map_pow, ← map_prod, ← Algebra.smul_def]
  letI algRS' : Algebra R S' :=
    RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
  haveI istRR'S' : @IsScalarTower R R' S' _ _ algRS'.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
  rw [← baseChangeEquiv_tmul_tmul]

/-- The coefficients of a base change of a polynomial law, for `ι : Type`. -/
theorem coeff_baseChange' (f : M →ₚₗ[R] N) {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R') (k : ι →₀ ℕ) :
    coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k =
      (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k := by
  simp only [coeff_eq, toFun_eq_toFun', baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum]
  simp only [← LinearEquiv.eq_symm_apply, lid_symm_apply]
  simp only [map_finsuppSum, LinearMap.rTensor_tmul, MvPolynomial.lcoeff_apply]
  rw [Finsupp.sum_eq_single k, coeff_eq, toFun_eq_toFun']
  · congr
    convert MvPolynomial.coeff_monomial k k (1 : R') <;>
      simp [MvPolynomial.monomial_eq]
  · intro l _ hlk
    suffices MvPolynomial.coeff k (∏ i, MvPolynomial.X (R := R') i ^ l i) = 0 by
      simp [this]
    convert MvPolynomial.coeff_monomial k l (1 : R') <;>
      simp [MvPolynomial.monomial_eq, hlk]
  · simp

/-- The coefficients of the base change of a polynomial law. -/
theorem coeff_baseChange (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R') (k : ι →₀ ℕ) :
    coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k =
      (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k := by
  have : ∃ κ : Type, Nonempty (ι ≃ κ) := Small.equiv_small
  obtain ⟨κ, ⟨e⟩⟩ := this
  have : Fintype κ := Fintype.ofEquiv ι e
  have : DecidableEq κ := Classical.typeDecidableEq κ
  set n := m.comp e.symm with hn
  have hn' : m = n.comp e := by ext; simp [hn]
  set s := r.comp e.symm with hs
  have hs' : r = s.comp e := by ext; simp [hs]
  rw [hn', ← coeff_comp_equiv]
  set l := k.equivMapDomain e with hl
  have : ∏ i, r i ^ k i = ∏ i, s i ^ l i := by
    simp [hs, hl]
    rw [Fintype.prod_equiv e.symm]
    simp
  rw [this, ← coeff_baseChange', coeff_comp_equiv]
  congr
  ext; simp [hs']

theorem baseChange_toFun_smul_tmul_tmul_eq_coeff_sum (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (m : ι → M) (r : ι → R')
    {S' : Type*} [CommSemiring S'] [Algebra R' S'] (s : ι → S') :
    (f.baseChange R').toFun S' (∑ i, s i ⊗ₜ[R'] (r i ⊗ₜ[R] m i)) =
      (((coeff m) f).sum fun k n ↦  ((∏ i, s i ^ k i) ⊗ₜ[R'] ((∏ i, r i ^ k i) ⊗ₜ[R] n)))  := by
  have := exists_lift'' (R := R') (M := R' ⊗[R] M) (S := S') (t := 0) s
  obtain ⟨n, φ, _, t, _, ht⟩ := exists_lift'' (R := R') (M := R' ⊗[R] M) (S := S') 0 s
  set srm := ∑ i, s i ⊗ₜ[R'] (r i ⊗ₜ[R] m i) with hsrm
  set trm := ∑ i, t i ⊗ₜ[R'] (r i ⊗ₜ[R] m i) with htrm
  have : φ.toLinearMap.rTensor _ trm = srm := by
    unfold srm trm
    simp only [map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, ht]
  rw [← this, ← isCompat_apply, toFun_eq_toFun', baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum,
    map_finsuppSum]
  apply Finsupp.sum_congr
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_prod, map_pow, ht]

/-- The coefficients of a base change of a polynomial law, for `ι : Type`. -/
theorem coeff_baseChange_tmul' (f : M →ₚₗ[R] N) {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R') (k : ι →₀ ℕ) :
    coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k =
      (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k := by
  simp only [coeff_eq, toFun_eq_toFun', baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum,
    ← LinearEquiv.eq_symm_apply, lid_symm_apply]
  simp only [map_finsuppSum, LinearMap.rTensor_tmul, MvPolynomial.lcoeff_apply]
  rw [Finsupp.sum_eq_single k, coeff_eq, toFun_eq_toFun']
  · congr
    convert MvPolynomial.coeff_monomial k k (1 : R') <;>
      simp [MvPolynomial.monomial_eq]
  · intro l _ hlk
    suffices MvPolynomial.coeff k (∏ i, MvPolynomial.X (R := R') i ^ l i) = 0 by
      simp [this]
    convert MvPolynomial.coeff_monomial k l (1 : R') <;>
      simp [MvPolynomial.monomial_eq, hlk]
  · simp

/-- The coefficients of the base change of a polynomial law satisfy the formula
  `coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k = (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k`. -/
theorem coeff_baseChange_tmul (f : M →ₚₗ[R] N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → M) (r : ι → R') (k : ι →₀ ℕ) :
    coeff (fun i ↦ r i ⊗ₜ[R] m i) (f.baseChange R') k =
      (∏ i, r i ^ k i) ⊗ₜ[R] coeff m f k := by
  have : ∃ κ : Type, Nonempty (ι ≃ κ) := Small.equiv_small
  obtain ⟨κ, ⟨e⟩⟩ := this
  have : Fintype κ := Fintype.ofEquiv ι e
  have : DecidableEq κ := Classical.typeDecidableEq κ
  set n := m.comp e.symm with hn
  have hn' : m = n.comp e := by ext; simp [hn]
  set s := r.comp e.symm with hs
  have hs' : r = s.comp e := by ext; simp [hs]
  rw [hn', ← coeff_comp_equiv]
  set l := k.equivMapDomain e with hl
  have : ∏ i, r i ^ k i = ∏ i, s i ^ l i := by
    simp [hs, hl]
    rw [Fintype.prod_equiv e.symm]
    simp
  rw [this, ← coeff_baseChange_tmul', coeff_comp_equiv]
  congr
  ext; simp [hs']

variable {R'} in
theorem baseChange_apply (f : M →ₚₗ[R] N) {S' : Type v} [CommSemiring S']
    [algR'S' : Algebra R' S'] [algRS' : Algebra R S'] [istRR'S' : IsScalarTower R R' S']
    (srm : S' ⊗[R'] (R' ⊗[R] M)) :
    (f.baseChange R').toFun S' srm = baseChangeEquiv.symm (f.toFun S' (baseChangeEquiv srm)) := by
  obtain ⟨m, rfl⟩ := exists_multiset_eq_sum_tmul_tmul' srm
  classical
  rw [toFun_eq_toFun', Finset.sum_multiset_map_count]
  simp_rw [smul_tmul']
  rw [← Finset.sum_attach, ← Finset.sum_coe_sort_eq_attach,
    baseChange_toFun'_smul_tmul_tmul_eq_coeff_sum, map_sum]
  simp_rw [baseChangeEquiv_tmul_tmul]
  rw [f.toFun_sum_tmul_eq_coeff_sum, map_finsuppSum]
  congr
  ext k n
  rw [LinearEquiv.eq_symm_apply, baseChangeEquiv_tmul_tmul]
  simp_rw [smul_pow, Algebra.smul_def, Finset.prod_mul_distrib, ← map_prod]

theorem toFun_baseChangeEquiv_one_tmul (f : M →ₚₗ[R] N) (m : R' ⊗[R] M) :
    f.toFun R' (baseChangeEquiv ((1 : R') ⊗ₜ[R'] m)) =
      baseChangeEquiv ((1 : R') ⊗ₜ[R'] f.toFun R' m) := by simp [baseChangeEquiv_one_tmul]

/- If $f\in\mathscr P_R(M;N)$ is a polynomial law, then its ground map $f'$ is the
map $M\to N$ deduced from~$f_R$ after applying the $R$-linear isomorphisms
$e_M\colon R\otimes_R M\simeq M$ and $e_N \colon R\otimes_R N\simeq N$. That is,
$f' = e_N \circ f_R \circ e_M^{-1}$.

Now, if $g$ is the base change of $f$ to~$S$, we want to show that its ground is simply the
map $f_S\colon S\otimes_R M \to S\otimes_R N$.

By definition, $g' = e_N \circ g_S \circ e_M^{-1}$ and
$g_S = \alpha_N \circ f_S \circ \alpha_M^{-1}$, so that
$g' = (e_N \circ \alpha_N) \circ f_S \circ (e_M\circ\alpha_M)^{-1}$.

Note that $e_N\circ\alpha_N$ is the identity isomorphism from $S\otimes_R N$ to itself.

-/

theorem baseChange_ground (f : M →ₚₗ[R] N) :
    (f.baseChange R').ground = f.toFun R' := by
  ext m
  simp only [ground, Function.comp_apply, ← LinearEquiv.eq_symm_apply, lid_symm_apply]
  rw [← toFun_eq_toFun', baseChange_apply, toFun_baseChangeEquiv_one_tmul,
    LinearEquiv.symm_apply_apply]

end PolynomialLaw
