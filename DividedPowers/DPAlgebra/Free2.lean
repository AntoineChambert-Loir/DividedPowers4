/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.BaseChange
import DividedPowers.DPAlgebra.Graded.Basic
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.ForMathlib.RingTheory.TensorProduct.DirectLimit.FG
import DividedPowers.ForMathlib.Data.FinsetLemmas
import DividedPowers.Plurinomial
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import DividedPowers.ForMathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.TensorProduct.Free

noncomputable section

open DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

namespace DividedPowerAlgebra

-- PR to [Mathlib.RingTheory.DividedPowers.RatAlgebra]
def _root_.RatAlgebra.dividedPowersTop {R : Type*} [CommRing R] [Algebra ℚ R]  :
    DividedPowers (⊤ : Ideal R) :=
  have : DecidablePred fun x ↦ x ∈ (⊤ : Ideal R) := by
    simp only [Submodule.mem_top]
    infer_instance --instDecidableTrue
  RatAlgebra.dividedPowers ⊤

/-[Mathlib.Algebra.BigOperators.Ring.List, Mathlib.Algebra.Ring.CharZero,
 Mathlib.Algebra.Ring.Associated, Mathlib.Algebra.Ring.Action.Group] -/
theorem _root_.RingHom.map_inverse {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    [IsLocalHom f] (a : A) :
    f (Ring.inverse a) = Ring.inverse (f a) := by
  by_cases ha : IsUnit a
  · have : IsUnit (f a) := by simpa
    rw [← ha.unit_spec, Ring.inverse_unit, ha.unit_spec, ← this.unit_spec, Ring.inverse_unit]
    erw [← Units.coe_map_inv f.toMonoidHom ha.unit]
    exact Units.inv_unique rfl
  · rw [Ring.inverse_non_unit _ ha, map_zero]
    suffices ¬ IsUnit (f a) by
      rw [Ring.inverse_non_unit _ this]
    simpa

universe u v v₁ v₂ w uA uR uS uM

section Int

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤)

section MvPolynomial

open MvPolynomial Nat

open scoped factorial

def basisFun (n : ι →₀ ℕ) := monomial n (n.prod fun _ a ↦ 1/(a ! :  ℚ))

theorem basisFun_def (n : ι →₀ ℕ) :
    basisFun n = monomial n (n.prod fun _ a ↦ 1/(a ! :  ℚ)) := rfl

theorem basisFun_zero : basisFun (0 : ι →₀ ℕ) = 1 := by
  simp [basisFun]

theorem basisFun_single (i : ι) (n : ℕ) :
    basisFun (Finsupp.single i n) = (n ! : ℚ)⁻¹ • X i ^ n := by
  simp [basisFun, ← MvPolynomial.C_mul_X_pow_eq_monomial, smul_eq_C_mul]

open Finsupp in
theorem basisFun_mul (m n : ι →₀ ℕ) :
    basisFun m * basisFun n = (m.prod fun i a ↦ choose (a + n i) a) • basisFun (m + n) := by
  simp only [basisFun]
  rw [prod_of_support_subset (s := (m + n).support) m (support_mono le_self_add) _ (by simp),
    prod_of_support_subset (s := (m + n).support) m (support_mono le_self_add) _ (by simp),
    prod_of_support_subset (s := (m + n).support) n (support_mono le_add_self) _ (by simp),
    Finsupp.prod, monomial_mul, MvPolynomial.smul_monomial]
  congr 1
  simp only [nsmul_eq_mul, cast_prod, ← Finset.prod_mul_distrib, Finsupp.coe_add, Pi.add_apply]
  apply Finset.prod_congr rfl
  intro x hx
  field_simp
  norm_cast
  rw [← add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
  ring

theorem basisFun_add {m n : ι →₀ ℕ} (h : Disjoint m.support n.support) :
    basisFun (m + n) = basisFun m * basisFun n := by
  rw [basisFun_mul, eq_comm]
  convert one_smul ℕ _
  simp only [Finsupp.prod]
  apply Finset.prod_eq_one
  intro i hi
  suffices n i = 0 by simp [this]
  rw [← Finsupp.notMem_support_iff]
  exact Disjoint.notMem_of_mem_left_finset h hi

theorem basisFun_eq_prod (n : ι →₀ ℕ) :
    basisFun n = n.prod fun i a ↦ (a ! : ℚ)⁻¹ • X i ^ a := by
  induction n using Finsupp.induction with
  | zero => simp [basisFun_zero]
  | single_add i a n hn ha hind =>
    have : Disjoint (Finsupp.single i a).support n.support := by
      simp only [Finset.disjoint_right, Finsupp.mem_support_single]
      grind
    rw [basisFun_add this, Finsupp.prod_add_index_of_disjoint this, ← hind,
      basisFun_single, Finsupp.prod_single_index (by simp)]

theorem factorial_smul_basisFun_single (i : ι) (n : ℕ) :
    (n !) • basisFun (Finsupp.single i n) = X i ^ n := by
      rw [basisFun, X_pow_eq_monomial, smul_monomial, Finsupp.prod_single_index (by simp)]
      simp [Rat.mul_inv_cancel (n !) (by simp [Nat.factorial_ne_zero])]

def expMvPolynomial : Subalgebra ℤ (MvPolynomial ι ℚ) where
  carrier := Submodule.span ℤ (Set.range (basisFun (ι := ι)))
  mul_mem' {p} {q} hp hq := by
    induction hp using Submodule.span_induction generalizing q with
    | @mem p hp =>
      obtain ⟨m, rfl⟩ := hp
      induction hq using Submodule.span_induction with
      | @mem q hq =>
        obtain ⟨n, rfl⟩ := hq
        rw [basisFun_mul]
        apply Submodule.smul_mem
        exact Submodule.mem_span_of_mem (Set.mem_range_self (m + n))
      | zero => simp
      | @add x y hxmem hymem hx hy =>
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      | @smul a x hxmem hx =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ a hx
    | zero => simp
    | @add x y hxmem hymem hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ (hx hq) (hy hq)
    | smul a p hpmem hp =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ (hp hq)
  one_mem' := Submodule.mem_span_of_mem ⟨0, basisFun_zero⟩
  add_mem' {p} {q} hp hq := Submodule.add_mem _ hp hq
  zero_mem' := by simp
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply Submodule.smul_mem
    apply Submodule.mem_span_of_mem
    exact ⟨0, basisFun_zero⟩

variable (b : Basis ι ℤ M)

--TODO: rename
def morphism : DividedPowerAlgebra ℤ M →ₐ[ℤ] (MvPolynomial ι ℚ) :=
  DividedPowerAlgebra.lift RatAlgebra.dividedPowersTop
    (b.constr ℤ fun i ↦ (X i : MvPolynomial ι ℚ)) (by simp)

theorem morphism_dp (n : ℕ) (i : ι) :
    morphism b (dp ℤ n (b i)) = basisFun (Finsupp.single i n) := by
  rw [morphism, lift_apply_dp, RatAlgebra.dividedPowersTop,
    RatAlgebra.dpow_apply, if_pos (by simp)]
  rw [Basis.constr_basis, ← factorial_smul_basisFun_single, nsmul_eq_mul, ← mul_assoc,
    Ring.inverse_mul_cancel, one_mul]
  exact RingHom.isUnit_map C (by simp [Nat.factorial_ne_zero])

lemma range_morphism : AlgHom.range (morphism b) = expMvPolynomial :=  by
  ext p
  constructor
  · rintro ⟨n, rfl⟩
    induction n using DividedPowerAlgebra.induction_on with
    | h_C a => simp
    | h_add f g hf hg =>
      simp only [map_add]
      exact Subalgebra.add_mem _ hf hg
    | h_dp x n m hx =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
      apply Subalgebra.mul_mem _ hx
      have := b.mem_span m
      induction (b.mem_span m) using Submodule.span_induction
        generalizing n with
      | zero => rw [dp_null]; split_ifs <;> simp
      | mem m hm =>
        obtain ⟨i, rfl⟩ := hm
        rw [morphism_dp]
        apply Submodule.mem_span_of_mem
        exact ⟨_, rfl⟩
      | add x y hxmem hymem hx hy =>
        rw [dp_add, map_sum]
        apply Subalgebra.sum_mem
        intro uv huv
        rw [map_mul]
        exact Subalgebra.mul_mem expMvPolynomial (hx uv.1 hxmem) (hy uv.2 hymem)
      | smul a x hxmem hx =>
        rw [dp_smul, map_smul]
        exact Subalgebra.smul_mem expMvPolynomial (hx n hxmem) (a ^ n)
  · intro hp
    induction hp using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨n, rfl⟩ := hx
      rw [basisFun_eq_prod]
      apply Subalgebra.prod_mem
      intro i hi
      refine ⟨dp ℤ (n i) (b i), by simp [morphism_dp, basisFun_single]⟩
    | zero => simp
    | add _ _ _ _ hxmem hymem =>
      apply Subalgebra.add_mem _ hxmem hymem
    | smul a x hx hxmem =>
      exact Subalgebra.smul_mem (morphism b).range hxmem a

/-- The basis of `DividedPowerAlgebra ℤ M` associated with a basis of `M`. -/
noncomputable def Int.basis {M : Type v} [AddCommGroup M]
    {ι : Type*} (b : Basis ι ℤ M) :
    Basis (ι →₀ ℕ) ℤ (DividedPowerAlgebra ℤ M) := by
  classical
  -- this will be `⇑Int.basis` and `morphism_v` is reproved later
  set v : (n : ι →₀ ℕ) → DividedPowerAlgebra ℤ M :=
    fun n ↦ n.prod fun i a ↦ dp ℤ a (b i)
  have v_eq (n) : v n = n.prod fun i a ↦ dp ℤ a (b i) := rfl
  have morphism_v (n : ι →₀ ℕ) : morphism b (v n) = basisFun n := by
    simp only [v, basisFun, map_finsuppProd, MvPolynomial.monomial_eq, ← Finsupp.prod_mul]
    apply Finsupp.prod_congr
    simp [morphism_dp, basisFun_single, smul_eq_C_mul]
  apply Basis.mk (v := v)
  · simp only [LinearIndependent,
      ← LinearMap.ker_eq_bot (f := (Finsupp.linearCombination ℤ v)),  Submodule.eq_bot_iff]
    intro x hx
    ext n
    simp only [LinearMap.mem_ker, v] at hx
    replace hx := congr(morphism b $hx)
    replace hx := congrArg (fun p ↦ p.coeff n) hx
    simp only [map_zero, MvPolynomial.coeff_zero, Finsupp.linearCombination_apply, map_finsuppSum] at hx
    rw [Finsupp.sum, MvPolynomial.coeff_sum] at hx
    rw [Finset.sum_eq_single n] at hx
    · rw [map_smul, coeff_smul, ← v_eq, morphism_v,
      basisFun, coeff_monomial, if_pos rfl] at hx
      simp only [one_div, zsmul_eq_mul, _root_.mul_eq_zero, Int.cast_eq_zero] at hx
      apply Or.resolve_right hx
      rw [← ne_eq, Finsupp.prod_ne_zero_iff]
      intro i hi
      simp [Nat.factorial_ne_zero]
    · intro m hm hmn
      rw [map_smul, coeff_smul, ← v_eq, morphism_v,
        basisFun, coeff_monomial, if_neg hmn, smul_zero]
    · intro hn
      simp only [Finsupp.notMem_support_iff] at hn
      simp [hn]
  · apply le_of_eq
    symm
    simp only [v]
    rw [← submodule_span_prod_dp_eq_top b.span_eq]

lemma injective_morphism : Function.Injective (morphism b) := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro p
  simp only [RingHom.mem_ker, Submodule.mem_bot]
  intro hp
  rw [← (Int.basis b).linearCombination_repr p] at hp
  rw [← AlgHom.coe_toLinearMap, LinearMap.map_finsupp_linearCombination] at hp
  simp only [AlgHom.coe_toLinearMap] at hp
  have : morphism b ∘ Int.basis b = basisFun := by
    ext1 n
    simp only [Int.basis, Basis.coe_mk, Function.comp_apply, basisFun,
      map_finsuppProd, MvPolynomial.monomial_eq, ← Finsupp.prod_mul]
    apply Finsupp.prod_congr
    simp [morphism_dp, basisFun_single, smul_eq_C_mul]
  rw [this, Finsupp.linearCombination_apply] at hp
  rw [← ((Int.basis b).repr).map_eq_zero_iff]
  set v := (Int.basis b).repr p
  ext n
  replace hp := congrArg (fun p ↦ p.coeff n) hp
  simp only [coeff_zero, Finsupp.sum, coeff_sum, coeff_smul] at hp
  rw [Finset.sum_eq_single n] at hp
  · classical
    rw [basisFun, coeff_monomial, if_pos rfl] at hp
    simp only [one_div, zsmul_eq_mul, _root_.mul_eq_zero, Int.cast_eq_zero] at hp
    apply Or.resolve_right hp
    rw [← ne_eq, Finsupp.prod_ne_zero_iff]
    intro i hi
    simp [Nat.factorial_ne_zero]
  · intro b _ hb
    classical
    rw [basisFun, coeff_monomial, if_neg hb, smul_zero]
  · intro hn
    rw [Finsupp.notMem_support_iff] at hn
    simp [hn]


-- NOTE: Perhaps generalize Int.basis_grade to [CharZero R] [IsDomain R]

section

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {ι : Type*} [DecidableEq ι] (G : ι → Submodule R M)
    [DirectSum.Decomposition G]
    {α : Type*} (b : Basis α R M)

/-- A basis of a module is homogeneous if each of its members
belongs to one submodule of the decomposition. -/
def DirectSum.basis_isHomogeneous : Prop :=
  ∀ a, ∃ i, b a ∈ G i

theorem DirectSum.mem_iff_component_eq_zero (x : M) (i : ι) :
    x ∈ G i ↔ ∀ j ≠ i, DirectSum.component R ι (fun i ↦ G i) j
      (DirectSum.decomposeLinearEquiv G x) = 0 := by
  constructor
  · intro h j hji
    simp only [DirectSum.decomposeLinearEquiv_apply]
    rw [DirectSum.decompose_of_mem G h, ← DirectSum.lof_eq_of R,
      DirectSum.component.of, dif_neg (Ne.symm hji)]
  · intro h
    classical
    rw [← DirectSum.sum_support_decompose G x]
    apply Submodule.sum_mem
    intro j hj
    by_cases hji : j = i
    · subst hji
      exact Submodule.coe_mem (((DirectSum.decompose G) x) j)
    · specialize h j hji
      convert Submodule.zero_mem _
      rwa [← Subtype.coe_inj, Submodule.coe_zero] at h

theorem DirectSum.mem_iff_eq_component (x : M) (i : ι) :
    x ∈ G i ↔ x = DirectSum.component R ι (fun i ↦ G i) i
      (DirectSum.decomposeLinearEquiv G x) := by
  constructor
  · intro h
    simp only [DirectSum.decomposeLinearEquiv_apply]
    rw [DirectSum.decompose_of_mem G h, ← DirectSum.lof_eq_of R,
      DirectSum.component.of, dif_pos rfl]
  · intro h
    rw [h]
    apply Submodule.coe_mem

variable {G b} in
theorem mem_iff_basis_mem_of_mem_support
    (h : DirectSum.basis_isHomogeneous G b) {i : ι} {x : M} :
    x ∈ G i ↔ ∀ a ∈ (b.repr x).support, b a ∈ G i := by
  constructor
  · intro hx a ha
    obtain ⟨j, hj⟩ :=  h a
    suffices j = i by simpa [← this]
    simp only [Finsupp.mem_support_iff] at ha
    contrapose ha
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
      DirectSum.mem_iff_component_eq_zero] at hx
    replace hx := congr(b.coord a $(hx j ha))
    simp only [ZeroMemClass.coe_zero, map_zero, Basis.coord_apply] at hx
    rw [← hx]
    simp only [map_sum, map_smul, DirectSum.decomposeLinearEquiv_apply,
      AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · rw [eq_comm]
      convert mul_one _
      rw [DirectSum.decompose_of_mem G hj, ← DirectSum.lof_eq_of R,
        DirectSum.component.of, dif_pos rfl]
      simp
    · intro a' ha' haa'
      convert mul_zero _
      obtain ⟨j', hj'⟩ := h a'
      rw [DirectSum.decompose_of_mem G hj', ← DirectSum.lof_eq_of R,
      DirectSum.component.of]
      by_cases hj'j : j' = j
      · rw [dif_pos hj'j]
        subst hj'j
        change (b.repr (b a')) a = 0
        simp [Finsupp.single_eq_of_ne (Ne.symm haa')]
      · rw [dif_neg hj'j]
        simp
    · intro ha
      simp only [Finsupp.mem_support_iff, ne_eq, not_not] at ha
      simp [ha]
  · intro h
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Submodule.sum_smul_mem (G i) (⇑(b.repr x)) h

variable {G b} in
/-- A homogeneous basis gives rise to bases of each submodule of the decomposition. -/
def DirectSum.Decomposition.basis (h : DirectSum.basis_isHomogeneous G b) (i : ι) :
    Basis {a | b a ∈ G i} R (G i) := by
  let v (a : {a : α | b a ∈ G i}) : G i := ⟨b a.val, a.prop⟩
  apply Basis.mk (v := v)
  · apply LinearIndependent.of_comp (f := (G i).subtype)
    exact LinearIndepOn.mono b.linearIndependent.linearIndepOn
      (Set.subset_univ _)
  classical
  rintro ⟨x,  hx⟩ -
  rw [mem_iff_basis_mem_of_mem_support h] at hx
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use (b.repr x).subtypeDomain _
  apply (G i).injective_subtype
  simp only [Set.coe_setOf, Set.mem_setOf_eq, map_finsuppSum, map_smul, Submodule.subtype_apply, v]
  simp only [Finsupp.sum]
  have : ((b.repr x).subtypeDomain (fun x ↦ b x ∈ G i)).support =
    Finset.subtype _ (b.repr x).support := by simp
  rw [this]
  rw [Finset.sum_congr (s₂ := Finset.subtype (fun x ↦ b x ∈ G i) (b.repr x).support)
    (g := fun u ↦ (b.repr x) u • b u) rfl (by simp)]
  rw [Finset.sum_subtype_of_mem (fun u ↦ b.repr x u • b u) hx]
  conv_rhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum]

end

theorem Int.basis_mem_grade (n : ι →₀ ℕ) :
    Int.basis b n ∈ grade ℤ M (n.sum fun _ a ↦ a) := by
  rw [mem_grade_iff]
  use n.prod fun i a ↦ X (a, b i)
  constructor
  · simp only [mem_weightedHomogeneousSubmodule]
    induction n using Finsupp.induction with
    | zero => simp [isWeightedHomogeneous_one]
    | single_add i a n hin ha hind =>
      classical
      -- already done somewhere, make a lemma?
      have h : Disjoint (Finsupp.single i a).support n.support := by
        simp only [Finset.disjoint_right, Finsupp.mem_support_single]
        grind
      rw [Finsupp.prod_add_index_of_disjoint h,
        Finsupp.sum_add_index_of_disjoint h, Finsupp.sum_single_index]
      convert IsWeightedHomogeneous.mul _ hind
      · suffices (Finsupp.single i a).prod
            (fun i a ↦ (X (a, b i) : MvPolynomial (ℕ × M) ℤ)) = X (a, b i) by
          simp [this, isWeightedHomogeneous_X]
        -- `Finsupp.prod_single_index` doesn't work because
        -- it allows the remaining parameter to be `0`.
        -- one should add a lemma that takes this hypothesis
        rw [Finsupp.prod, Finset.prod_eq_single i]
        · simp
        · intro j hj hj'
          simp only [Finsupp.mem_support_iff, ne_eq] at hj
          simp [Finsupp.single_eq_of_ne hj'] at hj
        · intro hi
          refine (ha ?_).elim
          simpa using hi
      · simp
  simp only [map_finsuppProd, basis, Basis.coe_mk, mk_X]

lemma Int.basis_mem_grade_iff_eq (n : ι →₀ ℕ) (d : ℕ) :
    Int.basis b n ∈ grade ℤ M d ↔ (n.sum fun _ a ↦ a) = d := by
  by_cases h : (n.sum fun _ a ↦ a) = d
  · simp only [← h, iff_true]
    exact basis_mem_grade b n
  · simp only [h, iff_false]
    intro h'
    apply (Int.basis b).ne_zero n
    rw [← DirectSum.decompose_of_mem_same (fun d ↦ grade ℤ M d) h',
      DirectSum.decompose_of_mem_ne (fun d ↦ grade ℤ M d) (basis_mem_grade b n) h]

/-- The basis of the nth graded part of `DividedPowerAlgebra ℤ M` associated with a basis of `M`. -/
noncomputable def Int.basis_grade (d : ℕ) :
    Basis {n : ι →₀ ℕ | (n.sum fun _ a ↦ a) = d} ℤ (grade ℤ M d) := by
  -- take the part of `Int.basis` that has degree `d `.
  let e : {n : ι →₀ ℕ | Int.basis b n  ∈ grade ℤ M d} ≃
      {n : ι →₀ ℕ | (n.sum fun _ a ↦ a) = d} := by
    apply Equiv.setCongr
    ext n
    simp [Int.basis_mem_grade_iff_eq]
  refine Basis.reindex ?_ e
  apply DirectSum.Decomposition.basis (b := Int.basis b) (G := fun d ↦ grade ℤ M d)
  unfold DirectSum.basis_isHomogeneous
  intro n
  refine ⟨_, basis_mem_grade b n⟩

theorem Int.coe_basis_grade (n : ι →₀ ℕ) (d : ℕ) (hn : (n.sum fun _ a ↦ a) = d) :
    Int.basis_grade b d ⟨n, hn⟩ = Int.basis b n := by
  simp [basis_grade, DirectSum.Decomposition.basis, Equiv.setCongr, Equiv.subtypeEquivProp]

end MvPolynomial

end Int

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : M) {n : ℕ}
  (N : Type w) [AddCommGroup N] [Module R N]

namespace Free

open Module Module.Free TensorProduct

variable [Module.Free R M]

-- Prop. A2.1
noncomputable example :
    R ⊗[ℤ] DividedPowerAlgebra ℤ M ≃ₐ[R] DividedPowerAlgebra R (R ⊗[ℤ] M) :=
  DividedPowerAlgebra.dpScalarExtensionEquiv ℤ R M

def baseChange_equiv' [Module.Free R M] :
    R ⊗[ℤ] (ChooseBasisIndex R M →₀ ℤ) ≃ₗ[R] M :=
  (finsuppScalarRight' ℤ R (ChooseBasisIndex R M) R).trans
    ((Module.Free.chooseBasis R M).repr).symm

def baseChange_equiv :
    R ⊗[ℤ] DividedPowerAlgebra ℤ (ChooseBasisIndex R M →₀ ℤ) ≃ₐ[R]
      DividedPowerAlgebra R M :=
  (dpScalarExtensionEquiv ℤ R (ChooseBasisIndex R M →₀ ℤ)).trans
    (LinearEquiv.lift (baseChange_equiv' R M))

instance : Free ℤ (DividedPowerAlgebra ℤ (ChooseBasisIndex R M →₀ ℤ)) :=
  Module.Free.of_basis (Int.basis (chooseBasis ℤ (ChooseBasisIndex R M →₀ ℤ)))

theorem free : Module.Free R (DividedPowerAlgebra R M) :=
  Module.Free.of_equiv (baseChange_equiv R M).toLinearEquiv

end Free

end DividedPowerAlgebra
