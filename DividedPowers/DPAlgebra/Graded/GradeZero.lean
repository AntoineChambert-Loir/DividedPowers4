/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.Graded.Basic
import DividedPowers.ForMathlib.RingTheory.AugmentationIdeal

universe u v

noncomputable section

-- TODO : move to MvPolynomial file
namespace MvPolynomial

open Ideal.Quotient

theorem mkₐ_eq_aeval {C : Type*} [CommRing C] {D : Type*} (I : Ideal (MvPolynomial D C)) :
    Ideal.Quotient.mkₐ C I = aeval fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d
  simp only [mkₐ_eq_mk, aeval_X]

theorem mk_eq_eval₂ {C : Type*} [CommRing C] {D : Type*} (I : Ideal (MvPolynomial D C)) :
    (Ideal.Quotient.mk I).toFun =
      eval₂ (algebraMap C (MvPolynomial D C ⧸ I)) fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← mkₐ_eq_mk C, mkₐ_eq_aeval, aeval_X]
  rfl


end MvPolynomial

namespace DividedPowerAlgebra

open DirectSum Finset Function Ideal Ideal.Quotient MvPolynomial RingEquiv RingQuot TrivSqZeroExt

section CommSemiring

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

variable [DecidableEq R]

section GradeZero
/-- The natural map from `DividedPowerAlgebra R M` to `R`. -/
def algebraMapInv : DividedPowerAlgebra R M →ₐ[R] R :=
  lift (dividedPowersBot R) (0 : M →ₗ[R] R)
    (fun _ => by simp only [LinearMap.zero_apply, mem_bot])

theorem algebraMapInv_mk (f : MvPolynomial (ℕ × M) R) :
    algebraMapInv R M (mk f) = aeval (fun nm : ℕ × M => ite (0 < nm.1) (0 : R) 1) f := by
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  ext ⟨n, m⟩
  simp only [algebraMapInv, AlgHom.comp_apply, aeval_X]
  by_cases hn : 0 < n
  · simp only [if_pos hn, lift_apply, LinearMap.zero_apply, aeval_X]
    rw [DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]
  · rw [if_neg hn]
    rw [not_lt, le_zero_iff] at hn
    simp only [hn, lift_apply, LinearMap.zero_apply, aeval_X,
      DividedPowers.dpow_zero _ (mem_bot.mpr rfl)]

theorem algebraMapInv_dp (n : ℕ) (m : M) :
    algebraMapInv R M (dp R n m) = if n = 0 then 1 else 0 := by
  rw [show dp R n m = mk (X (n, m)) by rfl, algebraMapInv_mk]
  simp only [aeval_X]
  by_cases hn : n = 0
  · rw [if_pos hn, if_neg (Eq.not_gt hn)]
  · rw [if_neg hn, if_pos (Nat.zero_lt_of_ne_zero hn)]

theorem proj'_zero_comp_algebraMap [DecidableEq M] (x : R) :
  ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val =
    (algebraMap R (DividedPowerAlgebra R M)) x := by
  simp only [proj', GradedAlgebra.proj', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    Algebra.algebraMap_eq_smul_one, decompose_smul, decompose_one]
  rfl

/-- `algebraMapInv R M` is a left inverse to `algebraMap R (DividedPowerAlgebra R M`. -/
theorem algebraMap_leftInverse :
    Function.LeftInverse (algebraMapInv R M) (algebraMap R (DividedPowerAlgebra R M)) := fun m => by
  simp only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply]

@[simp] theorem algebraMap_inj (x y : R) :
    (algebraMap R (DividedPowerAlgebra R M) x = algebraMap R (DividedPowerAlgebra R M) y) ↔ x = y :=
  (algebraMap_leftInverse R M).injective.eq_iff

@[simp] theorem algebraMap_eq_zero_iff (x : R) :
    algebraMap R (DividedPowerAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _ _).injective

@[simp] theorem algebraMap_eq_one_iff (x : R) :
    algebraMap R (DividedPowerAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _ _).injective

theorem algebraMap_right_inv_of_degree_zero [DecidableEq M] (x : grade R M 0) :
    (algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x) = x := by
  obtain ⟨p, hp0, hpx⟩ := (mem_grade_iff' _).mp x.2
  suffices ∃ (a : R), p.val = C a by
    obtain ⟨a, ha⟩ := this
    simp only [← hpx, ha, mk_C, AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply]
  use constantCoeff p.val
  ext exp
  simp only [coeff_C]
  split_ifs with hexp
  . rw [← hexp, constantCoeff_eq]
  . simp only [IsWeightedHomogeneous] at hp0
    by_contra h
    rw [eq_comm, ← Finsupp.support_eq_empty] at hexp
    obtain  ⟨nm, hnm⟩ := nonempty_of_ne_empty hexp
    specialize hp0 h
    simp only [Finsupp.weight, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, Finsupp.sum,
      sum_eq_zero_iff] at hp0
    specialize hp0 nm hnm
    simp only [smul_eq_mul, mul_eq_zero] at hp0
    rcases hp0 with hnm0 | hnm0
    . simp only [Finsupp.mem_support_iff] at hnm
      exact hnm hnm0
    . apply lt_irrefl 0
      nth_rewrite 2 [← hnm0]
      apply MvPolynomial.mem_supported.mp p.prop
      simp only [mem_coe, mem_vars, Finsupp.mem_support_iff, ne_eq, mem_support_iff, exists_prop]
      simp only [Finsupp.mem_support_iff] at hnm
      exact ⟨exp, h, hnm⟩

end GradeZero

end CommSemiring

section CommRing

variable (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M]

variable [DecidableEq R] --[DecidableEq M]

section GradeZero
/-- The augmentation ideal in the `DividedPowerAlgebra R M`, that is, the kernel of the map
  `algebraMapInv R M`.  -/
def augIdeal : (Ideal (DividedPowerAlgebra R M) : Type (max u v)) :=
  RingHom.ker (algebraMapInv R M)

theorem mem_augIdeal_iff (f : DividedPowerAlgebra R M) :
    f ∈ augIdeal R M ↔ algebraMapInv R M f = 0 := by
  rw [augIdeal, RingHom.mem_ker]

instance : DecidablePred (fun x ↦ x ∈ augIdeal R M) := by
    intro x
    simp only [mem_augIdeal_iff]
    infer_instance

/-- For `Nontrivial R`, `dp R n m` is contained in the augmentation ideal iff `0 < n`. -/
theorem dp_mem_augIdeal_iff [Nontrivial R] (n : ℕ) (m : M) :
    dp R n m ∈ augIdeal R M ↔ 0 < n := by
  erw [mem_augIdeal_iff, dp, algebraMapInv_mk, aeval_X]
  simp only [ite_eq_left_iff, not_not, one_ne_zero, imp_false]

/-- `dp R n m` is contained in the augmentation ideal for `0 < n` -/
theorem dp_mem_augIdeal {n : ℕ} (hn : 0 < n) (m : M) :
    dp R n m ∈ augIdeal R M := by
  erw [mem_augIdeal_iff, dp, algebraMapInv_mk, aeval_X, if_pos hn]

/-- The image of ι is contained in the augmentation ideal -/
theorem ι_mem_augIdeal (m : M) : ι R M m ∈ augIdeal R M := by
  have : (mkAlgHom R (Rel R M)) (X (1, m)) = mk (X (1, m)) := rfl
  simp only [this, mem_augIdeal_iff, ι_def, dp, algebraMapInv_mk, aeval_X, zero_lt_one, ite_true]

/-- The lift of the algebra morphism `algebraMapInv R M` to the quotient by the augmentation
  ideal. -/
def kerLiftAlg_algebraMapInv :
    (DividedPowerAlgebra R M ⧸ augIdeal R M) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (algebraMapInv R M) (fun a ↦ by simp only [mem_augIdeal_iff, imp_self])

-- probably useless
/- def algebraMap_mod_augIdeal :
    R →+* (DividedPowerAlgebra R M ⧸ augIdeal R M) :=
  algebraMap R (DividedPowerAlgebra R M ⧸ augIdeal R M)

  def algebraMap_comp_kerLiftAlg :
    DividedPowerAlgebra R M ⧸ RingHom.ker (algebraMapInv R M) →+* DividedPowerAlgebra R M :=
  (algebraMap R (DividedPowerAlgebra R M)).comp (kerLiftAlg_algebraMapInv R M).toRingHom

lemma augIdeal_isAugmentationIdeal' :
    Function.LeftInverse (Ideal.Quotient.mk (augIdeal R M))
      (algebraMap_comp_kerLiftAlg R M) := fun r ↦ by
  dsimp only [algebraMap_comp_kerLiftAlg]
  rw [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.mk_algebraMap]
  apply kerLiftAlg_rightInverse
 -/

lemma kerLiftAlg_leftInverse :
    Function.LeftInverse (kerLiftAlg_algebraMapInv R M) (algebraMap R _) :=
  AlgHom.commutes (kerLiftAlg (algebraMapInv R M))

lemma kerLiftAlg_rightInverse :
    Function.RightInverse (kerLiftAlg_algebraMapInv R M) (algebraMap R _) :=
  Function.rightInverse_of_injective_of_leftInverse
    (RingHom.kerLift_injective _) (kerLiftAlg_leftInverse _ _)

-- Q : if algebra map has a section, is the kernel an augmentation ideal?
theorem coeff_zero_of_mem_augIdeal {f : MvPolynomial (ℕ × M) R}
    (hf : f ∈ supported R {nm : ℕ × M | 0 < nm.fst}) (hf0 : mk f ∈ augIdeal R M) :
    coeff 0 f = 0 := by
  simp only [augIdeal, AlgHom.toRingHom_eq_coe, RingHom.mem_ker, RingHom.coe_coe] at hf0
  rw [← hf0, algebraMapInv_mk R M, eq_comm]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Finset.sum_eq_single 0]
  . simp only [monomial_zero', aeval_C, Algebra.id.map_eq_id, RingHom.id_apply]
  · intro b hb hb0
    rw [aeval_monomial, Algebra.id.map_eq_id, RingHom.id_apply]
    convert mul_zero (coeff b f)
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hb0
    rw [Finsupp.prod]
    apply Finset.prod_eq_zero hi
    have hi' : 0 < i.fst := by
      apply mem_supported.mp hf
      rw [Finset.mem_coe, mem_vars]
      exact ⟨b, ⟨hb, hi⟩⟩
    rw [if_pos hi']
    exact zero_pow (Finsupp.mem_support_iff.mp hi)
  · intro hf'
    rw [monomial_zero', aeval_C, Algebra.id.map_eq_id, RingHom.id_apply, ←
      not_mem_support_iff.mp hf']

theorem augIdeal_eq_span :
    augIdeal R M = span (Set.image2 (dp R) {n : ℕ | 0 < n} Set.univ) := by
  classical
  apply le_antisymm
  · intro f0 hf0
    obtain ⟨⟨f, hf⟩, rfl⟩ := surjective_of_supported R M f0
    have hf0' : coeff 0 f = 0 := coeff_zero_of_mem_augIdeal R M hf hf0
    simp only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply] at hf0 ⊢
    rw [f.as_sum, map_sum]
    refine Ideal.sum_mem _ ?_
    intro c hc
    rw [monomial_eq, Finsupp.prod]
    simp only [_root_.map_mul]
    refine' mul_mem_left _ _ _
    suffices supp_ss : ↑c.support ⊆ {nm : ℕ × M | 0 < nm.fst} by
      by_cases hc0 : c.support.Nonempty
      · obtain ⟨⟨n, m⟩, hnm⟩ := hc0
        rw [Finset.prod_eq_mul_prod_diff_singleton hnm]
        simp only [_root_.map_mul, map_pow]
        apply mul_mem_right _ _
          (pow_mem_of_mem _ _ _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hnm)))
        exact subset_span ⟨n, by simpa only [Set.mem_setOf_eq] using supp_ss hnm, m, trivial , rfl⟩
      · -- case where c.support is empty : c = 0 ; contradiction
        rw [not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hc0
        rw [hc0] at hc
        exact absurd hf0' (mem_support_iff.mp hc)
    · -- proof of supp_ss
      intro nm hnm
      apply mem_supported.mp hf
      simp only [mem_vars, mem_coe, mem_support_iff, ne_eq, Finsupp.mem_support_iff, exists_prop]
      rw [mem_coe, Finsupp.mem_support_iff] at hnm
      exact ⟨c, ⟨mem_support_iff.mp hc, hnm⟩⟩
  · rw [span_le]
    intro f
    simp only [Set.mem_image2, Set.mem_setOf_eq, Set.mem_univ, true_and, exists_and_left,
      SetLike.mem_coe, forall_exists_index, and_imp]
    intro n hn m hf
    rw [← hf, mem_augIdeal_iff, algebraMapInv, lift_apply_dp]
    simp_rw [LinearMap.zero_apply]
    rw [DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]

theorem right_inv' [DecidableEq M] (x : R) :
    (algebraMapInv R M) ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val = x := by
  rw [proj'_zero_comp_algebraMap]
  exact algebraMap_leftInverse R M x

theorem left_inv' [DecidableEq M] (x : grade R M 0) :
    (proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.val) = x := by
  ext
  simp only [proj', GradedAlgebra.proj', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  conv_rhs => rw [← DirectSum.decompose_of_mem_same _ x.2]
  simp only [algebraMap_right_inv_of_degree_zero R M x, decompose_coe, of_eq_same]

theorem lift_augIdeal_le {A : Type*} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) :
    Ideal.map (lift hI φ hφ) (augIdeal R M) ≤ I := by
  simp only [augIdeal_eq_span, Ideal.map_span, Ideal.span_le, SetLike.mem_coe]
  rintro y ⟨x, ⟨n, hn, m, _, rfl⟩, rfl⟩
  simp only [lift_apply_dp]
  refine hI.dpow_mem (ne_of_gt hn) (hφ m)

theorem lift_mem_of_mem_augIdeal {A : Type*} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : DividedPowerAlgebra R M)
    (hx : x ∈ augIdeal R M) : lift hI φ hφ x ∈ I :=
  (lift_augIdeal_le R M hI φ hφ) (mem_map_of_mem _ hx)

section

variable (S : Type*) [CommRing S] [Algebra R S]
  {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  (f : M →ₗ[R] N)
  [DecidableEq S]

theorem LinearMap.augIdeal_map_lift_le :
    (augIdeal R M).map (LinearMap.lift S f) ≤ augIdeal S N := by
  simp only [augIdeal_eq_span, Ideal.map_span, Ideal.span_le, SetLike.mem_coe]
  rintro y ⟨x, ⟨n, hn, m, _, rfl⟩, rfl⟩
  simp only [LinearMap.lift_apply_dp]
  apply Ideal.subset_span
  exact ⟨ n, hn, f m, Set.mem_univ _, rfl⟩

variable {R M f} in
theorem LinearMap.lift_mem_augIdeal_iff {x : DividedPowerAlgebra R M} :
    LinearMap.lift R f x ∈ augIdeal R N ↔ x ∈ augIdeal R M := by
  constructor
  · intro hx
    rw [mem_augIdeal_iff]
    set r := algebraMapInv R M x
    set y := x - algebraMap R _ r
    have hy : y ∈ augIdeal R M := by
      simp [y, mem_augIdeal_iff, r]
    have hx' : x = y + algebraMap R _ r := by simp [y]
    simp only [hx', map_add, AlgHom.commutes] at hx
    suffices LinearMap.lift R f y ∈ augIdeal R N by
      rw [mem_augIdeal_iff] at this
      rw [mem_augIdeal_iff, map_add, this, zero_add] at hx
      simpa only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply] using hx
    exact LinearMap.augIdeal_map_lift_le R M R f (Ideal.mem_map_of_mem _ hy)
  · intro hx
    exact LinearMap.augIdeal_map_lift_le R M R f (Ideal.mem_map_of_mem _ hx)

theorem LinearMap.augIdeal_map_lift
    (hf : Function.Surjective f) :
    (augIdeal R M).map (LinearMap.lift R f) = augIdeal R N := by
  apply le_antisymm
  · exact LinearMap.augIdeal_map_lift_le R M R f
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.lift_surjective_of hf x
    apply Ideal.mem_map_of_mem
    rwa [LinearMap.lift_mem_augIdeal_iff] at hx

end

/-- The restriction of `algebraMapInv R M ` to `grade R M 0`, as a ring isomorphism from
  `grade R M 0` to `R`. -/
noncomputable def ringEquivDegreeZero [DecidableEq M] : RingEquiv (grade R M 0) R where
  toFun x      := algebraMapInv R M x.1
  invFun       := proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)
  left_inv     := left_inv' R M
  right_inv    := right_inv' R M
  map_mul' x y := by rw [← _root_.map_mul]; rfl
  map_add' x y := by rw [← _root_.map_add]; rfl

/-- The natural ring homomorphism `RingHom (DividedPowerAlgebra R M) →+* R` obtained as the
  composition `(ringEquivDegreeZero R M).toFun ∘ proj' R M 0`. -/
def proj0RingHom [DecidableEq M] : RingHom (DividedPowerAlgebra R M) R where
  toFun := (ringEquivDegreeZero R M).toFun ∘ proj' R M 0
  map_one' := by
    simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, coe_toEquiv, comp_apply, proj'_zero_one R M]
    exact (ringEquivDegreeZero R M).map_one
  map_mul' x y := by
    simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, coe_toEquiv, comp_apply]
    rw [← _root_.map_mul, proj'_zero_mul]
  map_zero' := by
    simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, coe_toEquiv, comp_apply, map_zero]
  map_add' := by
    simp only [toEquiv_eq_coe, Equiv.toFun_as_coe, coe_toEquiv, comp_apply, map_add, forall_const]

omit [DecidableEq R] in
theorem algebraMap_mem_grade_zero  (r : R) :
    (algebraMap R (DividedPowerAlgebra R M)) r ∈ grade R M 0 := by
  rw [mem_grade_iff]
  use C r
  constructor
  · simp only [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_C Prod.fst r
  · rw [mk_C]

/-- The degree 0 part of `DividedPowerAlgebra R M` as an `R`-subalgebra. -/
def gradeZeroSubalgebra [DecidableEq M] : Subalgebra R (DividedPowerAlgebra R M) where
  carrier         := grade R M 0
  add_mem'        := add_mem
  mul_mem' ha hb  := mul_mem R M ha hb
  algebraMap_mem' := algebraMap_mem_grade_zero  R M

theorem gradeZeroSubalgebra_toSubmodule [DecidableEq M] :
    Subalgebra.toSubmodule (gradeZeroSubalgebra R M) = grade R M 0 := rfl

/-- `gradeZeroSubalgebra R M ` is the smallest `R`-subalgebra of `DividedPowerAlgebra R M`, i.e.,
  the image of `algebraMap R DividedPowerAlgebra R M`. -/
theorem gradeZeroSubalgebra_eq_bot [DecidableEq M] : gradeZeroSubalgebra R M = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Algebra.mem_bot]
  convert Set.mem_range_self ((algebraMapInv R M) p)
  exact (algebraMap_right_inv_of_degree_zero R M ⟨p, hp⟩).symm

/-- `augIdeal R M` is an augmentation ideal of the `R`-algebra `DividedPowerAlgebra R M`. -/
theorem isCompl_augIdeal : Ideal.IsAugmentation R (augIdeal R M) := by
  apply IsCompl.mk
  · rw [Submodule.disjoint_def]
    intro x
    simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot]
    rintro ⟨r, rfl⟩
    simp only [Submodule.restrictScalars_mem, mem_augIdeal_iff, AlgHom.commutes,
      Algebra.id.map_eq_id, RingHom.id_apply]
    rintro rfl
    rw [map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    simp only [Submodule.mem_sup, Subalgebra.mem_toSubmodule, Submodule.restrictScalars_mem]
    refine ⟨algebraMap R _ (algebraMapInv R M p), ?_, _, ?_, add_sub_cancel _ p⟩
    · rw [Algebra.mem_bot]
      exact Set.mem_range_self ((algebraMapInv R M) p)
    · simp only [mem_augIdeal_iff, map_sub, AlgHom.commutes, Algebra.id.map_eq_id,
        RingHom.id_apply, sub_self]

-- The following proof is clumsy
/-- `augIdeal R M` is an augmentation ideal of the `gradeZeroSubalgebra R M`-algebra
  `DividedPowerAlgebra R M`. -/
theorem isAugmentation [DecidableEq M] :
    Ideal.IsAugmentation (gradeZeroSubalgebra R M) (augIdeal R M) := by
  apply IsCompl.mk
  · rw [Submodule.disjoint_def]
    intro x
    simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range, Subtype.exists,
      Submodule.restrictScalars_mem, forall_exists_index, gradeZeroSubalgebra_eq_bot]
    rintro x y ⟨rfl⟩ ⟨rfl⟩ hy
    change algebraMap R _ y ∈ augIdeal R M at hy
    rw [mem_augIdeal_iff] at hy
    simp only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply] at hy
    simp only [hy, map_zero]
    rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    simp only [Submodule.mem_sup, Subalgebra.mem_toSubmodule, Submodule.restrictScalars_mem]
    use algebraMap R _ (algebraMapInv R M p)
    refine ⟨?_, ?_⟩
    · simp only [Algebra.mem_bot, Set.mem_range, Subtype.exists]
      exact ⟨algebraMap R _ (algebraMapInv R M p), algebraMap_mem_grade_zero R M _, rfl⟩
    · refine ⟨p - algebraMap R _ (algebraMapInv R M p), ?_, add_sub_cancel _ _⟩
      simp only [mem_augIdeal_iff, map_sub, AlgHom.commutes, Algebra.id.map_eq_id,
        RingHom.id_apply, sub_self]

end GradeZero
