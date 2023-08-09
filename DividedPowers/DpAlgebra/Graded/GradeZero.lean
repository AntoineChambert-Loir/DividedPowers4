import DividedPowers.DpAlgebra.Graded.Basic

import Mathlib.LinearAlgebra.TensorAlgebra.Basic

noncomputable section

namespace DividedPowerAlgebra


open DirectSum Finset Function Ideal Ideal.Quotient MvPolynomial RingEquiv RingQuot TrivSqZeroExt 

section CommSemiring

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] 

variable [DecidableEq R] [DecidableEq M]

section GradeZero

def algebraMapInv : DividedPowerAlgebra R M →ₐ[R] R :=
  lift (dividedPowersBot R) (0 : M →ₗ[R] R) 
    (fun m => by simp only [LinearMap.zero_apply, mem_bot])
#align divided_power_algebra.algebra_map_inv DividedPowerAlgebra.algebraMapInv

theorem algebraMapInv_eq (f : MvPolynomial (ℕ × M) R) :
    algebraMapInv R M (mk f) = aeval (fun nm : ℕ × M => ite (0 < nm.1) (0 : R) 1) f := by
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  ext ⟨n, m⟩
  simp only [algebraMapInv, AlgHom.comp_apply, aeval_X]
  by_cases hn : 0 < n
  · simp only [if_pos hn, liftAlgHom_apply, LinearMap.zero_apply, aeval_X]
    rw [DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]
  · rw [if_neg hn]
    rw [not_lt, le_zero_iff] at hn 
    simp only [hn, liftAlgHom_apply, LinearMap.zero_apply, aeval_X, 
      DividedPowers.dpow_zero _ (mem_bot.mpr rfl)]
#align divided_power_algebra.algebra_map_inv_eq DividedPowerAlgebra.algebraMapInv_eq

theorem proj'_zero_comp_algebraMap [DecidableEq R] [DecidableEq M] (x : R) :
  ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val =
    (algebraMap R (DividedPowerAlgebra R M)) x := by
  simp only [proj', proj, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, 
    Algebra.algebraMap_eq_smul_one, decompose_smul, decompose_one]
  rfl
#align divided_power_algebra.proj'_zero_comp_algebra_map
  DividedPowerAlgebra.proj'_zero_comp_algebraMap

theorem algebraMap_leftInverse :
    Function.LeftInverse (algebraMapInv R M) (algebraMap R (DividedPowerAlgebra R M)) := fun m => by
  simp only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply]
#align divided_power_algebra.algebra_map_left_inverse DividedPowerAlgebra.algebraMap_leftInverse

@[simp] theorem algebraMap_inj (x y : R) :
    (algebraMap R (DividedPowerAlgebra R M) x = algebraMap R (DividedPowerAlgebra R M) y) ↔ x = y :=
  (algebraMap_leftInverse R M).injective.eq_iff
#align divided_power_algebra.algebra_map_inj DividedPowerAlgebra.algebraMap_inj

@[simp] theorem algebraMap_eq_zero_iff (x : R) : 
    algebraMap R (DividedPowerAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _ _).injective
#align divided_power_algebra.algebra_map_eq_zero_iff DividedPowerAlgebra.algebraMap_eq_zero_iff

@[simp] theorem algebraMap_eq_one_iff (x : R) : 
    algebraMap R (DividedPowerAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _ _).injective
#align divided_power_algebra.algebra_map_eq_one_iff DividedPowerAlgebra.algebraMap_eq_one_iff

theorem mkₐ_eq_aeval {C : Type _} [CommRing C] {D : Type _} (I : Ideal (MvPolynomial D C)) :
    Ideal.Quotient.mkₐ C I = aeval fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d
  simp only [mkₐ_eq_mk, aeval_X]
#align divided_power_algebra.mkₐ_eq_aeval DividedPowerAlgebra.mkₐ_eq_aeval

theorem mk_eq_eval₂ {C : Type _} [CommRing C] {D : Type _} (I : Ideal (MvPolynomial D C)) :
    (Ideal.Quotient.mk I).toFun =
      eval₂ (algebraMap C (MvPolynomial D C ⧸ I)) fun d : D => Ideal.Quotient.mk I (X d) := by 
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← mkₐ_eq_mk C, mkₐ_eq_aeval, aeval_X] 
  rfl
#align divided_power_algebra.mk_eq_eval₂ DividedPowerAlgebra.mk_eq_eval₂

theorem algebraMap_right_inv_of_degree_zero (x : grade R M 0) :
  (algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.1) = x.1 := by
  obtain ⟨p, hp0, hpx⟩ := (mem_grade_iff' _ _ _).mp x.2
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
    simp only [weightedDegree', LinearMap.toAddMonoidHom_coe, Finsupp.total_apply, Finsupp.sum, 
      sum_eq_zero_iff] at hp0
    specialize hp0 nm hnm
    simp only [smul_eq_mul, mul_eq_zero] at hp0 
    cases' hp0 with hnm0 hnm0
    . simp only [Finsupp.mem_support_iff] at hnm
      exact hnm hnm0
    . apply lt_irrefl 0
      nth_rewrite 2 [← hnm0]
      apply MvPolynomial.mem_supported.mp p.prop
      simp only [mem_coe, mem_vars, Finsupp.mem_support_iff, ne_eq, mem_support_iff, exists_prop]
      simp only [Finsupp.mem_support_iff] at hnm
      exact ⟨exp, h, hnm⟩
#align divided_power_algebra.algebra_map_right_inv_of_degree_zero
  DividedPowerAlgebra.algebraMap_right_inv_of_degree_zero

end GradeZero

end CommSemiring

section CommRing

variable (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M] 

variable [DecidableEq R] [DecidableEq M]

section GradeZero

/-- An ideal J of a commutative ring A is an augmentation ideal
if ideal.quotient.mk J has a right inverse which is a RingHom -/
def IsAugmentationIdeal (A : Type _) [CommRing A] (J : Ideal A) : Prop :=
  ∃ g : A ⧸ J →+* A, Ideal.Quotient.mk J ∘ g = id
#align is_augmentation_ideal DividedPowerAlgebra.IsAugmentationIdeal

/-- The augmentation ideal in the divided_power_algebra -/
def augIdeal : (Ideal (DividedPowerAlgebra R M) : Type (max u v)) := 
  RingHom.ker (algebraMapInv R M)
#align divided_power_algebra.aug_ideal DividedPowerAlgebra.augIdeal


theorem mem_augIdeal_iff (f : DividedPowerAlgebra R M) :
    f ∈ augIdeal R M ↔ algebraMapInv R M f = 0 := by 
  rw [augIdeal, RingHom.mem_ker]
#align divided_power_algebra.mem_aug_ideal_iff DividedPowerAlgebra.mem_augIdeal_iff

/-- The image of ι is contained in the augmentation ideal -/
theorem ι_mem_augIdeal (m : M) : ι R M m ∈ augIdeal R M := by
  simp only [mem_augIdeal_iff, ι_def, dp, algebraMapInv_eq, aeval_X, zero_lt_one, ite_true]
#align divided_power_algebra.ι_mem_aug_ideal DividedPowerAlgebra.ι_mem_augIdeal

--instance : CommRing (DividedPowerAlgebra R M ⧸ augIdeal R M) := inferInstance
  /- Ideal.Quotient.commRing (augIdeal R M)  -/-- Slow
  /- @Ideal.Quotient.commRing (DividedPowerAlgebra R M)
    (DividedPowerAlgebra.instCommRing R M) (augIdeal R M) -/ 

set_option profiler true

example : HasQuotient (TensorAlgebra R M) (Ideal (TensorAlgebra R M)) := 
  Submodule.hasQuotient

example : HasQuotient (DividedPowerAlgebra R M) (Ideal (DividedPowerAlgebra R M)) := 
  Submodule.hasQuotient

example : CommRing (DividedPowerAlgebra R M ⧸ augIdeal R M) := 
  Quotient.commRing (augIdeal R M)


-- This one is still too slow
instance (priority := high) instAlgebra' : Algebra R (DividedPowerAlgebra R M ⧸ augIdeal R M) := 
Quotient.algebra R

count_heartbeats in -- prints heartbeat count in the declaration (and sets `maxHeartbeats` to infinity)
set_option synthInstance.maxHeartbeats 100000 in
set_option trace.profiler true in -- prints wall clock times in the declaration
set_option pp.proofs.withType false in
--The next two lemmas timeout (due to an inference problem, I think) 
lemma augIdeal_isAugmentationIdeal' : 
  Function.RightInverse 
    (kerLiftAlg (algebraMapInv R M))
    (algebraMap R (DividedPowerAlgebra R M ⧸ augIdeal R M)) := by
  refine' Function.rightInverse_of_injective_of_leftInverse (RingHom.kerLift_injective _) _
  intro r
  simp only [AlgHom.toRingHom_eq_coe]
  apply AlgHomClass.commutes 


#exit

-- We prove that the augmentation is an augmentation ideal, namely there is a section
theorem augIdeal_isAugmentationIdeal :
  IsAugmentationIdeal (DividedPowerAlgebra R M) (augIdeal R M) := by
  sorry
  /- use (algebraMap R (DividedPowerAlgebra R M)).comp (kerLiftAlg (algebraMapInv R M)).toRingHom
  ext x
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, 
    mk_algebraMap, id_eq]
  apply augIdeal_isAugmentationIdeal' -/
#align divided_power_algebra.aug_ideal_is_augmentation_ideal 
  DividedPowerAlgebra.augIdeal_isAugmentationIdeal

-- Q : if algebra map has a section, is the kernel an augmentation ideal?
theorem coeff_zero_of_mem_augIdeal {f : MvPolynomial (ℕ × M) R}
    (hf : f ∈ supported R {nm : ℕ × M | 0 < nm.fst}) (hf0 : mk f ∈ augIdeal R M) :
    coeff 0 f = 0 := by
  rw [augIdeal, RingHom.mem_ker] at hf0 
  rw [← hf0, algebraMapInv_eq R M, eq_comm]
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
    exact zero_pow (zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hi))
  · intro hf'
    rw [monomial_zero', aeval_C, Algebra.id.map_eq_id, RingHom.id_apply, ←
      not_mem_support_iff.mp hf']
#align divided_power_algebra.coeff_zero_of_mem_aug_ideal
  DividedPowerAlgebra.coeff_zero_of_mem_augIdeal

/- theorem augIdeal_eq_span' : augIdeal R M = span (Set.image2 (dp R) {n : ℕ | 0 < n} ⊤) :=
  sorry
#align divided_power_algebra.aug_ideal_eq_span' DividedPowerAlgebra.augIdeal_eq_span'
 -/

-- TODO: is it better to use ⊤ or set.univ? Is it the same?
theorem  augIdeal_eq_span : 
    augIdeal R M = span (Set.image2 (dp R) {n : ℕ | 0 < n} Set.univ) := by
  classical
  apply le_antisymm
  · intro f0 hf0
    obtain ⟨⟨f, hf⟩, rfl⟩ := surjective_of_supported R M f0
    have hf0' : coeff 0 f = 0 := coeff_zero_of_mem_augIdeal R M hf hf0
    simp only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply] at hf0 ⊢
    rw [f.as_sum, map_sum]
    refine' Ideal.sum_mem _ _
    intro c hc
    rw [monomial_eq, Finsupp.prod]
    simp only [_root_.map_mul]
    refine' mul_mem_left _ _ _
    suffices supp_ss : ↑c.support ⊆ {nm : ℕ × M | 0 < nm.fst} by
      by_cases hc0 : c.support.Nonempty
      · obtain ⟨⟨n, m⟩, hnm⟩ := hc0
        rw [Finset.prod_eq_mul_prod_diff_singleton hnm]
        simp only [_root_.map_mul, map_pow]
        apply
          mul_mem_right _ _
            (pow_mem_of_mem _ _ _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hnm)))
        exact subset_span ⟨n, m, by simpa only using supp_ss hnm, Set.mem_univ _, rfl⟩
      · -- cas où c.support est vide : c = 0 ; contradiction
        rw [not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hc0 
        rw [hc0] at hc 
        exact absurd hf0' (mem_support_iff.mp hc)
    · -- supp_ss
      intro nm hnm
      apply mem_supported.mp hf
      simp only [mem_vars, mem_coe, mem_support_iff, Ne.def, Finsupp.mem_support_iff, exists_prop]
      rw [mem_coe, Finsupp.mem_support_iff] at hnm 
      exact ⟨c, ⟨mem_support_iff.mp hc, hnm⟩⟩
  · rw [span_le]
    intro f
    simp only [Set.mem_image2, Set.mem_setOf_eq, Set.mem_univ, true_and_iff, exists_and_left,
      SetLike.mem_coe, forall_exists_index, and_imp]
    intro n hn m hf
    rw [← hf, mem_augIdeal_iff, algebraMapInv, liftAlgHom_apply_dp]
    simp_rw [LinearMap.zero_apply]
    rw [DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]
#align divided_power_algebra.aug_ideal_eq_span DividedPowerAlgebra.augIdeal_eq_span

theorem right_inv' (x : R) :
    (algebraMapInv R M) ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val = x := by
  rw [proj'_zero_comp_algebraMap]
  exact algebraMap_leftInverse R M x
#align divided_power_algebra.right_inv' DividedPowerAlgebra.right_inv'

theorem left_inv' (x : grade R M 0) :
    (proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.val) = x := by
  ext
  simp only [proj', proj, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  conv_rhs => rw [← DirectSum.decompose_of_mem_same _ x.2]
  simp only [algebraMap_right_inv_of_degree_zero R M x, decompose_coe, of_eq_same]
#align divided_power_algebra.left_inv' DividedPowerAlgebra.left_inv'

theorem lift_augIdeal_le {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) :
    Ideal.map (lift hI φ hφ) (augIdeal R M) ≤ I := by
  simp only [augIdeal_eq_span, Ideal.map_span, Ideal.span_le, SetLike.mem_coe]
  rintro y ⟨x, ⟨n, m, hn, _, rfl⟩, rfl⟩
  simp only [liftAlgHom_apply_dp]
  exact hI.dpow_mem (ne_of_gt hn) (hφ m)
#align divided_power_algebra.lift_aug_ideal_le DividedPowerAlgebra.lift_augIdeal_le

theorem lift_mem_of_mem_augIdeal {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : DividedPowerAlgebra R M)
    (hx : x ∈ augIdeal R M) : lift hI φ hφ x ∈ I :=
  (lift_augIdeal_le R M hI φ hφ) (mem_map_of_mem _ hx)
#align divided_power_algebra.lift_mem_of_mem_aug_ideal DividedPowerAlgebra.lift_mem_of_mem_augIdeal

-- grade R M 0 → R is isomorphism
noncomputable def ringEquivDegreeZero : RingEquiv (grade R M 0) R where
  toFun x      := algebraMapInv R M x.1
  invFun       := proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)
  left_inv     := left_inv' R M
  right_inv    := right_inv' R M
  map_mul' x y := by rw [← _root_.map_mul] ; rfl
  map_add' x y := by rw [← _root_.map_add] ; rfl
#align divided_power_algebra.ring_equiv_degree_zero DividedPowerAlgebra.ringEquivDegreeZero

def proj0RingHom : RingHom (DividedPowerAlgebra R M) R where
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
#align divided_power_algebra.proj_0_ring_hom DividedPowerAlgebra.proj0RingHom

end GradeZero