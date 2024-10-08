import DividedPowers.DPAlgebra.Graded.Basic
import DividedPowers.RatAlgebra
import Mathlib.Algebra.TrivSqZeroExt

noncomputable section

namespace DividedPowerAlgebra

open DirectSum Finset Function Ideal Ideal.Quotient MvPolynomial RingEquiv RingQuot TrivSqZeroExt

section CommRing

variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]


section GradeOne

theorem ι_mem_grade_one (m : M) : ι R M m ∈ grade R M 1 :=
  ⟨X ⟨1,m⟩, ⟨isWeightedHomogeneous_X R Prod.fst ⟨1,m⟩, rfl⟩⟩


variable [DecidableEq R]

section Module

variable [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

-- MI: inferInstance does not work!
instance [hR : DecidableEq R] : DecidablePred (fun x ↦ x ∈ kerIdeal R M) :=
  fun a ↦ hR ((fstHom R R M) a) 0

-- MI: I had to add `classical` in this definition (?)
variable (M)

/-- The canonical map from `divided_power_algebra R M` into `triv_sq_zero_ext R M`
  that sends `DividedPowerAlgebra.ι` to `TrivSqZeroExt.inr`. -/
def toTrivSqZeroExt :
    DividedPowerAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift (DividedPowers.OfSquareZero.dividedPowers
      (TrivSqZeroExt.sqZero R M) : DividedPowers (kerIdeal R M))
    (inrHom R M) (fun m => (mem_kerIdeal_iff_exists R M _).mpr ⟨m, rfl⟩)

variable {M}

@[simp] theorem toTrivSqZeroExt_ι (x : M) :
    toTrivSqZeroExt R M (ι R M x) = inr x := lift_ι_apply _ _ x

theorem toTrivSqZeroExt_apply_dp_of_two_le  (n : ℕ) (m : M) (hn : 2 ≤ n) :
    toTrivSqZeroExt R M (dp R n m) = 0 := by
  rw [toTrivSqZeroExt, liftAlgHom_apply_dp, DividedPowers.OfSquareZero.dpow_of_two_le]
  exact hn

end Module

variable (M)

variable [DecidableEq M]

theorem grade_one_eq_span :
    grade R M 1 = Submodule.span R (Set.range (dp R 1)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨q, hq1, hqp⟩ := surjective_of_supported' R M ⟨p, hp⟩
    simp only at hqp
    simp only [IsWeightedHomogeneous, ne_eq] at hq1
    rw [← hqp, (q : MvPolynomial (ℕ × M) R).as_sum, map_sum]
    apply Submodule.sum_mem (Submodule.span R (Set.range (dp R 1)))
    intro d hd
    have hsupp : ∀ nm : ℕ × M, nm ∈ d.support → 0 < nm.fst := by
      intro nm hnm
      apply mem_supported.mp q.2
      rw [mem_coe, mem_vars]
      exact ⟨d, hd, hnm⟩
    obtain ⟨m, hm⟩ := eq_finsupp_single_of_degree_one M (hq1 (mem_support_iff.mp hd)) hsupp
    rw [← hm, monomial_eq, C_mul', map_smul, Finsupp.prod_single_index, pow_one]
    exact Submodule.smul_mem (Submodule.span R (Set.range (dp R 1))) _
      (Submodule.subset_span (Set.mem_range.mpr ⟨m, rfl⟩))
    · rw [pow_zero]
  · rw [Submodule.span_le]
    intro p hp
    obtain ⟨m, hm⟩ := Set.mem_range.mp hp
    rw [← hm]
    exact dp_mem_grade R M 1 m

theorem grade_one_eq_span' :
    (⊤ : Submodule R (grade R M 1)) =
      Submodule.span R (Set.range fun m => ⟨dp R 1 m, dp_mem_grade R M 1 m⟩) := by
  apply Submodule.map_injective_of_injective (grade R M 1).injective_subtype
  rw [Submodule.map_subtype_top, Submodule.map_span]
  simp_rw [grade_one_eq_span R M]
  rw [← Set.range_comp]; rfl

section Module

variable [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem deg_one_right_inv :
    RightInverse
      (TrivSqZeroExt.sndHom R M ∘ (toTrivSqZeroExt R M).toLinearMap ∘ (grade R M 1).subtype)
      (proj' R M 1 ∘ ι R M) := by
  --try with snd_hom , submodule.val
  simp only [Function.rightInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe R]
  rw [DFunLike.coe_injective.eq_iff]
  apply LinearMap.ext_on_range (grade_one_eq_span' R M).symm
  intro m
  simp only [proj', proj, ι, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_subtype, comp_apply, AlgHom.toLinearMap_apply, sndHom_apply,
    LinearMap.id_coe, id_eq]
  ext
  dsimp only
  rw [← ι_def R M m, toTrivSqZeroExt_ι, ← ι_def, snd_inr, decompose_of_mem_same]
  apply ι_mem_grade_one

theorem deg_one_left_inv :
    LeftInverse (fun x : grade R M 1 => (toTrivSqZeroExt R M x.1).snd) (proj' R M 1 ∘ ι R M) := by
  intro m
  simp only [proj', proj, LinearMap.coe_mk, AddHom.coe_mk, ι, Function.comp_apply]
  rw [← TrivSqZeroExt.snd_inr R m, ← ι_def]
  apply congr_arg
  rw [snd_inr, decompose_of_mem_same, toTrivSqZeroExt_ι]
  apply ι_mem_grade_one

-- ι : M → grade R M 1 is an isomorphism
def linearEquivDegreeOne :
    LinearEquiv (RingHom.id R) M (grade R M 1) where
  toFun         := (proj' R M 1).comp (ι R M)
  invFun x      := TrivSqZeroExt.sndHom R M (toTrivSqZeroExt R M x.1)
  map_add' x y  := by simp only [map_add]
  map_smul' r x := by simp only [LinearMap.map_smulₛₗ]
  left_inv      := deg_one_left_inv R M
  right_inv     := deg_one_right_inv R M

lemma ι_toTrivSqZeroExt_of_mem_grade_one {a} (ha : a ∈ grade R M 1) :
    (ι R M) ((sndHom R M) ((toTrivSqZeroExt R M) a)) = a := by
  suffices ⟨(ι R M) ((sndHom R M) ((toTrivSqZeroExt R M) a)), ι_mem_grade_one R _⟩ =
    (⟨a, ha⟩ : grade R M 1) by
    simpa only [sndHom_apply, Subtype.mk.injEq] using this
  apply (linearEquivDegreeOne R M).symm.injective
  rw [← LinearEquiv.invFun_eq_symm]
  simp only [linearEquivDegreeOne, toTrivSqZeroExt_ι, sndHom_apply, snd_inr]

theorem mem_grade_one_iff (a : DividedPowerAlgebra R M) :
    a ∈ grade R M 1 ↔ ∃ m, a = ι R M m := by
  constructor
  . intro ha
    use ((sndHom R M) ((toTrivSqZeroExt R M) a))
    rw [ι_toTrivSqZeroExt_of_mem_grade_one R M ha]
  . rintro ⟨m, rfl⟩
    apply ι_mem_grade_one

end Module

end GradeOne

end CommRing

end DividedPowerAlgebra
