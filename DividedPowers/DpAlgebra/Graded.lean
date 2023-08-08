import DividedPowers.DpAlgebra.Init
import DividedPowers.RatAlgebra
import DividedPowers.ForMathlib.WeightedHomogeneous
import DividedPowers.ForMathlib.GradedRingQuot

import Mathlib.Algebra.TrivSqZeroExt

-- Modified version of PR #17855
-- Modified version of PR #17855
-- Quotients of graded rings
-- Quotients of graded rings

noncomputable section

namespace DividedPowerAlgebra

open Finset MvPolynomial Ideal.Quotient

open TrivSqZeroExt

open Ideal DirectSum

open RingQuot

variable (R M : Type _) [CommSemiring R] [AddCommMonoid M] [Module R M] 

variable [DecidableEq R] [DecidableEq M]

local instance : 
  GradedAlgebra (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=
  weightedGradedAlgebra R (Prod.fst : ℕ × M → ℕ)

theorem rel_isPureHomogeneous : 
  RelIsPureHomogeneous 
    (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) 
    (Rel R M) := by 
  intro a b h
  cases' h with a r n a m n a n a b
  . exact ⟨0, zero_mem _, zero_mem _⟩
  . use 0
    simp only [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_X, isWeightedHomogeneous_one]
  . use n
    simp only [mem_weightedHomogeneousSubmodule, Submodule.smul_mem, isWeightedHomogeneous_X]
  . use m + n
    constructor
    . apply IsWeightedHomogeneous.mul <;> simp only [isWeightedHomogeneous_X]
    . apply nsmul_mem
      simp only [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_X]
  . use n
    constructor
    . simp only [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_X]
    . apply Submodule.sum_mem
      intro c hc
      suffices : n = c + (n - c)
      nth_rewrite 2 [this]
      apply IsWeightedHomogeneous.mul <;> simp only [isWeightedHomogeneous_X]
      . rw [mem_range, Nat.lt_succ_iff] at hc
        rw [Nat.add_sub_of_le hc]

theorem Rel_isHomogeneous : RelIsHomogeneous 
  (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) 
  (Rel R M) :=  by 
  apply RelIsHomogeneous_of_isPureHomogeneous
  apply rel_isPureHomogeneous
  exact Rel.rfl_zero

theorem RelI_isHomogeneous 
    (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] 
    [DecidableEq R] [DecidableEq M] :
  (RelI R M).IsHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=  by 
  apply IsHomogeneous_of_rel_isPureHomogeneous 
    (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) 
    (Rel R M)
  apply rel_isPureHomogeneous
  
set_option linter.uppercaseLean3 false
#align divided_power_algebra.relI_is_homogeneous DividedPowerAlgebra.RelI_isHomogeneous
set_option linter.uppercaseLean3 true

-- THIS DOESN'T WORK ANYMORE BECAUSE I HAVE REWRITTEN
-- DividedPowerAlgebra AS A RingQuot…

/-- The graded submodules of `divided_power_algebra R M` -/
def grade (n : ℕ) : Submodule R (DividedPowerAlgebra R M) :=
  quotSubmodule R 
    (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) n
#align divided_power_algebra.grade DividedPowerAlgebra.grade

def mem_grade_iff (a : DividedPowerAlgebra R M) (n : ℕ) : 
  a ∈ grade R M n ↔ ∃ (p : MvPolynomial (ℕ × M) R), 
    (p ∈ weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ) n) ∧ 
    mk p = a := by
  simp only [grade, _root_.quotSubmodule, Submodule.mem_map]
  rfl

theorem one_mem : (1 : DividedPowerAlgebra R M) ∈ grade R M 0 :=
  ⟨1, isWeightedHomogeneous_one R _, map_one _⟩
#align divided_power_algebra.one_mem DividedPowerAlgebra.one_mem

/-- The canonical decomposition of `divided_power_algebra R M` -/
def decomposition : 
  DirectSum.Decomposition (M := DividedPowerAlgebra R M) (grade R M) := 
  _root_.quotDecomposition R 
    (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) (Rel_isHomogeneous R M)
#align divided_power_algebra.decomposition DividedPowerAlgebra.decomposition


/-- The graded algebra structure on the divided power algebra-/
def GAlgebra : GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  DirectSum.Decomposition_RingQuot R 
    (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) 
    (DividedPowerAlgebra.Rel R M) (Rel_isHomogeneous R M)
#align divided_power_algebra.divided_power_galgebra DividedPowerAlgebra.GAlgebra

open MvPolynomial

-- Do we need both versions?
theorem dp_mem_grade (n : ℕ) (m : M) : dp R n m ∈ grade R M n :=
  ⟨X (n, m), isWeightedHomogeneous_X R _ (n, m), rfl⟩
#align divided_power_algebra.dp_mem_grade DividedPowerAlgebra.dp_mem_grade

/- theorem mkₐ_mem_grade (n : ℕ) (m : M) : (mkₐ R (relI R M)) (X (n, m)) ∈ grade R M n :=
  ⟨X (n, m), isWeightedHomogeneous_X R _ (n, m), rfl⟩
#align divided_power_algebra.mkₐ_mem_grade DividedPowerAlgebra.mkₐ_mem_grade
 -/

/-- degree of a product is sum of degrees -/
theorem mul_mem ⦃i j : ℕ⦄ {gi gj : DividedPowerAlgebra R M} (hi : gi ∈ grade R M i)
    (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
  (GAlgebra R M).toGradedMonoid.mul_mem hi hj
#align divided_power_algebra.mul_mem DividedPowerAlgebra.mul_mem

def decompose : DividedPowerAlgebra R M → DirectSum ℕ fun i : ℕ => ↥(grade R M i) :=
  (GAlgebra R M).toDecomposition.decompose'
#align divided_power_algebra.decompose DividedPowerAlgebra.decompose

-- graded_algebra (grade R M )
instance : GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  GAlgebra R M

theorem mk_comp_toSupported :
    (@mk R M).comp ((Subalgebra.val _).comp (toSupported R)) = mk :=
  by
  apply MvPolynomial.algHom_ext
  rintro ⟨n, m⟩
  simp only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply, aeval_X,
    toSupported]
  split_ifs with h
  · rfl
  · simp only [not_lt, le_zero_iff] at h 
    rw [h, OneMemClass.coe_one, map_one]
    exact (dp_zero R m).symm

#align divided_power_algebra.mkₐ_comp_to_supported DividedPowerAlgebra.mk_comp_toSupported

theorem surjective_of_supported :
  Function.Surjective ((@mk R M).comp 
    (Subalgebra.val (supported R {nm : ℕ × M | 0 < nm.1}))) :=
  by
  intro f
  obtain ⟨p', hp'⟩ := DividedPowerAlgebra.mk_surjective f
  use toSupported R p'
  rw [← AlgHom.comp_apply, AlgHom.comp_assoc, mk_comp_toSupported, ← hp']
#align divided_power_algebra.surjective_of_supported DividedPowerAlgebra.surjective_of_supported

theorem surjective_of_supported' 
    {n : ℕ} (p : grade R M n) :
  ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
    IsWeightedHomogeneous Prod.fst q.1 n ∧ (@mk R M) q.1 = ↑p :=
  by
  --intro f,
  have hp := p.2
  simp only [mem_grade_iff] at hp
  obtain ⟨p', hpn', hp'⟩ := hp
  use toSupported R p'
  constructor
  · apply toSupported_isHomogeneous'
    exact hpn'
  -- rw [← mkₐ_eq_mk R]
  erw [FunLike.congr_fun (mk_comp_toSupported R M) p']
  -- TODO: write mk_comp_to_supported
  -- rw [mkₐ_eq_mk R]
  rw [hp']
#align divided_power_algebra.surjective_of_supported' DividedPowerAlgebra.surjective_of_supported'

theorem mem_grade_iff' {n : ℕ} (p : DividedPowerAlgebra R M) :
  p ∈ grade R M n ↔
  ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
    IsWeightedHomogeneous Prod.fst q.1 n ∧ (@mk R M) q.1 = p := by
  constructor
  . intro hp
    rw [← Submodule.coe_mk p hp]
    apply surjective_of_supported'
  . rintro ⟨q, hq, rfl⟩
    rw [mem_grade_iff]
    exact ⟨q, hq, rfl⟩

/-- The canonical linear map `M →ₗ[R] divided_power_algebra R M`. -/
def ι : M →ₗ[R] DividedPowerAlgebra R M := {
  toFun     := fun m ↦ dp R 1 m
  map_add'  := fun x y ↦ by
    simp only [dp_add, sum_range_succ', sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
      dp_zero, mul_one, one_mul]
  map_smul' := fun r x ↦ by
    simp only [dp_smul, pow_one, RingHom.id_apply] }
#align divided_power_algebra.ι DividedPowerAlgebra.ι

theorem ι_def (m : M) : ι R M m = dp R 1 m := rfl
#align divided_power_algebra.ι_def DividedPowerAlgebra.ι_def

/-
theorem mk_algHom_mvPolynomial_ι_eq_ι (m : M) : mkₐ R (relI R M) (X (1, m)) = ι R m :=
  rfl
#align divided_power_algebra.mk_alg_hom_mv_polynomial_ι_eq_ι DividedPowerAlgebra.mk_algHom_mvPolynomial_ι_eq_ι

theorem mk_alg_hom_mv_polynomial_ι_eq_ι' (m : M) : dp R 1 m = ι R m :=
  rfl
#align divided_power_algebra.mk_alg_hom_mv_polynomial_ι_eq_ι' DividedPowerAlgebra.mk_alg_hom_mv_polynomial_ι_eq_ι'
-/

variable {M} 
@[simp]
theorem ι_comp_lift {A : Type _} [CommRing A] [Algebra R A] 
    {I : Ideal A} (hI : DividedPowers I) 
    {φ : M →ₗ[R] A} (hφ : ∀ (m : M), φ m ∈ I) : 
  (DividedPowerAlgebra.lift hI φ hφ).toLinearMap.comp (ι R M) = φ := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  simp only [ι_def]
  simp only [liftAlgHom_apply_dp]
  exact hI.dpow_one (hφ m)
#align divided_power_algebra.ι_comp_lift DividedPowerAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A} 
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : M) : 
  lift hI φ hφ (ι R M x) = φ x := by
  conv_rhs => rw [← ι_comp_lift R hI hφ]; rfl
#align divided_power_algebra.lift_ι_apply DividedPowerAlgebra.lift_ι_apply


variable {R}

--  [graded_algebra 𝒜] --not used in this def
def HasGradedDpow {A : Type _} [CommSemiring A] [Algebra R A] 
    (𝒜 : ℕ → Submodule R A) {I : Ideal A} (hI : DividedPowers I) :=
  ∀ a ∈ I, ∀ (i : ℕ) (_ : a ∈ 𝒜 i) (n : ℕ), hI.dpow n a ∈ 𝒜 (n • i)
#align divided_power_algebra.has_graded_dpow DividedPowerAlgebra.HasGradedDpow

section DecidableEq

variable (R) 


variable (S : Type _) [CommSemiring S] [Algebra R S] 

theorem liftAux_isHomogeneous {A : Type _} [CommSemiring A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] (𝒜 : ℕ → Submodule S A)
    [GradedAlgebra 𝒜] (f : ℕ × M → A) (hf_zero : ∀ m, f (0, m) = 1)
    (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : ∀ n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : ∀ n u v, f ⟨n, u + v⟩ = (range (n + 1)).sum fun x : ℕ => f ⟨x, u⟩ * f ⟨n - x, v⟩)
    (hf : ∀ n m, f (n, m) ∈ 𝒜 n) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜
      (lift' f hf_zero hf_smul hf_mul hf_add) :=
  by
  intro i a 
  simp only [mem_grade_iff]
  rintro ⟨p, hp, rfl⟩
  rw [lift'AlgHom_apply, p.as_sum, aeval_sum]
  apply _root_.sum_mem
  intro c hc
  rw [aeval_monomial, ← smul_eq_mul, algebraMap_smul A]
  -- rw [smul_assoc]
  simp only [algebra_compatible_smul S (coeff c p)]
  apply Submodule.smul_mem
  rw [← hp (mem_support_iff.mp hc)]
  exact Finsupp.prod.mem_grade _ _ _ _ fun ⟨n, m⟩ _ => hf n m
#align divided_power_algebra.lift_aux_is_homogeneous DividedPowerAlgebra.liftAux_isHomogeneous

variable {R}

instance : GradedAlgebra (DividedPowerAlgebra.grade R M) := GAlgebra R M

theorem lift_isHomogeneous {A : Type _} [CommSemiring A] [Algebra R A] 
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] 
    {I : Ideal A} (hI : DividedPowers I) (hI' : HasGradedDpow 𝒜 hI)
    (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (hφ' : ∀ m, φ m ∈ 𝒜 1) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜 (lift hI φ hφ) :=
  by
  apply liftAux_isHomogeneous
  intro n m
  simpa only [Algebra.id.smul_eq_mul, mul_one] using hI' (φ m) (hφ m) 1 (hφ' m) n
#align divided_power_algebra.lift_is_homogeneous DividedPowerAlgebra.lift_isHomogeneous

#check dp

variable 
  {N : Type _} [AddCommMonoid N] 
  [DecidableEq S] [DecidableEq N]
  [Module R N] [Module S N] [IsScalarTower R S N] 
  [Algebra R (DividedPowerAlgebra S N)]
  [IsScalarTower R S (DividedPowerAlgebra S N)] 
  
theorem lift'_isHomogeneous (f : M →ₗ[R] N) :
  GalgHom.IsHomogeneous 
    (DividedPowerAlgebra.grade R M) (DividedPowerAlgebra.grade S N)
    (LinearMap.lift R S f) :=
  by
  apply liftAux_isHomogeneous R S (grade S N)
  intro n m
  exact dp_mem_grade S N n (f m)
/- 
  sorry 
  | hf_zero m := 
      dsimp
      rw [dp_zero]
  sorry
    (hf_smul := fun n r m => by 
      dsimp
      rw [LinearMap.map_smul, algebra_compatible_smul S r, 
        dp_smul, ← map_pow, ← algebra_compatible_smul S (r ^ n)])
    (hf_mul := fun n p m => by rw [dp_mul])
    (hf_add := fun n u v => by rw [map_add, dp_add])
    (hf := fun n m => by apply dp_mem_grade) -/
#align divided_power_algebra.lift'_is_homogeneous DividedPowerAlgebra.lift'_isHomogeneous

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/
variable (R)


def proj' (n : ℕ) : DividedPowerAlgebra R M →ₗ[R] grade R M n := proj (grade R M) n

#align divided_power_algebra.proj' DividedPowerAlgebra.proj'

theorem proj'_zero_one : (proj' R M 0) 1 = 1 := by
  rw [proj', proj, LinearMap.coe_mk, AddHom.coe_mk, decompose_one]
  rfl
#align divided_power_algebra.proj'_zero_one DividedPowerAlgebra.proj'_zero_one

theorem proj'_zero_mul (x y : DividedPowerAlgebra R M) :
    (proj' R M 0) (x * y) = (proj' R M 0) x * (proj' R M 0) y := by
  simp only [proj', ← projZeroRingHom'_apply, _root_.map_mul]
#align divided_power_algebra.proj'_zero_mul DividedPowerAlgebra.proj'_zero_mul

end DecidableEq

/- -- now useless instance :
    AddSubmonoidClass (Submodule R (DividedPowerAlgebra R M)) (DividedPowerAlgebra R M) := inferInstance
--  Submodule.addSubmonoidClass
-/

section GradeZero

variable (R)

def algebraMapInv : DividedPowerAlgebra R M →ₐ[R] R :=
  lift (dividedPowersBot R) (0 : M →ₗ[R] R) 
    (fun m => by simp only [LinearMap.zero_apply, mem_bot])
#align divided_power_algebra.algebra_map_inv DividedPowerAlgebra.algebraMapInv

theorem algebraMapInv_eq (f : MvPolynomial (ℕ × M) R) :
  algebraMapInv R M (mk f) = 
    aeval (fun nm : ℕ × M => ite (0 < nm.1) (0 : R) 1) f := by
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  ext ⟨n, m⟩
  simp only [algebraMapInv, AlgHom.comp_apply, aeval_X]
  by_cases hn : 0 < n
  · simp only [if_pos hn, liftAlgHom_apply, LinearMap.zero_apply, aeval_X]
    rw [DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]
  · rw [if_neg hn]
    rw [not_lt, le_zero_iff] at hn 
    simp only [hn, liftAlgHom_apply, LinearMap.zero_apply, aeval_X, DividedPowers.dpow_zero _ (mem_bot.mpr rfl)]
#align divided_power_algebra.algebra_map_inv_eq DividedPowerAlgebra.algebraMapInv_eq

theorem proj'_zero_comp_algebraMap [DecidableEq R] [DecidableEq M] (x : R) :
  ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val =
    (algebraMap R (DividedPowerAlgebra R M)) x := by
  simp only [proj', proj, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  simp only [Algebra.algebraMap_eq_smul_one, decompose_smul, decompose_one]
  rfl
#align divided_power_algebra.proj'_zero_comp_algebra_map DividedPowerAlgebra.proj'_zero_comp_algebraMap

-- variables (M)
theorem algebraMap_leftInverse :
    Function.LeftInverse (algebraMapInv R M) (algebraMap R (DividedPowerAlgebra R M)) := fun m => by
  simp only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply]
#align divided_power_algebra.algebra_map_left_inverse DividedPowerAlgebra.algebraMap_leftInverse

@[simp]
theorem algebraMap_inj (x y : R) :
  (algebraMap R (DividedPowerAlgebra R M) x = 
    algebraMap R (DividedPowerAlgebra R M) y) ↔ x = y :=
  (algebraMap_leftInverse R M).injective.eq_iff
#align divided_power_algebra.algebra_map_inj DividedPowerAlgebra.algebraMap_inj

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : 
  algebraMap R (DividedPowerAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) 
    (algebraMap_leftInverse _ _).injective
#align divided_power_algebra.algebra_map_eq_zero_iff DividedPowerAlgebra.algebraMap_eq_zero_iff

@[simp]
theorem algebraMap_eq_one_iff (x : R) : 
  algebraMap R (DividedPowerAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _ _).injective
#align divided_power_algebra.algebra_map_eq_one_iff DividedPowerAlgebra.algebraMap_eq_one_iff

theorem mkₐ_eq_aeval {C : Type _} [CommRing C] {D : Type _} 
    (I : Ideal (MvPolynomial D C)) :
  Ideal.Quotient.mkₐ C I = aeval fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d
  simp only [mkₐ_eq_mk, aeval_X]
#align divided_power_algebra.mkₐ_eq_aeval DividedPowerAlgebra.mkₐ_eq_aeval

theorem mk_eq_eval₂ {C : Type _} [CommRing C] {D : Type _} 
    (I : Ideal (MvPolynomial D C)) :
  (Ideal.Quotient.mk I).toFun =
    eval₂ (algebraMap C (MvPolynomial D C ⧸ I)) 
      fun d : D => Ideal.Quotient.mk I (X d) := by 
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← mkₐ_eq_mk C, mkₐ_eq_aeval, aeval_X] 
  rfl
#align divided_power_algebra.mk_eq_eval₂ DividedPowerAlgebra.mk_eq_eval₂

theorem algebraMap_right_inv_of_degree_zero (x : grade R M 0) :
  (algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.1) = x.1 := by
  have hx : x.val ∈ grade R M 0 := x.2
  rw [mem_grade_iff'] at hx
  obtain ⟨p, hp0, hpx⟩ := hx
  suffices : ∃ (a : R), p.val = C a
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
    simp only [weightedDegree', LinearMap.toAddMonoidHom_coe, Finsupp.total_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hp0
    specialize hp0 nm hnm
    simp only [smul_eq_mul, mul_eq_zero] at hp0 
    -- simp only [Finsupp.mem_support_iff, ne_eq] at hnm 
    cases' hp0 with hnm0 hnm0
    . simp only [Finsupp.mem_support_iff] at hnm
      exact hnm hnm0
    . apply lt_irrefl 0
      nth_rewrite 2 [← hnm0]
      apply MvPolynomial.mem_supported.mp p.prop
      simp only [mem_coe, mem_vars, Finsupp.mem_support_iff, ne_eq, mem_support_iff, exists_prop]
      simp only [Finsupp.mem_support_iff] at hnm
      exact ⟨exp, h, hnm⟩
#align divided_power_algebra.algebra_map_right_inv_of_degree_zero DividedPowerAlgebra.algebraMap_right_inv_of_degree_zero

/-- An ideal J of a commutative ring A is an augmentation ideal
if ideal.quotient.mk J has a right inverse which is a RingHom -/
def IsAugmentationIdeal (A : Type _) [CommRing A] (J : Ideal A) : Prop :=
  ∃ g : A ⧸ J →+* A, Ideal.Quotient.mk J ∘ g = id
#align is_augmentation_ideal DividedPowerAlgebra.IsAugmentationIdeal

/-- The augmentation ideal in the divided_power_algebra -/
def augIdeal : Ideal (DividedPowerAlgebra R M) :=
  RingHom.ker (algebraMapInv R M)
#align divided_power_algebra.aug_ideal DividedPowerAlgebra.augIdeal

theorem mem_augIdeal_iff (f : DividedPowerAlgebra R M) :
  f ∈ augIdeal R M ↔ algebraMapInv R M f = 0 := by 
  rw [augIdeal, RingHom.mem_ker]
#align divided_power_algebra.mem_aug_ideal_iff DividedPowerAlgebra.mem_augIdeal_iff

/-- The image of ι is contained in the augmentation ideal -/
theorem ι_mem_augIdeal (m : M) : (ι R) m ∈ augIdeal R M := by
  simp only [mem_augIdeal_iff, ι_def, dp, algebraMapInv_eq]
  simp only [aeval_X, zero_lt_one, ite_true]
#align divided_power_algebra.ι_mem_aug_ideal DividedPowerAlgebra.ι_mem_augIdeal

lemma augIdeal_isAugmentationIdeal' : 
  Function.RightInverse 
    (kerLiftAlg (algebraMapInv R M))
    (algebraMap R (DividedPowerAlgebra R M ⧸ augIdeal R M)) := by
  refine' Function.rightInverse_of_injective_of_leftInverse (RingHom.kerLift_injective _) _
  intro r
  simp only [AlgHom.toRingHom_eq_coe]
  apply AlgHomClass.commutes 

-- We prove that the augmentation is an augmentation ideal, namely there is a section
theorem augIdeal_isAugmentationIdeal :
  IsAugmentationIdeal (DividedPowerAlgebra R M) (augIdeal R M) := by
  use (algebraMap R (DividedPowerAlgebra R M)).comp (kerLiftAlg (algebraMapInv R M)).toRingHom
  ext x
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, mk_algebraMap, id_eq]
  apply augIdeal_isAugmentationIdeal'
#align divided_power_algebra.aug_ideal_is_augmentation_ideal DividedPowerAlgebra.augIdeal_isAugmentationIdeal

-- Q : if algebra map has a section, is the kernel an augmentation ideal?
theorem coeff_zero_of_mem_augIdeal {f : MvPolynomial (ℕ × M) R}
    (hf : f ∈ supported R {nm : ℕ × M | 0 < nm.fst}) 
    (hf0 : mk f ∈ augIdeal R M) :
    coeff 0 f = 0 := by
  rw [augIdeal, RingHom.mem_ker] at hf0 
  -- rw [algebraMapInv_eq] at hf0
  rw [← hf0, algebraMapInv_eq R M, eq_comm]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Finset.sum_eq_single 0]
  . simp only [monomial_zero', aeval_C, Algebra.id.map_eq_id, RingHom.id_apply]
  · intro b hb hb0
    rw [aeval_monomial, Algebra.id.map_eq_id, RingHom.id_apply]
    change coeff b f * _ = 0
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
#align divided_power_algebra.coeff_zero_of_mem_aug_ideal DividedPowerAlgebra.coeff_zero_of_mem_augIdeal

/- theorem augIdeal_eq_span' : augIdeal R M = span (Set.image2 (dp R) {n : ℕ | 0 < n} ⊤) :=
  sorry
#align divided_power_algebra.aug_ideal_eq_span' DividedPowerAlgebra.augIdeal_eq_span'
 -/

-- TODO: is it better to use ⊤ or set.univ? Is it the same?
theorem  augIdeal_eq_span : 
  augIdeal R M = span (Set.image2 (dp R) {n : ℕ | 0 < n} Set.univ) :=
  by
  classical
  apply le_antisymm
  · intro f0 hf0
    obtain ⟨⟨f, hf⟩, rfl⟩ := surjective_of_supported R M f0
    have hf0' : coeff 0 f = 0 := coeff_zero_of_mem_augIdeal R M hf hf0
    simp only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply] at hf0 ⊢
    rw [f.as_sum]; rw [map_sum]
    refine' Ideal.sum_mem _ _
    intro c hc
    rw [monomial_eq, Finsupp.prod]
    simp only [_root_.map_mul]
    refine' mul_mem_left _ _ _
    suffices supp_ss : ↑c.support ⊆ {nm : ℕ × M | 0 < nm.fst}
    · by_cases hc0 : c.support.Nonempty
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
    (proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.val) = x :=
  by
  ext
  simp only [proj'._eq_1, proj._eq_1, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  conv_rhs => rw [← DirectSum.decompose_of_mem_same _ x.2]
  simp only [algebraMap_right_inv_of_degree_zero R M x, decompose_coe, of_eq_same]
#align divided_power_algebra.left_inv' DividedPowerAlgebra.left_inv'

theorem lift_augIdeal_le {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) :
  Ideal.map (lift hI φ hφ) (augIdeal R M) ≤ I := by
  simp only [augIdeal_eq_span, Ideal.map_span, Ideal.span_le, SetLike.mem_coe]
  rintro y ⟨x, ⟨n, m, hn, _, rfl⟩, rfl⟩
  dsimp
  rw [liftAlgHom_apply_dp]
  exact hI.dpow_mem (ne_of_gt hn) (hφ m)
#align divided_power_algebra.lift_aug_ideal_le DividedPowerAlgebra.lift_augIdeal_le

theorem lift_mem_of_mem_augIdeal {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : DividedPowerAlgebra R M)
    (hx : x ∈ augIdeal R M) : lift hI φ hφ x ∈ I :=
  (lift_augIdeal_le R M hI φ hφ) (mem_map_of_mem _ hx)
#align divided_power_algebra.lift_mem_of_mem_aug_ideal DividedPowerAlgebra.lift_mem_of_mem_augIdeal

-- grade R M 0 → R is isomorphism
noncomputable def ringEquivDegreeZero : RingEquiv (grade R M 0) R
    where
  toFun x := algebraMapInv R M x.1
  invFun := proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)
  left_inv := left_inv' R M
  right_inv := right_inv' R M
  map_mul' x y := by rw [← _root_.map_mul] ; rfl
  map_add' x y := by rw [← _root_.map_add] ; rfl
#align divided_power_algebra.ring_equiv_degree_zero DividedPowerAlgebra.ringEquivDegreeZero

def proj0RingHom : RingHom (DividedPowerAlgebra R M) R
    where
  toFun := (ringEquivDegreeZero R M).toFun ∘ proj' R M 0
  map_one' := by 
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, RingEquiv.coe_toEquiv, Function.comp_apply]
    simp only [proj'_zero_one R M]
    exact (ringEquivDegreeZero R M).map_one
  map_mul' x y := by
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, RingEquiv.coe_toEquiv, Function.comp_apply]
    rw [← _root_.map_mul, proj'_zero_mul]
  map_zero' := by 
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, 
      RingEquiv.coe_toEquiv, Function.comp_apply, map_zero]
  map_add' := by
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, 
      RingEquiv.coe_toEquiv, Function.comp_apply, map_add, forall_const]
#align divided_power_algebra.proj_0_ring_hom DividedPowerAlgebra.proj0RingHom

end GradeZero

section GradeOne

variable (R)

theorem ι_mem_grade_one (m : M) : ι R m ∈ grade R M 1 := by
  rw [mem_grade_iff]
  use X ⟨1,m⟩
  constructor
  . simp only [mem_weightedHomogeneousSubmodule]
    convert isWeightedHomogeneous_X R Prod.fst ⟨1,m⟩
  . rfl

variable [Module Rᵐᵒᵖ M] [IsCentralScalar R M] 

/-- The canonical map from `divided_power_algebra R M` into `triv_sq_zero_ext R M` that sends
`divided_power_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def toTrivSqZeroExt :
    DividedPowerAlgebra R M →ₐ[R] TrivSqZeroExt R M := 
  lift (DividedPowers.OfSquareZero.dividedPowers 
      (TrivSqZeroExt.sqZero R M) : DividedPowers (kerIdeal R M))
    (inrHom R M) 
    (fun m => (mem_kerIdeal_iff_exists R M _).mpr ⟨m, rfl⟩)
#align divided_power_algebra.to_triv_sq_zero_ext DividedPowerAlgebra.toTrivSqZeroExt

@[simp]
theorem toTrivSqZeroExt_ι (x : M) :
    toTrivSqZeroExt R M (ι R x) = inr x :=
  lift_ι_apply R _ _ _ x
#align divided_power_algebra.to_triv_sq_zero_ext_ι DividedPowerAlgebra.toTrivSqZeroExt_ι

/- -- Pas très utile
theorem toTrivSqZeroExt_snd (m : M) :
    ((toTrivSqZeroExt R M) (ι R m)).snd = m := by
  rw [toTrivSqZeroExt_ι]
  rfl
#align divided_power_algebra.to_triv_sq_zero_ext_snd DividedPowerAlgebra.toTrivSqZeroExt_snd
-/

theorem toTrivSqZeroExt_apply_dp_of_two_le (n : ℕ) (m : M) (hn : 2 ≤ n) :
  toTrivSqZeroExt R M (dp R n m) = 0 := by
  rw [toTrivSqZeroExt, liftAlgHom_apply_dp]
  rw [DividedPowers.OfSquareZero.dpow_of_two_le]
  exact hn

theorem deg_one_left_inv :
    Function.LeftInverse 
      (fun x : grade R M 1 => (toTrivSqZeroExt R M x.1).snd)
      (proj' R M 1 ∘ ι R) :=
  by
  intro m
  simp only [proj'._eq_1, proj._eq_1, LinearMap.coe_mk, AddHom.coe_mk, ι, Function.comp_apply]
  rw [← TrivSqZeroExt.snd_inr R m, ← ι_def]
  apply congr_arg
  simp only [snd_inr]
  rw [decompose_of_mem_same, toTrivSqZeroExt_ι]
  apply ι_mem_grade_one

#align divided_power_algebra.deg_one_left_inv DividedPowerAlgebra.deg_one_left_inv

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
    have hsupp : ∀ nm : ℕ × M, nm ∈ d.support → 0 < nm.fst :=
      by
      intro nm hnm
      apply mem_supported.mp q.2
      rw [mem_coe, mem_vars]
      exact ⟨d, hd, hnm⟩
    obtain ⟨m, hm⟩ := eq_finsupp_single_of_degree_one M (hq1 (mem_support_iff.mp hd)) hsupp
    rw [← hm, monomial_eq, C_mul', map_smul, Finsupp.prod_single_index, pow_one]
    exact
      Submodule.smul_mem (Submodule.span R (Set.range (dp R 1))) _
        (Submodule.subset_span (Set.mem_range.mpr ⟨m, rfl⟩))
    · rw [pow_zero]
  · rw [Submodule.span_le]
    intro p hp
    obtain ⟨m, hm⟩ := Set.mem_range.mp hp
    rw [← hm]
    exact dp_mem_grade R M 1 m
#align divided_power_algebra.grade_one_eq_span DividedPowerAlgebra.grade_one_eq_span

theorem grade_one_eq_span' :
    (⊤ : Submodule R (grade R M 1)) =
      Submodule.span R (Set.range fun m => ⟨dp R 1 m, dp_mem_grade R M 1 m⟩) :=
  by
  apply Submodule.map_injective_of_injective (grade R M 1).injective_subtype
  simp only [Submodule.map_subtype_top]
  rw [Submodule.map_span]
  simp_rw [grade_one_eq_span R M]
  rw [← Set.range_comp]; rfl
#align divided_power_algebra.grade_one_eq_span' DividedPowerAlgebra.grade_one_eq_span'


theorem deg_one_right_inv :
    Function.RightInverse
      (TrivSqZeroExt.sndHom R M ∘ (toTrivSqZeroExt R M).toLinearMap ∘ (grade R M 1).subtype)
      (proj' R M 1 ∘ ι R) :=
  by
  --try with snd_hom , submodule.val
  simp only [Function.rightInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe R]
  rw [FunLike.coe_injective.eq_iff]
  apply LinearMap.ext_on_range (grade_one_eq_span' R M).symm
  intro m
  simp only [proj'._eq_1, proj._eq_1, ι, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coeSubtype,
    Function.comp_apply, AlgHom.toLinearMap_apply, sndHom_apply, LinearMap.id_coe, id_eq]
  ext
  dsimp
  rw [← ι_def R m, toTrivSqZeroExt_ι, ← ι_def, snd_inr]
  rw [decompose_of_mem_same]
  apply ι_mem_grade_one
#align divided_power_algebra.deg_one_right_inv DividedPowerAlgebra.deg_one_right_inv

-- ι : M → grade R M 1 is an isomorphism
def linearEquivDegreeOne :
  LinearEquiv (RingHom.id R) M (grade R M 1) where
  toFun := (proj' R M 1).comp (ι R)
  invFun x := TrivSqZeroExt.sndHom R M (toTrivSqZeroExt R M x.1)
  map_add' x y := by simp only [map_add]
  map_smul' r x := by simp only [LinearMap.map_smulₛₗ]
  left_inv := deg_one_left_inv R M
  right_inv := deg_one_right_inv R M
#align divided_power_algebra.linear_equiv_degree_one DividedPowerAlgebra.linearEquivDegreeOne

lemma ι_toTrivSqZeroExt_of_mem_grade_one {a} (ha : a ∈ grade R M 1) :
  (ι R) ((sndHom R M) ((toTrivSqZeroExt R M) a)) = a := by
  suffices : 
    ⟨(ι R) ((sndHom R M) ((toTrivSqZeroExt R M) a)), ι_mem_grade_one R M _⟩ = (⟨a, ha⟩ : grade R M 1) 
  simpa only [sndHom_apply, Subtype.mk.injEq] using this 
  apply (linearEquivDegreeOne R M).symm.injective
  rw [← LinearEquiv.invFun_eq_symm]
  simp only [linearEquivDegreeOne, toTrivSqZeroExt_ι]
  simp only [sndHom_apply, snd_inr]

theorem mem_grade_one_iff (a : DividedPowerAlgebra R M) : 
  a ∈ grade R M 1 ↔ ∃ m, a = ι R m := by
  constructor
  . intro ha
    use ((sndHom R M) ((toTrivSqZeroExt R M) a))
    rw [ι_toTrivSqZeroExt_of_mem_grade_one R M ha]
  . rintro ⟨m, rfl⟩
    apply ι_mem_grade_one

end GradeOne

end DividedPowerAlgebra

