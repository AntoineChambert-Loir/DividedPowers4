import DividedPowers.DpAlgebra.Init
import DividedPowers.RatAlgebra
import DividedPowers.ForMathlib.WeightedHomogeneous
import DividedPowers.ForMathlib.GradedRingQuot

import Mathlib.Algebra.TrivSqZeroExt

noncomputable section

namespace DividedPowerAlgebra

open DirectSum Finset Function Ideal Ideal.Quotient MvPolynomial RingEquiv RingQuot TrivSqZeroExt 

section CommSemiring

variable (R M : Type _) [CommSemiring R] [AddCommMonoid M] [Module R M] 

variable [DecidableEq R] [DecidableEq M]

local instance : GradedAlgebra (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=
  weightedGradedAlgebra R (Prod.fst : ℕ × M → ℕ)

theorem rel_isPureHomogeneous : 
    RelIsPureHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) (Rel R M) := by 
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
      suffices n = c + (n - c) by
        nth_rewrite 2 [this]
        apply IsWeightedHomogeneous.mul <;> simp only [isWeightedHomogeneous_X]
      rw [mem_range, Nat.lt_succ_iff] at hc
      rw [Nat.add_sub_of_le hc]

theorem Rel_isHomogeneous : 
    RelIsHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) (Rel R M) := 
  RelIsHomogeneous_of_isPureHomogeneous _ (rel_isPureHomogeneous R M) Rel.rfl_zero

theorem RelI_isHomogeneous (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] 
    [DecidableEq R] [DecidableEq M] :
    (RelI R M).IsHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) := 
  IsHomogeneous_of_rel_isPureHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) 
    (Rel R M) (rel_isPureHomogeneous R M)
  
set_option linter.uppercaseLean3 false
#align divided_power_algebra.relI_is_homogeneous DividedPowerAlgebra.RelI_isHomogeneous

set_option linter.uppercaseLean3 true

/-- The graded submodules of `divided_power_algebra R M` -/
def grade (n : ℕ) : Submodule R (DividedPowerAlgebra R M) :=
  quotSubmodule R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) n
#align divided_power_algebra.grade DividedPowerAlgebra.grade

lemma mem_grade_iff (a : DividedPowerAlgebra R M) (n : ℕ) : 
    a ∈ grade R M n ↔ ∃ (p : MvPolynomial (ℕ × M) R), 
      (p ∈ weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ) n) ∧ mk p = a := by
  simp only [grade, _root_.quotSubmodule, Submodule.mem_map]
  rfl

theorem one_mem : (1 : DividedPowerAlgebra R M) ∈ grade R M 0 :=
  ⟨1, isWeightedHomogeneous_one R _, map_one _⟩
#align divided_power_algebra.one_mem DividedPowerAlgebra.one_mem

/-- The canonical decomposition of `divided_power_algebra R M` -/
def decomposition : DirectSum.Decomposition (M := DividedPowerAlgebra R M) (grade R M) := 
  _root_.quotDecomposition R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) (Rel_isHomogeneous R M)
#align divided_power_algebra.decomposition DividedPowerAlgebra.decomposition

/-- The graded algebra structure on the divided power algebra-/
def GAlgebra : GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  DirectSum.Decomposition_RingQuot R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) 
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
instance : GradedAlgebra (DividedPowerAlgebra.grade R M) := GAlgebra R M

theorem mk_comp_toSupported :
    (@mk R M).comp ((Subalgebra.val _).comp (toSupported R)) = mk := by
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
    Surjective ((@mk R M).comp (Subalgebra.val (supported R {nm : ℕ × M | 0 < nm.1}))) := by
  intro f
  obtain ⟨p', hp'⟩ := DividedPowerAlgebra.mk_surjective f
  use toSupported R p'
  rw [← AlgHom.comp_apply, AlgHom.comp_assoc, mk_comp_toSupported, ← hp']
#align divided_power_algebra.surjective_of_supported DividedPowerAlgebra.surjective_of_supported

theorem surjective_of_supported' {n : ℕ} (p : grade R M n) :
    ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
      IsWeightedHomogeneous Prod.fst q.1 n ∧ (@mk R M) q.1 = ↑p := by
  obtain ⟨p', hpn', hp'⟩ := (mem_grade_iff R M _ _).mpr p.2
  use toSupported R p'
  constructor
  · apply toSupported_isHomogeneous'
    exact hpn'
  erw [FunLike.congr_fun (mk_comp_toSupported R M) p', hp']
  -- TODO: write mk_comp_to_supported
#align divided_power_algebra.surjective_of_supported' DividedPowerAlgebra.surjective_of_supported'

theorem mem_grade_iff' {n : ℕ} (p : DividedPowerAlgebra R M) :
    p ∈ grade R M n ↔ ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
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
#align divided_power_algebra.mk_alg_hom_mv_polynomial_ι_eq_ι 
  DividedPowerAlgebra.mk_algHom_mvPolynomial_ι_eq_ι

theorem mk_alg_hom_mv_polynomial_ι_eq_ι' (m : M) : dp R 1 m = ι R m :=
  rfl
#align divided_power_algebra.mk_alg_hom_mv_polynomial_ι_eq_ι'
  DividedPowerAlgebra.mk_alg_hom_mv_polynomial_ι_eq_ι'
-/

variable {M} 
@[simp] theorem ι_comp_lift {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A} 
    (hI : DividedPowers I) {φ : M →ₗ[R] A} (hφ : ∀ (m : M), φ m ∈ I) : 
    (DividedPowerAlgebra.lift hI φ hφ).toLinearMap.comp (ι R M) = φ := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ι_def, 
    liftAlgHom_apply_dp]
  exact hI.dpow_one (hφ m)
#align divided_power_algebra.ι_comp_lift DividedPowerAlgebra.ι_comp_lift

@[simp] theorem lift_ι_apply {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A} 
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : M) : 
    lift hI φ hφ (ι R M x) = φ x := by
  conv_rhs => rw [← ι_comp_lift R hI hφ]; rfl
#align divided_power_algebra.lift_ι_apply DividedPowerAlgebra.lift_ι_apply


variable {R}

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
      (lift' f hf_zero hf_smul hf_mul hf_add) := by
  intro i a 
  simp only [mem_grade_iff]
  rintro ⟨p, hp, rfl⟩
  rw [lift'AlgHom_apply, p.as_sum, aeval_sum]
  apply _root_.sum_mem
  intro c hc
  rw [aeval_monomial, ← smul_eq_mul, algebraMap_smul A, algebra_compatible_smul S (coeff c p)]
  apply Submodule.smul_mem
  rw [← hp (mem_support_iff.mp hc)]
  exact Finsupp.prod.mem_grade _ _ _ _ fun ⟨n, m⟩ _ => hf n m
#align divided_power_algebra.lift_aux_is_homogeneous DividedPowerAlgebra.liftAux_isHomogeneous

variable {R}

instance : GradedAlgebra (DividedPowerAlgebra.grade R M) := GAlgebra R M

theorem lift_isHomogeneous {A : Type _} [CommSemiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A) 
    [GradedAlgebra 𝒜] {I : Ideal A} (hI : DividedPowers I) (hI' : HasGradedDpow 𝒜 hI)
    (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (hφ' : ∀ m, φ m ∈ 𝒜 1) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜 (lift hI φ hφ) := by
  apply liftAux_isHomogeneous
  intro n m
  simpa only [Algebra.id.smul_eq_mul, mul_one] using hI' (φ m) (hφ m) 1 (hφ' m) n
#align divided_power_algebra.lift_is_homogeneous DividedPowerAlgebra.lift_isHomogeneous

variable {N : Type _} [AddCommMonoid N] [DecidableEq S] [DecidableEq N] [Module R N] [Module S N] 
  [IsScalarTower R S N] [Algebra R (DividedPowerAlgebra S N)]
  [IsScalarTower R S (DividedPowerAlgebra S N)] 
  
theorem lift'_isHomogeneous (f : M →ₗ[R] N) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) (DividedPowerAlgebra.grade S N)
      (LinearMap.lift R S f) := by
  apply liftAux_isHomogeneous R S (grade S N)
  exact (λ (n : ℕ) m => dp_mem_grade S N n (f m))
#align divided_power_algebra.lift'_is_homogeneous DividedPowerAlgebra.lift'_isHomogeneous

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/
variable (R M)

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