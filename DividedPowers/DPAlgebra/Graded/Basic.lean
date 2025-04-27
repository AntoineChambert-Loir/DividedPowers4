/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.Init
import DividedPowers.ForMathlib.GradedRingQuot
import Mathlib.Algebra.MvPolynomial.CommRing


noncomputable section

namespace DividedPowerAlgebra

open DirectSum Finset Function Ideal Ideal.Quotient MvPolynomial RingEquiv RingQuot TrivSqZeroExt

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The weighted graded algebra structure on `MvPolynomial (ℕ × M) R`.-/
local instance : GradedAlgebra (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=
  weightedGradedAlgebra R (Prod.fst : ℕ × M → ℕ)

theorem rel_isPureHomogeneous :
    Rel.IsPureHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) (Rel R M) := by
  intro a b h
  cases h with
  | rfl_zero => exact ⟨0, zero_mem _, zero_mem _⟩
  | zero =>
      use 0
      simp only [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_X,
        isWeightedHomogeneous_one, and_self]
  | @smul r n x =>
      use n
      simp only [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_X,
        Submodule.smul_mem, and_self]
  | @mul m n =>
      use m + n
      exact ⟨IsWeightedHomogeneous.mul (isWeightedHomogeneous_X _ _ _)
        (isWeightedHomogeneous_X _ _ _), nsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_X _ _ _)) _⟩
  | @add n =>
      use n
      refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_X _ _ _), ?_⟩
      apply Submodule.sum_mem
      exact fun (c, d) hcd ↦ mem_antidiagonal.mp hcd ▸
        (isWeightedHomogeneous_X _ _ _).mul (isWeightedHomogeneous_X _ _ _)

theorem Rel_isHomogeneous :
    Rel.IsHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) (Rel R M) :=
  Rel.IsHomogeneous_of_isPureHomogeneous (rel_isPureHomogeneous R M) Rel.rfl_zero

theorem RelI_isHomogeneous (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    (RelI R M).IsHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=
  IsHomogeneous_of_rel_isPureHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (Rel R M) (rel_isPureHomogeneous R M)

/-- The graded submodules of `DividedPowerAlgebra R M`. -/
def grade (n : ℕ) : Submodule R (DividedPowerAlgebra R M) :=
  quotSubmodule R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) n

lemma mem_grade_iff (a : DividedPowerAlgebra R M) (n : ℕ) :
    a ∈ grade R M n ↔ ∃ (p : MvPolynomial (ℕ × M) R),
      (p ∈ weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ) n) ∧ mk p = a := by
  simp only [grade, _root_.quotSubmodule, Submodule.mem_map]; rfl

theorem one_mem : (1 : DividedPowerAlgebra R M) ∈ grade R M 0 :=
  ⟨1, isWeightedHomogeneous_one R _, map_one _⟩

/-- The canonical decomposition of `DividedPowerAlgebra R M` -/
def decomposition [DecidableEq R] [DecidableEq M] :
    DirectSum.Decomposition (M := DividedPowerAlgebra R M) (grade R M) :=
  quotDecomposition R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) (Rel_isHomogeneous R M)

/-- The graded algebra structure on the divided power algebra-/
def gradedAlgebra [DecidableEq R] [DecidableEq M] : GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  DirectSum.Decomposition_RingQuot R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.Rel R M) (Rel_isHomogeneous R M)

open Classical in
instance : GradedAlgebra (grade R M) :=
  gradedAlgebra R M

open MvPolynomial

theorem dp_mem_grade (n : ℕ) (m : M) : dp R n m ∈ grade R M n :=
  ⟨X (n, m), isWeightedHomogeneous_X R _ (n, m), rfl⟩

/-- The degree of a product is equal to the sum of the degrees. -/
theorem mul_mem [DecidableEq R] [DecidableEq M] ⦃i j : ℕ⦄ {gi gj : DividedPowerAlgebra R M}
    (hi : gi ∈ grade R M i) (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
  (gradedAlgebra R M).toGradedMonoid.mul_mem hi hj

/-- The equivalence between `DividedPowerAlgebra R M` and the direct sum of `grade R M i`,
  where `i` runs over `ℕ`. -/
def decompose [DecidableEq R] [DecidableEq M] :
    DividedPowerAlgebra R M → DirectSum ℕ fun i : ℕ => ↥(grade R M i) :=
  (gradedAlgebra R M).toDecomposition.decompose'

/-- The graded algebra instance on `DividedPowerAlgebra R M`. -/
instance [DecidableEq R] [DecidableEq M]  : GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  gradedAlgebra R M

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

theorem surjective_of_supported :
    Surjective ((@mk R M).comp (Subalgebra.val (supported R {nm : ℕ × M | 0 < nm.1}))) := by
  intro f
  obtain ⟨p', hp'⟩ := DividedPowerAlgebra.mk_surjective f
  use toSupported R p'
  rw [← AlgHom.comp_apply, AlgHom.comp_assoc, mk_comp_toSupported, ← hp']

variable {R M}

theorem surjective_of_supported' {n : ℕ} (p : grade R M n) :
    ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
      IsWeightedHomogeneous Prod.fst q.1 n ∧ (@mk R M) q.1 = ↑p := by
  obtain ⟨p', hpn', hp'⟩ := (mem_grade_iff R M _ _).mpr p.2
  use toSupported R p'
  refine ⟨toSupported_isHomogeneous _ _ _ hpn', ?_⟩
  erw [DFunLike.congr_fun (mk_comp_toSupported R M) p', hp']

/-- We show that an element `p : DividedPowerAlgebra R M` belongs to the degree `n` submodule if
  and only if it is the image under `DividedPowerAlgebra.mk` of a homogeneous polynomial of
  degree `n` supported on `{nm : ℕ × M | 0 < nm.1}`. -/
theorem mem_grade_iff' {n : ℕ} (p : DividedPowerAlgebra R M) :
    p ∈ grade R M n ↔ ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
      IsWeightedHomogeneous Prod.fst q.1 n ∧ (@mk R M) q.1 = p :=
  ⟨fun hp ↦ Submodule.coe_mk p hp ▸ surjective_of_supported' _, fun ⟨q, hq, hpq⟩ ↦  ⟨q, hq, hpq⟩⟩

variable (R M) in
/-- The canonical linear map `M →ₗ[R] DividedPowerAlgebra R M`. -/
def ι : M →ₗ[R] DividedPowerAlgebra R M := {
  toFun     := fun m ↦ dp R 1 m
  map_add'  := fun x y ↦ by
    simp only [dp_add]
    simp only [Nat.antidiagonal_succ, zero_add, antidiagonal_zero, map_singleton,
      Embedding.coe_prodMap, Embedding.coeFn_mk, Prod.map_apply, Nat.reduceSucc,
      Embedding.refl_apply, cons_eq_insert, mem_singleton, Prod.mk.injEq, and_self,
      not_false_eq_true, sum_insert, sum_singleton]
    simp only [mem_singleton, Prod.mk.injEq, zero_ne_one, one_ne_zero, and_self, not_false_eq_true,
      sum_insert, dp_zero, one_mul, sum_singleton, mul_one, add_comm]
  map_smul' := fun r x ↦ by
    simp only [dp_smul, pow_one, RingHom.id_apply] }

theorem ι_def (m : M) : ι R M m = dp R 1 m := rfl

@[simp] theorem ι_comp_lift {A : Type*} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) {φ : M →ₗ[R] A} (hφ : ∀ (m : M), φ m ∈ I) :
    (DividedPowerAlgebra.lift hI φ hφ).toLinearMap.comp (ι R M) = φ := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ι_def,
    lift_apply_dp]
  exact hI.dpow_one (hφ m)

@[simp] theorem lift_ι_apply {A : Type*} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) {φ : M →ₗ[R] A} (hφ : ∀ m, φ m ∈ I) (x : M) :
    lift hI φ hφ (ι R M x) = φ x := by
  conv_rhs => rw [← ι_comp_lift hI hφ]
  rfl

/-- We say that a divided power algebra has a *graded* divided power structure if for every `n : ℕ`,
  `hI.dpow n` sends elements of `𝒜 i` to elements of `𝒜 (n • i)`.  -/
def HasGradedDpow {A : Type*} [CommSemiring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) {I : Ideal A} (hI : DividedPowers I) : Prop :=
  ∀ a ∈ I, ∀ (n i : ℕ) (_ : a ∈ 𝒜 i) , hI.dpow n a ∈ 𝒜 (n • i)

section lift'

variable {S : Type*} [CommSemiring S] [Algebra R S]

theorem liftAux_isHomogeneous {A : Type*} [CommSemiring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜] {f : ℕ × M → A}
    (hf_zero : ∀ m, f (0, m) = 1)
    (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : ∀ n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : ∀ n u v, f ⟨n, u + v⟩ = (antidiagonal n).sum fun (x, y) => f ⟨x, u⟩ * f ⟨y, v⟩)
    (hf : ∀ n m, f (n, m) ∈ 𝒜 n) :
    GAlgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜 (id : ℕ → ℕ)
      (lift' hf_zero hf_smul hf_mul hf_add) := by
  intro i a
  rw [mem_grade_iff]
  rintro ⟨p, hp, rfl⟩
  rw [lift'_apply, p.as_sum, aeval_sum]
  apply _root_.sum_mem
  intro c hc
  rw [aeval_monomial, ← smul_eq_mul, algebraMap_smul A, algebra_compatible_smul S (coeff c p)]
  apply Submodule.smul_mem
  exact hp (mem_support_iff.mp hc) ▸ Finsupp.prod_mem_grade fun ⟨n, m⟩ _ => hf n m

theorem lift_isHomogeneous {A : Type*} [CommSemiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] {I : Ideal A} (hI : DividedPowers I) (hI' : HasGradedDpow 𝒜 hI)
    (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (hφ' : ∀ m, φ m ∈ 𝒜 1) :
    GAlgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜  (id : ℕ → ℕ) (lift hI φ hφ) := by
  apply liftAux_isHomogeneous
  intro n m
  simpa only [Algebra.id.smul_eq_mul, mul_one] using hI' (φ m) (hφ m) n 1 (hφ' m)

variable {N : Type*} [AddCommMonoid N] [DecidableEq S] [DecidableEq N] [Module R N] [Module S N]
  [IsScalarTower R S N]

theorem lift'_isHomogeneous (f : M →ₗ[R] N) :
    GAlgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) (DividedPowerAlgebra.grade S N)
      (id : ℕ → ℕ) (DividedPowerAlgebra.LinearMap.lift S f) :=
  liftAux_isHomogeneous (grade S N) _ _ _ _ (λ (n : ℕ) m => dp_mem_grade S N n (f m))

end lift'

section proj'

variable (R M)

/-- The projection from `DividedPowerAlgebra R M` to the degree `n` submodule `grade R M n`,
  as an `R`-linear map-/
def proj' [DecidableEq R] [DecidableEq M] (n : ℕ) : DividedPowerAlgebra R M →ₗ[R] grade R M n :=
  GradedAlgebra.proj' (grade R M) n

theorem proj'_zero_one [DecidableEq R] [DecidableEq M] : (proj' R M 0) 1 = 1 := by
  rw [proj', GradedAlgebra.proj', LinearMap.coe_mk, AddHom.coe_mk, decompose_one]; rfl

theorem proj'_zero_mul [DecidableEq R] [DecidableEq M] (x y : DividedPowerAlgebra R M) :
    (proj' R M 0) (x * y) = (proj' R M 0) x * (proj' R M 0) y := by
  simp only [proj', ← GradedAlgebra.proj'_zeroRingHom_apply, _root_.map_mul]

end proj'

end DividedPowerAlgebra
