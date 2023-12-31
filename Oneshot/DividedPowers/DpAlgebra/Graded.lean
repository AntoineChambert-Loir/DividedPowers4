import Oneshot.DividedPowers.DPAlgebra.Init
import Oneshot.DividedPowers.RatAlgebra
import Mathbin.Algebra.TrivSqZeroExt
import Oneshot.WeightedHomogeneous
import Oneshot.GradedRingQuot

-- Modified version of PR #17855
-- Modified version of PR #17855
-- Quotients of graded rings
-- Quotients of graded rings
variable (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M]

noncomputable section

namespace DividedPowerAlgebra

open Finset MvPolynomial Ideal.Quotient

open TrivSqZeroExt

open Ideal DirectSum

open RingQuot

section DecidableEq

variable (M)

theorem relI_isHomogeneous :
    (relI R M).Homogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=
  by
  apply is_homogeneous_span
  rintro x ⟨a, b, h, hx⟩
  rw [eq_sub_iff_add_eq.mpr hx]
  induction' h with n r n m n p m n u v
  ·
    exact
      ⟨0, Submodule.sub_mem _ (is_weighted_homogeneous_X R _ _) (is_weighted_homogeneous_one R _)⟩
  ·
    exact
      ⟨n,
        Submodule.sub_mem _ (is_weighted_homogeneous_X R _ _)
          (Submodule.smul_mem _ _ (is_weighted_homogeneous_X R _ _))⟩
  ·
    exact
      ⟨n + p,
        Submodule.sub_mem _
          (is_weighted_homogeneous.mul (is_weighted_homogeneous_X R _ _)
            (is_weighted_homogeneous_X R _ _))
          (nsmul_mem (is_weighted_homogeneous_X R _ _) _)⟩
  · use n
    refine' Submodule.sub_mem _ (is_weighted_homogeneous_X R _ _) (Submodule.sum_mem _ _)
    intro c hc
    have hnc : n = c + (n - c) := (Nat.add_sub_of_le (finset.mem_range_succ_iff.mp hc)).symm
    nth_rw 2 [hnc]
    exact
      is_weighted_homogeneous.mul (is_weighted_homogeneous_X R _ _)
        (is_weighted_homogeneous_X R _ _)
#align divided_power_algebra.relI_is_homogeneous DividedPowerAlgebra.relI_isHomogeneous

variable [DecidableEq R] [DecidableEq M]

/-- The graded submodules of `divided_power_algebra R M` -/
def grade :=
  quotSubmodule R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.relI R M)
#align divided_power_algebra.grade DividedPowerAlgebra.grade

theorem one_mem : (1 : DividedPowerAlgebra R M) ∈ grade R M 0 :=
  ⟨1, isWeightedHomogeneous_one R _, rfl⟩
#align divided_power_algebra.one_mem DividedPowerAlgebra.one_mem

/-- The canonical decomposition of `divided_power_algebra R M` -/
def decomposition :=
  quotDecomposition R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.relI R M) (relI_isHomogeneous R M)
#align divided_power_algebra.decomposition DividedPowerAlgebra.decomposition

end DecidableEq

/-- The graded algebra structure on the divided power algebra-/
def dividedPowerGalgebra [DecidableEq R] [DecidableEq M] :
    GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  gradedQuotAlg R (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
    (DividedPowerAlgebra.relI R M) (DividedPowerAlgebra.relI_isHomogeneous R M)
#align divided_power_algebra.divided_power_galgebra DividedPowerAlgebra.dividedPowerGalgebra

open MvPolynomial

section DecidableEq

variable (M) [DecidableEq R] [DecidableEq M]

-- Do we need both versions?
theorem dp_mem_grade (n : ℕ) (m : M) : dp R n m ∈ grade R M n :=
  ⟨X (n, m), isWeightedHomogeneous_X R _ (n, m), rfl⟩
#align divided_power_algebra.dp_mem_grade DividedPowerAlgebra.dp_mem_grade

theorem mkₐ_mem_grade (n : ℕ) (m : M) : (mkₐ R (relI R M)) (X (n, m)) ∈ grade R M n :=
  ⟨X (n, m), isWeightedHomogeneous_X R _ (n, m), rfl⟩
#align divided_power_algebra.mkₐ_mem_grade DividedPowerAlgebra.mkₐ_mem_grade

/-- degree of a product is sum of degrees -/
theorem mul_mem ⦃i j : ℕ⦄ {gi gj : DividedPowerAlgebra R M} (hi : gi ∈ grade R M i)
    (hj : gj ∈ grade R M j) : gi * gj ∈ grade R M (i + j) :=
  (dividedPowerGalgebra R M).to_gradedMonoid.mul_mem hi hj
#align divided_power_algebra.mul_mem DividedPowerAlgebra.mul_mem

def decompose : DividedPowerAlgebra R M → DirectSum ℕ fun i : ℕ => ↥(grade R M i) :=
  (dividedPowerGalgebra R M).toDecomposition.decompose'
#align divided_power_algebra.decompose DividedPowerAlgebra.decompose

-- graded_algebra (grade R M )
instance : GradedAlgebra (DividedPowerAlgebra.grade R M) :=
  dividedPowerGalgebra R M

end DecidableEq

variable (M)

theorem mkₐ_comp_toSupported :
    (mkₐ R (relI R M)).comp ((Subalgebra.val _).comp (toSupported R)) = mkₐ R _ :=
  by
  apply MvPolynomial.algHom_ext
  rintro ⟨n, m⟩
  simp only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply, aeval_X,
    toSupported]
  split_ifs
  · rfl
  · simp only [not_lt, le_zero_iff] at h 
    dsimp only [relI]
    rw [h, algebraMap.coe_one, quotient_mk_eq_ofRel rel.zero]
#align divided_power_algebra.mkₐ_comp_to_supported DividedPowerAlgebra.mkₐ_comp_toSupported

variable {M}

theorem surjective_of_supported :
    Function.Surjective
      ((mkₐ R (relI R M)).comp (Subalgebra.val (supported R {nm : ℕ × M | 0 < nm.1}))) :=
  by
  intro f
  obtain ⟨p', hp'⟩ := mk_surjective f
  use toSupported R p'
  rw [← AlgHom.comp_apply, AlgHom.comp_assoc, mkₐ_comp_to_supported, ← hp', mkₐ_eq_mk]
#align divided_power_algebra.surjective_of_supported DividedPowerAlgebra.surjective_of_supported

theorem surjective_of_supported' [DecidableEq R] [DecidableEq M] {n : ℕ} (p : grade R M n) :
    ∃ q : supported R {nm : ℕ × M | 0 < nm.1},
      IsWeightedHomogeneous Prod.fst q.1 n ∧ (⇑(mk (relI R M))) q.1 = ↑p :=
  by
  --intro f,
  have hp := p.2
  simp only [grade, quotSubmodule, Subtype.val_eq_coe, Submodule.mem_map,
    mem_weighted_homogeneous_submodule, mkₐ_eq_mk] at hp 
  obtain ⟨p', hpn', hp'⟩ := hp
  use toSupported R p'
  constructor
  · apply toSupported_is_homogeneous
    exact hpn'
  rw [← mkₐ_eq_mk R]
  erw [FunLike.congr_fun (mkₐ_comp_to_supported R M) p']
  -- TODO: write mk_comp_to_supported
  rw [mkₐ_eq_mk R]
  rw [hp']
  · infer_instance
#align divided_power_algebra.surjective_of_supported' DividedPowerAlgebra.surjective_of_supported'

/-- The canonical linear map `M →ₗ[R] divided_power_algebra R M`. -/
def ι : M →ₗ[R] DividedPowerAlgebra R M
    where
  toFun m := dp R 1 m
  map_add' x y := by
    simp only [dp_add, sum_range_succ', sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
      dp_zero, mul_one, one_mul]
  map_smul' r x := by rw [dp_smul, pow_one, RingHom.id_apply]
#align divided_power_algebra.ι DividedPowerAlgebra.ι

theorem ι_def (m : M) : ι R m = dp R 1 m :=
  rfl
#align divided_power_algebra.ι_def DividedPowerAlgebra.ι_def

theorem mk_algHom_mvPolynomial_ι_eq_ι (m : M) : mkₐ R (relI R M) (X (1, m)) = ι R m :=
  rfl
#align divided_power_algebra.mk_alg_hom_mv_polynomial_ι_eq_ι DividedPowerAlgebra.mk_algHom_mvPolynomial_ι_eq_ι

theorem mk_alg_hom_mv_polynomial_ι_eq_ι' (m : M) : dp R 1 m = ι R m :=
  rfl
#align divided_power_algebra.mk_alg_hom_mv_polynomial_ι_eq_ι' DividedPowerAlgebra.mk_alg_hom_mv_polynomial_ι_eq_ι'

@[simp]
theorem ι_comp_lift {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A} (hI : DividedPowers I)
    (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) : (lift R M hI φ hφ).toLinearMap.comp (ι R) = φ :=
  by
  ext
  rw [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ←
    mk_alg_hom_mv_polynomial_ι_eq_ι, lift_eqₐ, eval₂_X]
  exact hI.dpow_one (hφ x)
#align divided_power_algebra.ι_comp_lift DividedPowerAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A} (hI : DividedPowers I)
    (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x) : lift R M hI φ hφ (ι R x) = φ x := by
  conv_rhs => rw [← ι_comp_lift R hI φ hφ]; rfl
#align divided_power_algebra.lift_ι_apply DividedPowerAlgebra.lift_ι_apply

variable (M)

variable {R}

--  [graded_algebra 𝒜] --not used in this def
def HasGradedDpow {A : Type _} [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) {I : Ideal A}
    (hI : DividedPowers I) :=
  ∀ (a : A) (ha : a ∈ I) (i : ℕ) (hai : a ∈ 𝒜 i) (n : ℕ), hI.dpow n a ∈ 𝒜 (n • i)
#align divided_power_algebra.has_graded_dpow DividedPowerAlgebra.HasGradedDpow

section DecidableEq

variable (R) [DecidableEq R] [DecidableEq M]

theorem liftAux_isHomogeneous {A : Type _} [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] (f : ℕ × M → A) (hf_zero : ∀ m, f (0, m) = 1)
    (hf_smul : ∀ (n : ℕ) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : ∀ n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : ∀ n u v, f ⟨n, u + v⟩ = (range (n + 1)).Sum fun x : ℕ => f ⟨x, u⟩ * f ⟨n - x, v⟩)
    (hf : ∀ n m, f (n, m) ∈ 𝒜 n) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜
      (liftAux R M f hf_zero hf_smul hf_mul hf_add) :=
  by
  intro i a ha
  dsimp [grade, quotSubmodule] at ha 
  obtain ⟨p, hp, rfl⟩ := ha
  rw [← mkₐ_eq_mk R, lift_aux_eq, p.as_sum, eval₂_sum]
  apply _root_.sum_mem
  intro c hc
  rw [eval₂_monomial, ← smul_eq_mul, algebraMap_smul A]
  apply Submodule.smul_mem
  rw [← hp (mem_support_iff.mp hc)]
  exact Finsupp.prod.mem_grade _ _ _ _ fun ⟨n, m⟩ hnm => hf n m
  · infer_instance
#align divided_power_algebra.lift_aux_is_homogeneous DividedPowerAlgebra.liftAux_isHomogeneous

variable {R}

theorem lift_isHomogeneous {A : Type _} [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
    [GradedAlgebra 𝒜] {I : Ideal A} (hI : DividedPowers I) (hI' : HasGradedDpow 𝒜 hI)
    (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (hφ' : ∀ m, φ m ∈ 𝒜 1) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) 𝒜 (lift R M hI φ hφ) :=
  by
  apply lift_aux_is_homogeneous
  intro n m
  simpa only [Algebra.id.smul_eq_mul, mul_one] using hI' (φ m) (hφ m) 1 (hφ' m) n
#align divided_power_algebra.lift_is_homogeneous DividedPowerAlgebra.lift_isHomogeneous

theorem lift'_isHomogeneous {N : Type _} [DecidableEq N] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    GalgHom.IsHomogeneous (DividedPowerAlgebra.grade R M) (DividedPowerAlgebra.grade R N)
      (lift' R R f) :=
  by
  apply lift_aux_is_homogeneous
  · intro m; rw [dp_zero]
  · intro n r m; rw [LinearMap.map_smul, dp_smul]
  · intro n p m; rw [dp_mul]
  · intro n u v; rw [map_add, dp_add]
  · intro n m; exact ⟨X (n, f m), ⟨is_weighted_homogeneous_X R _ _, rfl⟩⟩
#align divided_power_algebra.lift'_is_homogeneous DividedPowerAlgebra.lift'_isHomogeneous

/- We need the projections (divided_power_algebra R M) → grade R M n ,
more generally for graded algebras -/
variable (R)

def proj' (n : ℕ) : DividedPowerAlgebra R M →ₗ[R] grade R M n :=
  proj (grade R M) n
#align divided_power_algebra.proj' DividedPowerAlgebra.proj'

theorem proj'_zero_one : (proj' R M 0) 1 = 1 := by
  rw [proj', proj, LinearMap.coe_mk, decompose_one] <;> rfl
#align divided_power_algebra.proj'_zero_one DividedPowerAlgebra.proj'_zero_one

theorem proj'_zero_mul (x y : DividedPowerAlgebra R M) :
    (proj' R M 0) (x * y) = (proj' R M 0) x * (proj' R M 0) y := by
  simp only [proj', ← projZeroRingHom'_apply, _root_.map_mul]
#align divided_power_algebra.proj'_zero_mul DividedPowerAlgebra.proj'_zero_mul

end DecidableEq

instance :
    AddSubmonoidClass (Submodule R (MvPolynomial (ℕ × M) R ⧸ relI R M)) (DividedPowerAlgebra R M) :=
  Submodule.addSubmonoidClass

section GradeZero

variable (R)

-- TODO: use divided_powers.bot instead of of_square_zero
def algebraMapInv : DividedPowerAlgebra R M →ₐ[R] R :=
  lift R M (DividedPowers.OfSquareZero.dividedPowers (by rw [zero_eq_bot, pow_two, bot_mul]))
    (0 : M →ₗ[R] R) fun m => by simp only [LinearMap.zero_apply, zero_eq_bot, mem_bot]
#align divided_power_algebra.algebra_map_inv DividedPowerAlgebra.algebraMapInv

theorem algebraMapInv_eq (f : MvPolynomial (ℕ × M) R) :
    algebraMapInv R M (mkₐ R (relI R M) f) = aeval (fun nm : ℕ × M => ite (0 < nm.1) (0 : R) 1) f :=
  by
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  ext ⟨n, m⟩
  simp only [algebra_map_inv, AlgHom.comp_apply, lift_eqₐ, LinearMap.zero_apply, aeval_X]
  by_cases hn : 0 < n
  · rw [if_pos hn, eval₂_X, DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]
  · rw [if_neg hn]
    rw [not_lt, le_zero_iff] at hn 
    rw [hn, eval₂_X, DividedPowers.dpow_zero _ (mem_bot.mpr rfl)]
#align divided_power_algebra.algebra_map_inv_eq DividedPowerAlgebra.algebraMapInv_eq

theorem proj'_zero_comp_algebraMap [DecidableEq R] [DecidableEq M] (x : R) :
    ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val =
      (algebraMap R (DividedPowerAlgebra R M)) x :=
  by
  rw [Function.comp_apply, Subtype.val_eq_coe, proj', proj, LinearMap.coe_mk,
    Algebra.algebraMap_eq_smul_one, decompose_smul, decompose_one, DFinsupp.coe_smul, Pi.smul_apply,
    Submodule.coe_smul_of_tower]
  rfl
#align divided_power_algebra.proj'_zero_comp_algebra_map DividedPowerAlgebra.proj'_zero_comp_algebraMap

-- variables (M)
theorem algebraMap_leftInverse :
    Function.LeftInverse (algebraMapInv R M) (algebraMap R (DividedPowerAlgebra R M)) := fun m => by
  simp only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply]
#align divided_power_algebra.algebra_map_left_inverse DividedPowerAlgebra.algebraMap_leftInverse

@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (DividedPowerAlgebra R M) x = algebraMap R (DividedPowerAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse R M).Injective.eq_iff
#align divided_power_algebra.algebra_map_inj DividedPowerAlgebra.algebraMap_inj

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (DividedPowerAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _ _).Injective
#align divided_power_algebra.algebra_map_eq_zero_iff DividedPowerAlgebra.algebraMap_eq_zero_iff

@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (DividedPowerAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _ _).Injective
#align divided_power_algebra.algebra_map_eq_one_iff DividedPowerAlgebra.algebraMap_eq_one_iff

theorem mkₐ_eq_aeval {C : Type _} [CommRing C] {D : Type _} (I : Ideal (MvPolynomial D C)) :
    Ideal.Quotient.mkₐ C I = aeval fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d <;> simp only [mkₐ_eq_mk, aeval_X]
#align divided_power_algebra.mkₐ_eq_aeval DividedPowerAlgebra.mkₐ_eq_aeval

theorem mk_eq_eval₂ {C : Type _} [CommRing C] {D : Type _} (I : Ideal (MvPolynomial D C)) :
    (Ideal.Quotient.mk I).toFun =
      eval₂ (algebraMap C (MvPolynomial D C ⧸ I)) fun d : D => Ideal.Quotient.mk I (X d) :=
  by ext d <;> simp_rw [RingHom.toFun_eq_coe, ← mkₐ_eq_mk C, mkₐ_eq_aeval, aeval_X] <;> rfl
#align divided_power_algebra.mk_eq_eval₂ DividedPowerAlgebra.mk_eq_eval₂

theorem algebraMap_right_inv_of_degree_zero [DecidableEq R] [DecidableEq M] (x : grade R M 0) :
    (algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.1) = x.1 :=
  by
  have hx : x.val ∈ grade R M 0 := x.2
  simp only [grade, quotSubmodule, Subtype.val_eq_coe, Submodule.mem_map,
    mem_weighted_homogeneous_submodule, is_weighted_homogeneous] at hx 
  obtain ⟨p, hp0, hpx⟩ := hx
  rw [Subtype.val_eq_coe, ← hpx, algebra_map_inv_eq, mkₐ_eq_aeval, map_aeval, Algebra.id.map_eq_id,
    RingHomCompTriple.comp_eq, coe_eval₂_hom, aeval_def, p.as_sum, eval₂_sum, eval₂_sum,
    Finset.sum_congr rfl]
  intro exp hexp
  have h : ∀ nm : ℕ × M, nm ∈ exp.support → nm.fst = 0 :=
    by
    intro nm hnm
    specialize hp0 (mem_support_iff.mp hexp)
    rw [weighted_degree', Finsupp.total_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hp0 
    specialize hp0 nm hnm
    rw [Algebra.id.smul_eq_mul, Nat.mul_eq_zero] at hp0 
    exact Or.resolve_left hp0 (finsupp.mem_support_iff.mp hnm)
  rw [eval₂_monomial, eval₂_monomial]
  apply congr_arg
  rw [Finsupp.prod_congr]
  intro nm hnm
  rw [if_neg, ← @Prod.mk.eta _ _ nm, ← dp_eq_mk, h nm hnm, dp_zero, map_one]
  · rw [h nm hnm]; exact lt_irrefl 0
#align divided_power_algebra.algebra_map_right_inv_of_degree_zero DividedPowerAlgebra.algebraMap_right_inv_of_degree_zero

/-- An ideal J of a commutative ring A is an augmentation ideal
if ideal.quotient.mk J has a right inverse which is a ring_hom -/
def IsAugmentationIdeal (A : Type _) [CommRing A] (J : Ideal A) : Prop :=
  ∃ g : A ⧸ J →+* A, Ideal.Quotient.mk J ∘ g = id
#align is_augmentation_ideal IsAugmentationIdeal

/-- The augmentation ideal in the divided_power_algebra -/
def augIdeal : Ideal (DividedPowerAlgebra R M) :=
  RingHom.ker (algebraMapInv R M)
#align divided_power_algebra.aug_ideal DividedPowerAlgebra.augIdeal

theorem mem_augIdeal_iff (f : DividedPowerAlgebra R M) :
    f ∈ augIdeal R M ↔ algebraMapInv R M f = 0 := by rw [aug_ideal, RingHom.mem_ker]
#align divided_power_algebra.mem_aug_ideal_iff DividedPowerAlgebra.mem_augIdeal_iff

/-- The image of ι is contained in the augmentation ideal -/
theorem ι_mem_augIdeal (m : M) : (ι R) m ∈ augIdeal R M := by
  simp only [mem_aug_ideal_iff, ι, dp, LinearMap.coe_mk, algebra_map_inv_eq, aeval_X,
    Nat.lt_one_iff, eq_self_iff_true, if_true]
#align divided_power_algebra.ι_mem_aug_ideal DividedPowerAlgebra.ι_mem_augIdeal

-- We prove that the augmentation is an augmentation ideal, namely there is a section
theorem augIdeal_isAugmentationIdeal :
    IsAugmentationIdeal (DividedPowerAlgebra R M) (augIdeal R M) :=
  by
  let g := ker_lift_alg (algebra_map_inv R M)
  let g1 := algebraMap R (DividedPowerAlgebra R M ⧸ aug_ideal R M)
  use (algebraMap R (DividedPowerAlgebra R M)).comp g.to_ring_hom
  ext x
  rw [ker_lift_alg_to_ring_hom, RingHom.coe_comp, Function.comp_apply, mk_algebra_map, id.def]
  suffices h_inv : Function.RightInverse g g1
  · exact h_inv x
  refine' Function.rightInverse_of_injective_of_leftInverse (RingHom.kerLift_injective _) _
  intro r
  rw [AlgHomClass.commutes, Algebra.id.map_eq_id, RingHom.id_apply]
#align divided_power_algebra.aug_ideal_is_augmentation_ideal DividedPowerAlgebra.augIdeal_isAugmentationIdeal

-- Q : if algebra map has a section, is the kernel an augmentation ideal?
theorem coeff_zero_of_mem_augIdeal {f : MvPolynomial (ℕ × M) R}
    (hf : f ∈ supported R {nm : ℕ × M | 0 < nm.fst}) (hf0 : (mk (relI R M)) f ∈ augIdeal R M) :
    coeff 0 f = 0 := by
  rw [aug_ideal, RingHom.mem_ker] at hf0 
  rw [← hf0, ← mkₐ_eq_mk R _, algebra_map_inv_eq R M, eq_comm]
  conv_lhs => rw [f.as_sum, map_sum]
  convert @Finset.sum_eq_single _ _ _ f.support _ 0 _ _
  · rw [monomial_zero', aeval_C, Algebra.id.map_eq_id, RingHom.id_apply]
  · intro b hb hb0
    rw [aeval_monomial, Algebra.id.map_eq_id, RingHom.id_apply]
    convert MulZeroClass.mul_zero _
    obtain ⟨i, hi⟩ := finsupp.support_nonempty_iff.mpr hb0
    rw [Finsupp.prod]
    apply Finset.prod_eq_zero hi
    have hi' : 0 < i.fst := by
      apply mem_supported.mp hf
      rw [Finset.mem_coe, mem_vars]
      exact ⟨b, ⟨hb, hi⟩⟩
    rw [if_pos hi']
    exact zero_pow (zero_lt_iff.mpr (finsupp.mem_support_iff.mp hi))
  · intro hf'
    rw [monomial_zero', aeval_C, Algebra.id.map_eq_id, RingHom.id_apply, ←
      not_mem_support_iff.mp hf']
#align divided_power_algebra.coeff_zero_of_mem_aug_ideal DividedPowerAlgebra.coeff_zero_of_mem_augIdeal

theorem augIdeal_eq_span' : augIdeal R M = span (Set.image2 (dp R) {n : ℕ | 0 < n} ⊤) :=
  sorry
#align divided_power_algebra.aug_ideal_eq_span' DividedPowerAlgebra.augIdeal_eq_span'

-- TODO: is it better to use ⊤ or set.univ? Is it the same?
theorem
  augIdeal_eq_span :--  aug_ideal R M = span (set.image (λ nm, mk _ (X nm)) { nm : ℕ × M | 0 < nm.1 }) :=
        augIdeal
        R M =
      span (Set.image2 (dp R) {n : ℕ | 0 < n} Set.univ) :=
  by
  classical
  apply le_antisymm
  · intro f0 hf0
    obtain ⟨⟨f, hf⟩, rfl⟩ := DividedPowerAlgebra.surjective_of_supported R f0
    have hf0' : coeff 0 f = 0 := coeff_zero_of_mem_aug_ideal R M hf hf0
    simp only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply,
      SetLike.coe_mk] at hf0 ⊢
    rw [f.as_sum]; rw [map_sum]
    refine' Ideal.sum_mem _ _
    intro c hc
    rw [monomial_eq, Finsupp.prod]
    simp only [_root_.map_mul]
    refine' mul_mem_left _ _ _
    suffices supp_ss : ↑c.support ⊆ {nm : ℕ × M | 0 < nm.fst}
    · by_cases hc0 : c.support.nonempty
      · obtain ⟨⟨n, m⟩, hnm⟩ := hc0
        rw [Finset.prod_eq_mul_prod_diff_singleton hnm]
        simp only [_root_.map_mul, map_pow]
        apply
          mul_mem_right _ _
            (pow_mem_of_mem _ _ _ (Nat.pos_of_ne_zero (finsupp.mem_support_iff.mp hnm)))
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
    rw [← hf, mem_aug_ideal_iff, algebra_map_inv, lift_dp_eq]
    simp_rw [LinearMap.zero_apply]
    rw [DividedPowers.dpow_eval_zero _ (ne_of_gt hn)]
#align divided_power_algebra.aug_ideal_eq_span DividedPowerAlgebra.augIdeal_eq_span

theorem right_inv' [DecidableEq R] [DecidableEq M] (x : R) :
    (algebraMapInv R M) ((proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) x).val = x := by
  rw [proj'_zero_comp_algebra_map] <;> exact algebra_map_left_inverse R M x
#align divided_power_algebra.right_inv' DividedPowerAlgebra.right_inv'

theorem left_inv' [DecidableEq R] [DecidableEq M] (x : grade R M 0) :
    (proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)) ((algebraMapInv R M) x.val) = x :=
  by
  ext
  simp only [proj', proj, LinearMap.coe_mk, Function.comp_apply]
  conv_rhs => rw [← Subtype.val_eq_coe, ← DirectSum.decompose_of_mem_same _ x.2]
  rw [algebra_map_right_inv_of_degree_zero R M x]
#align divided_power_algebra.left_inv' DividedPowerAlgebra.left_inv'

theorem lift_augIdeal_le {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) :
    Ideal.map (lift R M hI φ hφ) (augIdeal R M) ≤ I :=
  by
  simp only [aug_ideal_eq_span, Ideal.map_span, Ideal.span_le, SetLike.mem_coe]
  rintro y ⟨x, ⟨n, m, hn, hm, rfl⟩, rfl⟩
  rw [lift_dp_eq]
  exact hI.dpow_mem (ne_of_gt hn) (hφ m)
#align divided_power_algebra.lift_aug_ideal_le DividedPowerAlgebra.lift_augIdeal_le

theorem lift_mem_of_mem_augIdeal {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A}
    (hI : DividedPowers I) (φ : M →ₗ[R] A) (hφ : ∀ m, φ m ∈ I) (x : DividedPowerAlgebra R M)
    (hx : x ∈ augIdeal R M) : lift R M hI φ hφ x ∈ I :=
  (lift_augIdeal_le R M hI φ hφ) (mem_map_of_mem _ hx)
#align divided_power_algebra.lift_mem_of_mem_aug_ideal DividedPowerAlgebra.lift_mem_of_mem_augIdeal

-- grade R M 0 → R is isomorphism
noncomputable def ringEquivDegreeZero [DecidableEq R] [DecidableEq M] : RingEquiv (grade R M 0) R
    where
  toFun x := algebraMapInv R M x.1
  invFun := proj' R M 0 ∘ algebraMap R (DividedPowerAlgebra R M)
  left_inv := left_inv' R M
  right_inv := right_inv' R M
  map_mul' x y := by rw [← _root_.map_mul] <;> rfl
  map_add' x y := by rw [← _root_.map_add] <;> rfl
#align divided_power_algebra.ring_equiv_degree_zero DividedPowerAlgebra.ringEquivDegreeZero

def proj0RingHom [DecidableEq R] [DecidableEq M] : RingHom (DividedPowerAlgebra R M) R
    where
  toFun := (ringEquivDegreeZero R M).toFun ∘ proj' R M 0
  map_one' := by rw [RingEquiv.toFun_eq_coe, MulEquivClass.map_eq_one_iff, proj'_zero_one]
  map_mul' x y := by
    rw [RingEquiv.toFun_eq_coe, Function.comp_apply, ← _root_.map_mul, proj'_zero_mul]
  map_zero' := by simp only [RingEquiv.toFun_eq_coe, Function.comp_apply, map_zero]
  map_add' := by
    simp only [RingEquiv.toFun_eq_coe, Function.comp_apply, map_add, eq_self_iff_true, forall_const]
#align divided_power_algebra.proj_0_ring_hom DividedPowerAlgebra.proj0RingHom

end GradeZero

section GradeOne

variable (R)

/-- The canonical map from `divided_power_algebra R M` into `triv_sq_zero_ext R M` that sends
`divided_power_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    DividedPowerAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R M
    (DividedPowers.OfSquareZero.dividedPowers (TrivSqZeroExt.square_zero R M) :
      DividedPowers (kerIdeal R M))
    (inrHom R M) fun m => (mem_kerIdeal_iff_exists R M _).mpr ⟨m, rfl⟩
#align divided_power_algebra.to_triv_sq_zero_ext DividedPowerAlgebra.toTrivSqZeroExt

@[simp]
theorem toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M) :
    toTrivSqZeroExt R M (ι R x) = inr x :=
  lift_ι_apply R _ _ _ x
#align divided_power_algebra.to_triv_sq_zero_ext_ι DividedPowerAlgebra.toTrivSqZeroExt_ι

theorem toTrivSqZeroExt_snd [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (m : M) :
    ((toTrivSqZeroExt R M) ((mkₐ R (relI R M)) (X (1, m)))).snd = m := by
  rw [← dp_eq_mkₐ, ← ι_def, to_triv_sq_zero_ext_ι] <;> rfl
#align divided_power_algebra.to_triv_sq_zero_ext_snd DividedPowerAlgebra.toTrivSqZeroExt_snd

theorem deg_one_left_inv [DecidableEq R] [DecidableEq M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    Function.LeftInverse (fun x : grade R M 1 => (toTrivSqZeroExt R M x.1).snd)
      (proj' R M 1 ∘ ι R) :=
  by
  intro m
  simp only [Function.comp_apply, Subtype.val_eq_coe, ι, dp, proj', proj, LinearMap.coe_mk]
  rw [← TrivSqZeroExt.snd_inr R m]
  apply congr_arg
  rw [snd_inr, ← to_triv_sq_zero_ext_ι, ι, LinearMap.coe_mk, dp,
    decompose_of_mem_same _ (mkₐ_mem_grade R M 1 m)]
#align divided_power_algebra.deg_one_left_inv DividedPowerAlgebra.deg_one_left_inv

theorem grade_one_eq_span (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq R]
    [DecidableEq M] : grade R M 1 = Submodule.span R (Set.range (dp R 1)) :=
  by
  apply le_antisymm
  · intro p hp
    obtain ⟨q, hq1, hqp⟩ := surjective_of_supported' R ⟨p, hp⟩
    rw [Subtype.val_eq_coe, Submodule.coe_mk] at hqp 
    rw [is_weighted_homogeneous, Subtype.val_eq_coe] at hq1 
    rw [← hqp, ← mkₐ_eq_mk R, (q : MvPolynomial (ℕ × M) R).as_sum, map_sum]
    apply Submodule.sum_mem (Submodule.span R (Set.range (dp R 1)))
    intro d hd
    have hsupp : ∀ nm : ℕ × M, nm ∈ d.support → 0 < nm.fst :=
      by
      intro nm hnm
      apply mem_supported.mp q.2
      rw [Subtype.val_eq_coe, mem_coe, mem_vars]
      exact ⟨d, hd, hnm⟩
    obtain ⟨m, hm⟩ := eq_finsupp_single_of_degree_one M (hq1 (mem_support_iff.mp hd)) hsupp
    rw [← hm, monomial_eq, C_mul', map_smul, Finsupp.prod_single_index, pow_one]
    exact
      Submodule.smul_mem (Submodule.span R (Set.range (dp R 1))) _
        (Submodule.subset_span (set.mem_range.mpr ⟨m, rfl⟩))
    · rw [pow_zero]
  · rw [Submodule.span_le]
    intro p hp
    obtain ⟨m, hm⟩ := set.mem_range.mp hp
    rw [← hm]
    exact dp_mem_grade R M 1 m
#align divided_power_algebra.grade_one_eq_span DividedPowerAlgebra.grade_one_eq_span

theorem grade_one_eq_span' (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq R]
    [DecidableEq M] :
    (⊤ : Submodule R (grade R M 1)) =
      Submodule.span R (Set.range fun m => ⟨dp R 1 m, dp_mem_grade R M 1 m⟩) :=
  by
  apply Submodule.map_injective_of_injective (grade R M 1).injective_subtype
  simp only [Submodule.map_subtype_top]
  rw [Submodule.map_span]
  simp_rw [grade_one_eq_span R M]
  rw [← Set.range_comp]; rfl
#align divided_power_algebra.grade_one_eq_span' DividedPowerAlgebra.grade_one_eq_span'

theorem deg_one_right_inv [DecidableEq R] [DecidableEq M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    Function.RightInverse
      (TrivSqZeroExt.sndHom R M ∘ (toTrivSqZeroExt R M).toLinearMap ∘ (grade R M 1).Subtype)
      (proj' R M 1 ∘ ι R) :=
  by
  --try with snd_hom , submodule.val
  simp only [Function.rightInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe R]
  rw [fun_like.coe_injective.eq_iff]
  apply LinearMap.ext_on_range (grade_one_eq_span' R M).symm
  intro m
  have hm : ((to_triv_sq_zero_ext R M) (dp R 1 m)).snd = m :=
    by
    rw [to_triv_sq_zero_ext, dp, mkₐ_eq_mk, lift, lift_aux, liftₐ_apply, lift_mk]
    simp only [inr_hom_apply, AlgHom.coe_toRingHom, eval₂_alg_hom_X']
    rw [DividedPowers.dpow_one _ ((mem_ker_ideal_iff_exists R M _).mpr ⟨m, rfl⟩), snd_inr]
  simp only [LinearMap.coe_comp, Submodule.coeSubtype, Function.comp_apply, Submodule.coe_mk,
    AlgHom.toLinearMap_apply, snd_hom_apply, LinearMap.id_coe, id.def, proj', proj,
    LinearMap.coe_mk, ι]
  ext
  rw [hm, decompose_of_mem_same _ (dp_mem_grade R M 1 m), Subtype.coe_mk]
#align divided_power_algebra.deg_one_right_inv DividedPowerAlgebra.deg_one_right_inv

-- ι : M → grade R M 1 is isomorphism
def linearEquivDegreeOne [DecidableEq R] [DecidableEq M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    LinearEquiv (RingHom.id R) M (grade R M 1)
    where
  toFun := (proj' R M 1).comp (ι R)
  invFun x := TrivSqZeroExt.sndHom R M (toTrivSqZeroExt R M x.1)
  map_add' x y := by simp only [map_add]
  map_smul' r x := by simp only [LinearMap.map_smulₛₗ]
  left_inv := deg_one_left_inv R M
  right_inv := deg_one_right_inv R M
#align divided_power_algebra.linear_equiv_degree_one DividedPowerAlgebra.linearEquivDegreeOne

end GradeOne

end DividedPowerAlgebra

