import DividedPowers.PolynomialLaw.Coeff
import DividedPowers.PolynomialLaw.BaseChange

universe u

variable (R : Type u) [CommSemiring R]

/- # Polynomial laws. -/

namespace PolynomialLaw

variable {R}

/- **MI** : The file now works assuming the weaker hypotheses `CommSemiring R`, `CommSemiring S`,
  `AddCommMonoid M`, `AddCommMonoid N`. -/

open Finset MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {ι N : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
  [(i : ι) → Module R (M i)] [AddCommMonoid N] [Module R N]

section Fintype

open LinearMap

section Decidable_Fintype

variable [Fintype ι] [DecidableEq ι]

section multiGenerize

/-- Given `m : ι → Π i, M i`, `generize m` is the `R`-linear map sending `f : (Π i, M i) →ₚₗ[R] N`
to the term of `MvPolynomial ι R ⊗[R] N` obtained by applying `f.toFun (MvPolynomial ι R)` to the
sum `∑ i, X i ⊗ₜ[R] m i`. -/
noncomputable def multiGenerize (m : Π i, M i) :
    ((Π i, M i) →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i))) -- ? Use linear combination
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

theorem multiGenerize_eq_generize (m : Π i, M i) :
    multiGenerize (R := R) (N := N) m = generize (fun (i : ι)  ↦ Pi.single i (m i)) := by
  simp [generize, multiGenerize]

end multiGenerize

section multiCoeff

variable (m : Π i, M i) (k : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)

/-- The multi-coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def multiCoeff :
    ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (multiGenerize m)

include M N R in
theorem multiCoeff_eq_coeff (m : Π i, M i) :
    multiCoeff  (R := R) (N := N) m = coeff (R := R) (ι := ι) (M := Π i, M i)  (N := N)
        (fun i ↦ Pi.single i (m i)) := by
  simp only [multiCoeff, coeff, multiGenerize_eq_generize]

theorem multiGenerize_eq : multiGenerize m f =
    (multiCoeff m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n) := by
  simp only [multiCoeff_eq_coeff, multiGenerize_eq_generize]
  simp only [generize_eq]
/-  dsimp only [multiCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize h : scalarRTensor (multiGenerize m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h, LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d (fun _ _ hb ↦ by simp [if_neg hb,
    scalarRTensor_apply_tmul_apply]) (by simp), scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul] -/

theorem multiCoeff_eq :
  multiCoeff m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] (Pi.single i (m i))))) := by
  rw [multiCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _

theorem toFun_sum_tmul_eq_multiCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) :
    f.toFun S (∑ i, r i ⊗ₜ[R] (Pi.single i (m i))) =
      (multiCoeff m f).sum (fun k n ↦ (∏ i, r i ^ k i) ⊗ₜ[R] n) := by
  simp only [multiCoeff_eq_coeff, toFun_sum_tmul_eq_coeff_sum]
  /- have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] (Pi.single i (m i)))
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := multiGenerize_eq m f
  simp only [multiGenerize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul] -/

theorem toFun_tmul_eq_multiCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) (i : ι) :
    f.toFun S (r ⊗ₜ[R] (Pi.single i (m i))) =
      ((multiCoeff (Pi.single i (m i)) f).sum fun k n ↦ (∏ i, r ^ k i) ⊗ₜ[R] n) := by
  simp only [multiCoeff_eq_coeff]
  have : r ⊗ₜ[R] Pi.single i (m i) =
      ∑ (j : ι), r ⊗ₜ[R] Pi.single j (Pi.single i (m i) j) := by
    rw [← tmul_sum, eq_comm]
    congr
    rw [Finset.sum_eq_single i (fun _ _ hj ↦ by rw [Pi.single_eq_of_ne hj, Pi.single_zero])
      (fun hi ↦ absurd (mem_univ i) hi),
      Pi.single_eq_same]
  rw [this]
  -- rw [toFun_sum_tmul_eq_multiCoeff_sum]
  rw [toFun_sum_tmul_eq_coeff_sum]

end multiCoeff

open Function

variable (r : ι → R) (r₁ r₂ : R) (m m₁ m₂ : Π i, M i) (k : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)

theorem ground_apply_sum_smul_eq_multiCoeff_sum :
    ground f (∑ i, (r i) • Pi.single i (m i)) =
      (multiCoeff m f).sum (fun k n ↦ (∏ i,  r i ^ k i) • n) := by
  simp [multiCoeff_eq_coeff, ground_apply_sum_smul]
/-
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_sum, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ ↦ by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])
-/

theorem ground_apply_smul_eq_multiCoeff_sum :
    ground f (r₁ • m₁) = (multiCoeff m₁ f).sum (fun k n ↦ r₁ ^ (∑ i, k i) • n) := by
  suffices r₁ • m₁ = ∑ i, r₁ • (Pi.single i (m₁ i)) by
    simp only [this, multiCoeff_eq_coeff, ground_apply_sum_smul,
      Finset.prod_pow_eq_pow_sum]
/-  suffices r₁ • m₁ = ∑ i, r₁ • (Pi.single i (m₁ i)) by
    rw [this, ground_apply_sum_smul_eq_multiCoeff_sum]
    exact sum_congr rfl (fun i _ ↦ by simp [Finset.prod_pow_eq_pow_sum]) -/
  simp [← Finset.smul_sum]
  congr
  ext i
  simp only [Finset.sum_apply, sum_pi_single, mem_univ, ↓reduceIte]

variable {S : Type*} [CommSemiring S] [Algebra R S]

theorem multiCoeff_injective {m : Π i, M i}
    (hm : Submodule.span R (Set.range fun i ↦ Pi.single i (m i)) = ⊤) :
    Function.Injective (multiCoeff m : ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N) := fun f g h ↦ by
  classical
  simp only [multiCoeff_eq_coeff] at h
  apply coeff_injective hm h
/-
  ext S _ _ p
  suffices hp : p ∈ Submodule.span S (Set.range fun i ↦ 1 ⊗ₜ[R] Pi.single i (m i)) by
    simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
    obtain ⟨r, rfl⟩ := hp
    rw [Finsupp.sum_of_support_subset _ (subset_univ _) _ (fun  i _ ↦ by
      rw [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul])]
    simp [smul_eq_mul, mul_one, ← toFun_eq_toFun'_apply, toFun_sum_tmul_eq_multiCoeff_sum, h]
  simp [Submodule.span_tensorProduct_eq_top_of_span_eq_top _ hm]
-/

theorem multiCoeff_inj {m : Π i, M i}
    (hm : Submodule.span R (Set.range fun i ↦ Pi.single i (m i)) = ⊤)
    {f g : (Π i, M i) →ₚₗ[R] N} :
    (multiCoeff m f) = (multiCoeff m g ) ↔ f = g :=
  (multiCoeff_injective hm).eq_iff

end Decidable_Fintype

end Fintype

end Coefficients

end PolynomialLaw
