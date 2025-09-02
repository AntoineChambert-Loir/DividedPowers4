import DividedPowers.PolynomialLaw.Coeff

universe u

variable (R : Type u) [CommSemiring R]

/- # Polynomial laws. -/

namespace PolynomialLaw

variable {R}

open Finset MvPolynomial TensorProduct

/- ## Multi-coefficients of polynomial laws. -/

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
noncomputable def _root_.Module.multiGenerize :
    ((Π i, M i)) →ₗ[R] MvPolynomial ι R ⊗[R] (Π i, M i) where
  toFun m       := (∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i)))
  map_add' p q  := by simp [Pi.single_add, tmul_add, sum_add_distrib]
  map_smul' r p := by simp [ Pi.single_smul, Finset.smul_sum]

/-- Given `m : ι → Π i, M i`, `generize m` is the `R`-linear map sending `f : (Π i, M i) →ₚₗ[R] N`
to the term of `MvPolynomial ι R ⊗[R] N` obtained by applying `f.toFun (MvPolynomial ι R)` to the
sum `∑ i, X i ⊗ₜ[R] m i`. -/
noncomputable def multiGenerize' (m : Π i, M i) :
    ((Π i, M i) →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i)))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

open Module in
theorem multiGenerize_eq_generize (f : ((Π i, M i) →ₚₗ[R] N)) (m : Π i, M i) :
    f.toFun (MvPolynomial ι R) (multiGenerize m) =
    f.toFun (MvPolynomial ι R) (generize (fun (i : ι) ↦ Pi.single i (m i))) := by
  simp [generize, multiGenerize]

end multiGenerize

section multiCoeff

open Module

variable (m : Π i, M i) (k : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)

/-- The multi-coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def multiCoeff :
    ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (multiGenerize' m)

theorem multiCoeff_eq_coeff (m : Π i, M i) :
    multiCoeff m = coeff (R := R) (ι := ι) (N := N) (fun i ↦ Pi.single i (m i)) := by
  simp [multiCoeff, multiGenerize', coeff, generize', generize, coe_mk, AddHom.coe_mk]

theorem multiGenerize_eq : f.toFun (MvPolynomial ι R) (multiGenerize m)=
    (multiCoeff m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n) := by
  simp [multiCoeff_eq_coeff, multiGenerize_eq_generize, generize_eq]

theorem multiCoeff_eq :
  multiCoeff m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] (Pi.single i (m i))))) := by
  rw [multiCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _

theorem toFun_sum_tmul_eq_multiCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) :
    f.toFun S (∑ i, r i ⊗ₜ[R] (Pi.single i (m i))) =
      (multiCoeff m f).sum (fun k n ↦ (∏ i, r i ^ k i) ⊗ₜ[R] n) := by
  simp [multiCoeff_eq_coeff, toFun_sum_tmul_eq_coeff_sum]

theorem toFun_tmul_eq_multiCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) (i : ι) :
    f.toFun S (r ⊗ₜ[R] (Pi.single i (m i))) =
      ((multiCoeff (Pi.single i (m i)) f).sum fun k n ↦ (∏ i, r ^ k i) ⊗ₜ[R] n) := by
  simp only [multiCoeff_eq_coeff]
  have : r ⊗ₜ[R] Pi.single i (m i) = ∑ (j : ι), r ⊗ₜ[R] Pi.single j (Pi.single i (m i) j) := by
    rw [← tmul_sum, eq_comm]
    congr
    rw [Finset.sum_eq_single i (fun _ _ hj ↦ by rw [Pi.single_eq_of_ne hj, Pi.single_zero])
      (fun hi ↦ absurd (mem_univ i) hi),
      Pi.single_eq_same]
  rw [this, toFun_sum_tmul_eq_coeff_sum]

end multiCoeff

open Function

variable (r : ι → R) (r₁ r₂ : R) (m m₁ m₂ : Π i, M i) (k : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)

theorem ground_apply_sum_smul_eq_multiCoeff_sum :
    ground f (∑ i, (r i) • Pi.single i (m i)) =
      (multiCoeff m f).sum (fun k n ↦ (∏ i,  r i ^ k i) • n) := by
  simp [multiCoeff_eq_coeff, ground_apply_sum_smul]

theorem ground_apply_smul_eq_multiCoeff_sum :
    ground f (r₁ • m₁) = (multiCoeff m₁ f).sum (fun k n ↦ r₁ ^ (∑ i, k i) • n) := by
  suffices r₁ • m₁ = ∑ i, r₁ • (Pi.single i (m₁ i)) by
    simp only [this, multiCoeff_eq_coeff, ground_apply_sum_smul,
      Finset.prod_pow_eq_pow_sum]
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
  exact coeff_injective hm h

theorem multiCoeff_inj {m : Π i, M i}
    (hm : Submodule.span R (Set.range fun i ↦ Pi.single i (m i)) = ⊤)
    {f g : (Π i, M i) →ₚₗ[R] N} :
    (multiCoeff m f) = (multiCoeff m g ) ↔ f = g :=
  (multiCoeff_injective hm).eq_iff

end Decidable_Fintype

end Fintype

end Coefficients

end PolynomialLaw
