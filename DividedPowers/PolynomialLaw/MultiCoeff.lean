import DividedPowers.ForMathlib.Algebra.MvPolynomial.Lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Basic
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Pi
import DividedPowers.PolynomialLaw.Coeff

universe u

variable {R : Type u} [CommSemiring R]

namespace Module

open Finset LinearMap MvPolynomial TensorProduct

variable {ι N : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
  [(i : ι) → Module R (M i)] [AddCommMonoid N] [Module R N] [Fintype ι] [DecidableEq ι]

/-- `multiGenerize` is the `R`-linear map sending `m : Π i, M i` to the sum
  `∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i)) : MvPolynomial ι R ⊗[R] (Π i, M i)`. -/
noncomputable def multiGenerize : ((Π i, M i)) →ₗ[R] MvPolynomial ι R ⊗[R] (Π i, M i) where
  toFun m       := ∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i))
  map_add' p q  := by simp [Pi.single_add, tmul_add, sum_add_distrib]
  map_smul' r p := by simp [Pi.single_smul, Finset.smul_sum]

theorem multiGenerize_eq_generize (m : Π i, M i) :
    (multiGenerize m) = (generize (R := R) (fun (i : ι) ↦ Pi.single i (m i))) := by
  simp [generize, multiGenerize]

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- `multiGenerize` is the `S`-linear map that sends `s ⊗ₜ m : S ⊗[R] Π i, M i` to
  `∑ i, s • X i ⊗ₜ[R] Pi.single i (m i) : (MvPolynomial ι S) ⊗[R] Π i, M i`.  -/
noncomputable def multiGenerizeBaseChange :
    (S ⊗[R] Π i, M i) →ₗ[S] (MvPolynomial ι S) ⊗[R] Π i, M i where
  toFun sm := LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
    ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (piRight R S S _).symm (Pi.single i (piRight R S S _ sm i))))
  map_add' x y := by
    simp only [← map_add]
    congr
    simp_rw [map_add, Pi.add_def, Pi.single_add, map_add, tmul_add, Finset.sum_add_distrib]
  map_smul' s x := by
    simp only [map_smul, piRight_apply, Pi.smul_apply, map_sum, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.single_smul, map_smul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul, LinearEquiv.rTensor_tmul,
        AlgEquiv.toLinearEquiv_apply, smul_tmul', smul_eq_mul,
        scalarRTensorAlgEquiv, rTensorAlgHom, smul_eq_C_mul _ s, mul_left_comm (C s)]
    | add x y hx hy =>
      simp [Pi.single_add, smul_add, map_add, tmul_add, ← hx, ← hy]

lemma multiGenerizeBaseChange_apply_tmul (s : S) (m : Π i, M i) :
    multiGenerizeBaseChange (s ⊗ₜ[R] m) = ∑ i, s • X i ⊗ₜ[R] Pi.single i (m i) := by
  simp only [multiGenerizeBaseChange, map_sum]
  apply Finset.sum_congr rfl
  simp [smul_tmul', scalarRTensorAlgEquiv, rTensorAlgHom, mul_comm _ (C s), C_mul']

lemma multiGenerizeBaseChange_apply_eq (sm : S ⊗[R] Π i, M i) :
    multiGenerizeBaseChange sm = (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
        (∑ (i : ι), (X i) ⊗ₜ (TensorProduct.compRight R S S M i) sm))) := by
  simp only [multiGenerizeBaseChange, piRight_apply, map_sum, coe_mk, AddHom.coe_mk]
  congr
  ext i
  apply congr_arg₂ _ rfl
  induction sm using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp [Pi.single_add, tmul_add, ← hx, ← hy]

end Module

/- # Polynomial laws. -/

namespace PolynomialLaw

open Finset MvPolynomial TensorProduct

/- ## Multi-coefficients of polynomial laws. -/

section Coefficients

variable {ι N : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
  [AddCommMonoid N] [Module R N]

open LinearMap

section Decidable_Fintype

variable [Fintype ι] [DecidableEq ι]

section multiCoeff

open Module

variable (m : Π i, M i) (k : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)

/-- Given `m : Π i, M i`, `multiGenerize' m` is the `R`-linear map sending
`f : (Π i, M i) →ₚₗ[R] N` to the term of `MvPolynomial ι R ⊗[R] N` obtained by applying
`f.toFun (MvPolynomial ι R)` to the sum `∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i))`.
This is provided as an auxiliary map for the definition `PolynomialLaw.multiCoeff`. -/
noncomputable def multiGenerize' : ((Π i, M i) →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i : ι, X i ⊗ₜ[R] (Pi.single i (m i)))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

/-- The multi-coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def multiCoeff : ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (multiGenerize' m)

theorem multiCoeff_eq_coeff (m : Π i, M i) :
    multiCoeff m = coeff (R := R) (ι := ι) (N := N) (fun i ↦ Pi.single i (m i)) := by
  simp [multiCoeff, multiGenerize', coeff, generize', generize, coe_mk, AddHom.coe_mk]

theorem toFun_multiGenerize_eq : f.toFun (MvPolynomial ι R) (multiGenerize m)=
    (multiCoeff m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n) := by
  simp [multiCoeff_eq_coeff, multiGenerize_eq_generize, toFun_generize_eq]

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
    simp only [this, multiCoeff_eq_coeff, ground_apply_sum_smul, Finset.prod_pow_eq_pow_sum]
  simp [← Finset.smul_sum]
  congr
  ext i
  simp

variable {S : Type*} [CommSemiring S] [Algebra R S] {m}

theorem multiCoeff_injective (hm : Submodule.span R (Set.range fun i ↦ Pi.single i (m i)) = ⊤) :
    Function.Injective (multiCoeff m : ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N) := fun f g h ↦ by
  simp only [multiCoeff_eq_coeff] at h
  exact coeff_injective hm h

theorem multiCoeff_inj (hm : Submodule.span R (Set.range fun i ↦ Pi.single i (m i)) = ⊤)
    {f g : (Π i, M i) →ₚₗ[R] N} : (multiCoeff m f) = (multiCoeff m g ) ↔ f = g :=
  (multiCoeff_injective hm).eq_iff

open Module

variable (sm : S ⊗[R] Π i, M i)

/-- The multi-coefficients of a polynomial law, after base change, as a `Finsupp`. -/
noncomputable def multiCoeffBaseChange : (ι →₀ ℕ) →₀ S ⊗[R] N :=
  finsuppLeft R S N _ (f.toFun _ (multiGenerizeBaseChange sm))

theorem multiGenerize_eq_sum_multiCoeffBaseChange :
    f.toFun _ (multiGenerizeBaseChange sm) = (f.multiCoeffBaseChange sm).sum
      (fun k ↦ AlgebraTensorModule.map (monomial k) LinearMap.id) := by
  simp only [multiCoeffBaseChange]
  set sn := finsuppLeft R S N _ (f.toFun _ (multiGenerizeBaseChange sm)) with hsn
  rw [← LinearEquiv.symm_apply_eq] at hsn
  rw [← hsn, finsuppLeft_symm_apply_eq_sum]

lemma multiCoeffBaseChange_apply' : multiCoeffBaseChange f sm = MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (multiGenerizeBaseChange sm)) := by
  ext k
  simp only [multiCoeffBaseChange]
  rw [multiGenerize_eq_sum_multiCoeffBaseChange]
  rfl

lemma multiCoeffBaseChange_apply :
    multiCoeffBaseChange f sm = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
        ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
          (∑ (i : ι), (X i) ⊗ₜ (TensorProduct.compRight R S S M i) sm)))) := by
  rw [multiCoeffBaseChange_apply', multiGenerizeBaseChange_apply_eq]

variable (m)

lemma multiCoeffBaseChange_apply_tmul (s : S) :
    multiCoeffBaseChange f (s ⊗ₜ m) k = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (s ⊗ₜ (Pi.single i (m i))))))) k := by
  rw [multiCoeffBaseChange_apply]
  congr
  simp [TensorProduct.compRight, singleRight, projRight]

variable (s : Π (_ : ι), S) (m : Π i, M i)

lemma multiCoeffBaseChange_apply_smul [Nontrivial R] (s : Π _, S) :
    multiCoeffBaseChange f (∑ i, s i • (TensorProduct.compRight R S S M i) sm) k =
      (∏ i, s i ^ k i) • multiCoeffBaseChange f sm k := by
  let ψ := ((aeval (R := S) (fun i ↦ (C (s i) * X i : MvPolynomial ι S))).restrictScalars R)
  suffices ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (∑ i, X i ⊗ₜ[R] (TensorProduct.compRight R S S M i)
            (∑ i, s i • (TensorProduct.compRight R S S M i) sm))))  =
      ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap)
        ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (∑ i, X i ⊗ₜ[R] (TensorProduct.compRight R S S M i) sm)))) by
    simp only [multiCoeffBaseChange_apply, this, ← f.isCompat_apply]
    clear this
    generalize ht : (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i, X i ⊗ₜ[R] (TensorProduct.compRight R S S M i) sm)))) = t
    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (∏ i, s i ^ k i)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    rw [eq_comm]
    dsimp only [LinearMap.rTensor, TensorProduct.map]
    apply lift.unique
    intro f k
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, lift.tmul,
      lcoeff_apply, mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply, smul_tmul']
    apply congr_arg₂ _ _ rfl
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | monomial k' a =>
        simp only [ψ, coeff_monomial]
        split_ifs with h
        · rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial,
           algebraMap_eq, coeff_C_mul, Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_pos rfl]
          simp
        · simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, algebraMap_eq]
          rw [coeff_C_mul, Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_neg h]
          simp
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearEquiv.rTensor_apply, AlgEquiv.toLinearEquiv_toLinearMap, ← rTensor_comp_apply]
  induction sm using TensorProduct.induction_on with
  | zero => simp [map_zero, smul_zero, Finset.sum_const_zero, tmul_zero]
  | tmul t m =>
    simp only [compRight_tmul, ← map_smul, compRight_singleRight]
    simp only [map_smul, singleRight_tmul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      assoc_symm_tmul, rTensor_tmul, coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    rw [smul_tmul', TensorProduct.assoc_symm_tmul]
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_toLinearMap, smul_eq_mul, rTensor_tmul,
      coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply, AlgEquiv.trans_apply, AlgHom.coe_restrictScalars', ψ]
    congr
    simp only [rTensorAlgHom_apply_eq, rTensor_apply_tmul, Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X i) := rfl
    simp only [this, support_X, Finset.mem_singleton] at hd
    simp only [hd, MvPolynomial.aeval_def, algebraMap_eq, eval₂_map]
    simp only [eval₂, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Finsupp.prod_pow,
      map_zero, zero_mul, Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul, X,
      ← single_eq_monomial, Finsupp.single_eq_same, _root_.one_smul]
    rw [Finset.prod_eq_single i (fun _ _ hj ↦ by rw [Finsupp.single_eq_of_ne (Ne.symm hj),
      pow_zero]) (fun hj ↦ absurd (Finset.mem_univ _) hj)]
    simp [single_eq_monomial, mul_comm (s i) t, C_mul_monomial,]
  | add sm sm' h h' => simp only [map_add, smul_add, Finset.sum_add_distrib, tmul_add, h, h']

lemma multiCoeffBaseChange_def :
    multiCoeffBaseChange f sm = (MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (∑ x, (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
        ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
          (X x ⊗ₜ[R] (TensorProduct.compRight R S S M x sm)))))) := by
  ext n
  simp [multiCoeffBaseChange_apply, map_sum]

variable {S' : Type*} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S')

theorem multiGenerizeBaseChange_rTensor :
    multiGenerizeBaseChange ((LinearMap.rTensor ((i : ι) → M i) φ.toLinearMap) sm) =
      LinearMap.rTensor _ (mapAlgHom φ).toLinearMap (multiGenerizeBaseChange sm) := by
  induction sm using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>  simp [rTensor_tmul, multiGenerizeBaseChange_apply_tmul, smul_tmul',
      smul_eq_C_mul, mapAlgHom_apply]
  | add x y hx hy => simp [map_add, ← hx, ← hy]

theorem rTensor_multiCoeffBaseChange_eq :
    (LinearMap.rTensor N φ.toLinearMap) (multiCoeffBaseChange f sm k) =
      multiCoeffBaseChange f ((LinearMap.rTensor ((i : ι) → M i) φ.toLinearMap) sm) k := by
  simp [multiCoeffBaseChange, multiGenerizeBaseChange_rTensor, ← f.isCompat_apply,
    rTensor_finsuppLeft_eq]

end Decidable_Fintype

end Coefficients

end PolynomialLaw
