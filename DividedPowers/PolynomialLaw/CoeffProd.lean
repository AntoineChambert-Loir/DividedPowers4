import DividedPowers.ForMathlib.RingTheory.SubmoduleMem
import DividedPowers.PolynomialLaw.Coeff
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Prod

universe u

variable (R : Type u) [CommSemiring R]

/- # Prerequisites. -/

/- # Polynomial laws. -/

namespace PolynomialLaw

variable {R}

/- **MI** : The file now works assuming the weaker hypotheses `CommSemiring R`, `CommSemiring S`,
  `AddCommMonoid M`, `AddCommMonoid N`. -/

open Finset MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {M M' N ι : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N]

section Fintype

open LinearMap

variable [Fintype ι]

section generize

/-- Given `m : ι → M × M'`, `generizeFst m` is the `R`-linear map sending
`f : M × M' →ₚₗ[R] N` to the term of `MvPolynomial ι R ⊗[R] N` obtained by applying
`f.toFun (MvPolynomial ι R)` to the
sum `∑ i, X i ⊗ₜ[R] ((m i).1, 0)`. -/
noncomputable def generizeFst (m : ι → M × M') :
    (M × M' →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] ((m i).1, 0))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

noncomputable def generizeSnd (m : ι → M × M') :
    (M × M' →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] (0, (m i).2))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

end generize

section coeff

variable [DecidableEq ι] (m : ι → M × M') (k : ι →₀ ℕ) (f : M × M' →ₚₗ[R] N)

/-- The coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def coeffFst : (M × M' →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (generizeFst m)

noncomputable def coeffSnd : (M × M' →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (generizeSnd m)

theorem generizeFst_eq : generizeFst m f =
    (coeffFst m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n)  := by
  dsimp only [coeffFst, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize h : scalarRTensor (generizeFst m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h, LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d (fun _ _ hb ↦ by simp [if_neg hb,
    scalarRTensor_apply_tmul_apply]) (by simp), scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul]

theorem generizeSnd_eq : generizeSnd m f =
    (coeffSnd m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n)  := by
  dsimp only [coeffSnd, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize h : scalarRTensor (generizeSnd m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h, LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d (fun _ _ hb ↦ by simp [if_neg hb,
    scalarRTensor_apply_tmul_apply]) (by simp), scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul]

theorem coeffFst_eq :
  coeffFst m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] ((m i).1, 0)))) := by
  rw [coeffFst, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _

theorem coeffSnd_eq :
  coeffSnd m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] (0, (m i).2)))) := by
  rw [coeffSnd, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _

open TensorProduct

-- TODO: rename, if it works
theorem toFun_sum_tmul_eq_coeff_sum' (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S × S) :
    f.toFun S (∑ i, ((prodRight R S S M M').symm
      ((r i).1 ⊗ₜ[R] (m i).1, (r i).2 ⊗ₜ[R] (m i).2))) =
      (coeffFst m f).sum (fun k n ↦ (∏ i, (r i).1 ^ k i) ⊗ₜ[R] n) +
      (coeffSnd m f).sum (fun k n ↦ (∏ i, (r i).2 ^ k i) ⊗ₜ[R] n) := by
  have := (f.isCompat (MvPolynomial.aeval (fun i ↦ (r i).1)))
   -- (∑ i, X i ⊗ₜ[R] ((m i).1, 0))
  have hc := congr_fun (f.isCompat (MvPolynomial.aeval (fun i ↦ (r i).1)))
    (∑ i, X i ⊗ₜ[R] ((m i).1, 0))
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at hc
  set g := generizeFst m f + generizeSnd m f with hg
  let h := generizeFst_eq m f
  let h' := generizeSnd_eq m f
  simp only [generizeFst, coe_mk, AddHom.coe_mk] at h
  simp only [generizeSnd, coe_mk, AddHom.coe_mk] at h'
  have : f.toFun S (∑ i, (prodRight R S S M M').symm
      ((r i).1 ⊗ₜ[R] (m i).1, (r i).2 ⊗ₜ[R] (m i).2)) =
      f.toFun S (∑ i, (prodRight R S S M M').symm
      ((r i).1 ⊗ₜ[R] (m i).1, 0)) +
      f.toFun S (∑ i, (prodRight R S S M M').symm
      (0, (r i).2 ⊗ₜ[R] (m i).2)) := by
    sorry
  have foo : ∑ i, (prodRight R S S M M').symm ((r i).1 ⊗ₜ[R] (m i).1, 0) =
    ∑ i, (r i).1 ⊗ₜ[R] ((m i).1, 0) := sorry
  rw [this, foo, ← hc]

  sorry
  /- rw [← hc, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul] -/

end coeff

#exit

end Fintype

open Function

/-- Variant of `toFun_sum_tmul_eq_coeff_sum` over a Finset -/
theorem toFun_sum_tmul_eq_coeff_finset_sum [DecidableEq ι] (m : ι → M) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) (s : Finset ι) :
    f.toFun S (∑ i ∈ s, r i ⊗ₜ[R] m i) = (coeff (fun i : s ↦ m i) f).sum
      (fun k n ↦ (∏ i ∈ s, r i ^ ((Function.extend (fun x ↦ x.val) k (const ι 0)) i)) ⊗ₜ[R] n) := by
  convert toFun_sum_tmul_eq_coeff_sum (fun (i : s) ↦ m i) f S fun (i : s) ↦ r i
  · rw [univ_eq_attach, ← sum_attach]
  · rw [univ_eq_attach, ← prod_attach]
    exact prod_congr rfl (fun _ _ ↦ congr_arg₂ _ rfl (Subtype.coe_injective.extend_apply _ _ _))

-- Useful ?
/-- Variant of `toFun_sum_tmul_eq_coeff_sum` with a `Finsupp`-/
theorem toFun_sum_tmul_eq_coeff_finsupp_sum [DecidableEq ι] (m : ι → M) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι →₀ S) :
    f.toFun S (r.sum fun i a ↦ a ⊗ₜ[R] m i) = (coeff (fun i : r.support ↦ m i) f).sum
      (fun k n ↦ (∏ i ∈ r.support,
        (r i ^ ((Function.extend (fun x ↦ x.val) k (const ι 0)) i))) ⊗ₜ[R] n) := by
  rw [Finsupp.sum, toFun_sum_tmul_eq_coeff_finset_sum]

section Fintype

variable [Fintype ι]

section Decidable_Fintype

variable [DecidableEq ι] (f : M →ₚₗ[R] N) (m : ι → M) (r : ι → R) (r₁ r₂ : R) (m₁ m₂ : M)

theorem ground_apply_sum_smul :
    ground f (∑ i, (r i) • (m i)) = (coeff m f).sum (fun k n ↦ (∏ i,  r i ^ k i) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_sum, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ ↦ by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])

theorem ground_apply_smul :
    ground f (r₁ • m₁) = (coeff (const Unit m₁) f).sum (fun k n ↦ r₁ ^ (k 0) • n) := by
  suffices r₁ • m₁ = ∑ i, (const Unit r₁) i • (const Unit m₁ i) by
    rw [this, ground_apply_sum_smul]
    exact sum_congr rfl (fun i _ ↦ by simp)
  simp

theorem ground_apply_add_smul : ground f (r₁ • m₁ + r₂ • m₂) =
      (coeff (R := R) (![m₁, m₂]) f).sum fun k n ↦ (∏ i, (![r₁, r₂]) i ^ (k i)) • n := by
  suffices r₁ • m₁ + r₂ • m₂ = ∑ i, (![r₁, r₂]) i • (![m₁, m₂]) i  by
    rw [this, ground_apply_sum_smul]
  simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]

variable {S : Type*} [CommSemiring S] [Algebra R S]

theorem coeff_injective {m : ι → M} (hm : Submodule.span R (Set.range m) = ⊤) :
    Function.Injective (coeff m : (M →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N) := fun f g h ↦ by
  ext S _ _ p
  suffices hp : p ∈ Submodule.span S (Set.range fun s ↦ 1 ⊗ₜ[R] m s) by
    simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
    obtain ⟨r, rfl⟩ := hp
    rw [Finsupp.sum_of_support_subset _ (subset_univ _) _ (fun  i _ ↦ by
      rw [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul])]
    simp [smul_eq_mul, mul_one, ← toFun_eq_toFun'_apply, toFun_sum_tmul_eq_coeff_sum, h]
  simp [Submodule.span_tensorProduct_eq_top_of_span_eq_top m hm]

theorem coeff_inj {m : ι → M} (hm : Submodule.span R (Set.range m) = ⊤)
    {f g : M →ₚₗ[R] N} : coeff m f = coeff m g ↔ f = g := (coeff_injective hm).eq_iff

end Decidable_Fintype

end Fintype

end Coefficients

end PolynomialLaw


namespace Finsupp

open Finset MvPolynomial PolynomialLaw TensorProduct

variable {R} {M N ι : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (S : Type*) [CommSemiring S] [Algebra R S]

/- When M is free, we can go in the other direction and construct,
  from a basis `b` of `M` and `N`-valued polynomials, a polynomial law. -/
variable (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) (m : S ⊗[R] M)

section Fintype

variable [Fintype ι]

-- BP
/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ`, `Finsupp.polynomialLaw b h : M →ₚₗ[R] N` is
the polynomial map whose coefficients at `b` are given by `h`. -/
noncomputable def polynomialLaw : M →ₚₗ[R] N where
  toFun' S _ _ x := h.sum fun k n ↦ (∏ i, (LinearForm.baseChange R S _ (b.coord i)) x ^ k i) ⊗ₜ[R] n
  isCompat' φ   := by
    ext m
    rw [Function.comp_apply, sum, _root_.map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    apply congr_arg₂ _ _ rfl
    rw [map_prod φ]
    apply Finset.prod_congr rfl (fun _ _ ↦ ?_)
    rw [map_pow]
    exact congr_arg₂ _ (by rw [LinearForm.baseChange_compat_apply]) rfl

theorem polynomialLaw_toFun_apply : (polynomialLaw b h).toFun S m =
    h.sum fun k n ↦ (∏ i, (LinearForm.baseChange R S _ (b.coord i)) m ^ k i) ⊗ₜ[R] n := by
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  simp only [← isCompat_apply, toFun_eq_toFun', polynomialLaw, map_finsuppSum]
  apply sum_congr
  intro k _
  rw [LinearMap.rTensor_tmul]
  congr
  simp only [AlgHom.toLinearMap_apply, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro i _
  apply congr_arg₂ _ _ rfl
  rw [LinearForm.baseChange_compat_apply]

open LinearMap

theorem generize_polynomialLaw_eq_sum :
    ((generize ⇑b) (polynomialLaw b h)) = sum h (fun k n ↦ (monomial k 1) ⊗ₜ[R] n) := by
  classical
  set m := ∑ i, (X i : MvPolynomial ι R) ⊗ₜ[R] b i with hm
  rw [generize, LinearMap.coe_mk, AddHom.coe_mk, polynomialLaw_toFun_apply]
  have : ∀ i, (LinearForm.baseChange R (MvPolynomial ι R) M (Basis.coord b i)) m = X i := fun i ↦ by
    rw [hm, map_sum, Finset.sum_eq_single i, LinearForm.baseChange_apply_tmul, Basis.coord_apply,
      Basis.repr_self, single_eq_same, _root_.one_smul, mul_one]
    · intro j _ hj
      rw [LinearForm.baseChange_apply_tmul, Basis.coord_apply, Basis.repr_self,
        Algebra.mul_smul_comm, mul_one, single_smul, one_smul, single_eq_of_ne hj]
    · simp
  simp only [← hm, this]
  apply sum_congr (fun k _ ↦ ?_)
  congr
  rw [← MvPolynomial.prod_X_pow_eq_monomial, ← prod_mul_prod_compl k.support]
  convert mul_one _
  apply prod_eq_one
  intro i hi
  rw [mem_compl, mem_support_iff, ne_eq, not_not] at hi
  rw [hi, pow_zero]

/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ,
  `Finsupp.polynomialLaw b h : M →ₚₗ[R] N` is the polynomial map
  whose coefficients at `b` are given by `h` -/
theorem coeff_polynomialLaw [DecidableEq ι] :
    coeff (DFunLike.coe b) (polynomialLaw b h) = h := by
  simp only [PolynomialLaw.coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  ext d
  rw [scalarRTensor_apply, eq_comm, ← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply,
    generize_polynomialLaw_eq_sum, map_finsuppSum, sum_eq_single d
    (fun b _ hb ↦ by rw [rTensor_tmul, lcoeff_apply, coeff_monomial, if_neg hb, zero_tmul])
    (fun _ ↦ by rw [tmul_zero, map_zero]), rTensor_tmul, lcoeff_apply, coeff_monomial, if_pos rfl]

theorem polynomialLaw_of_coeff [DecidableEq ι] (f : M →ₚₗ[R] N) :
    polynomialLaw b (coeff (DFunLike.coe b) f) = f :=
  (coeff_inj (eq_top_iff.mpr (fun m _ ↦ Submodule.span_mono
    (Set.image_subset_range _ _) (Basis.mem_span_repr_support b m)))).mp (coeff_polynomialLaw _ _)

noncomputable def polynomialLawEquivCoeff : ((ι →₀ ℕ) →₀ N) ≃ₗ[R] (M →ₚₗ[R] N) where
  toFun h      := polynomialLaw b h
  map_add' h k := by
    classical
    ext S _ _ m
    simp only [← toFun_eq_toFun', add_toFun, polynomialLaw_toFun_apply, Pi.add_apply]
    rw [sum_of_support_subset h (h.support.subset_union_left), sum_of_support_subset k
      (h.support.subset_union_right), sum_of_support_subset (h + k) support_add]
    simp_rw [coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [sum_add_distrib]
    all_goals intro i _hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    ext S _ _ m
    simp only [← toFun_eq_toFun', RingHom.id_apply, smul_toFun, Pi.smul_apply,
      polynomialLaw_toFun_apply]
    rw [sum_of_support_subset (a • h) support_smul _ (fun k _ ↦ by rw [TensorProduct.tmul_zero]),
      sum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [coe_smul, Pi.smul_apply, tmul_smul])
  invFun f    := by classical exact coeff (DFunLike.coe b) f
  left_inv h  := by dsimp; rw [coeff_polynomialLaw]
  right_inv f := by classical dsimp; rw [polynomialLaw_of_coeff b]

end Fintype

end Finsupp
