import DividedPowers.ForMathlib.Algebra.Algebra.Bilinear
import DividedPowers.ForMathlib.Algebra.BigOperators.Group.Finset.Basic
import DividedPowers.ForMathlib.RingTheory.SubmoduleMem
import DividedPowers.ForMathlib.RingTheory.TensorProduct.Basic
import DividedPowers.ForMathlib.RingTheory.TensorProduct.MvPolynomial
import DividedPowers.PolynomialLaw.Basic2

universe u

variable {R : Type u} [CommSemiring R]

/- # Polynomial laws. -/

namespace PolynomialLaw

/- **MI** : The file now works assuming the weaker hypotheses `CommSemiring R`, `CommSemiring S`,
  `AddCommMonoid M`, `AddCommMonoid N`. -/

open Finset MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {M N ι : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section Fintype

open LinearMap

variable [Fintype ι]

section generize

/-- Given `m : ι → M`, `generize m` is the `R`-linear map sending `f : M →ₚₗ[R] N` to the
term of `MvPolynomial ι R ⊗[R] N` obtained by applying `f.toFun (MvPolynomial ι R)` to the
sum `∑ i, X i ⊗ₜ[R] m i`. -/
noncomputable def generize (m : ι → M) :
    (M →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i)
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

variable {S : Type*} [CommSemiring S] [Algebra R S]
/-- Given `m : ι → M` and `s : ι → S`, `generize' m s` is the `R`-linear map sending `f : M →ₚₗ[R] N` to the
term of `MvPolynomial ι S ⊗[R] N` obtained by applying `f.toFun (MvPolynomial ι R)` to the
sum `∑ i, s i • X i ⊗ₜ[R] m i`. -/
noncomputable def generize' (m : ι → M) (s : ι → S) :
    (M →ₚₗ[R] N) →ₗ[R] MvPolynomial ι S ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι S) (∑ i, s i • X i ⊗ₜ[R] m i)
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

theorem generize'_eq_generize (m : ι → M) (s : ι → S) (f : M →ₚₗ[R] N) :
    generize' m s f =
      (aeval (R := R) fun i ↦ s i • X (R := S) i).toLinearMap.rTensor N (generize m f) := by
  simp [generize, generize', f.isCompat_apply, smul_tmul']

/-- **MI** : do we need these two lemmas? I don't think we are using them. -/
theorem generize_comp_equiv {κ : Type*} [Fintype κ] {e : ι ≃ κ} {m : κ → M} {f : M →ₚₗ[R] N} :
    generize m f =
      (aeval (fun i ↦ X (e i))).toLinearMap.rTensor N (generize (fun x ↦ m (e x)) f) := by
  let hf := f.isCompat_apply (aeval (fun i ↦ X (e i)) : MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (∑ i, X i ⊗ₜ[R] (m (e i)))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf
  simp only [generize, coe_mk, AddHom.coe_mk, hf]
  apply congr_arg
  simp [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

theorem generize_comp_equiv' {κ : Type*} [Fintype κ] {e : ι ≃ κ} {m : κ → M}
    {f : M →ₚₗ[R] N} : (generize (fun x ↦ m (e x)) f) =
      (aeval (fun i ↦ X (e.symm i))).toLinearMap.rTensor N (generize m f) := by
  let hf' := f.isCompat_apply (aeval (fun i ↦ X (e.symm i)) :
    MvPolynomial κ R →ₐ[R] MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i)
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf'
  simp only [generize, coe_mk, AddHom.coe_mk, hf']
  apply congr_arg
  simp [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

end generize

section coeff

variable [DecidableEq ι] (m : ι → M) (k : ι →₀ ℕ)
  {S : Type*} [CommSemiring S] [Algebra R S] (s : ι → S)
  (f : M →ₚₗ[R] N)

/-- The coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def coeff : (M →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (generize m)

theorem generize_eq : generize m f = (coeff m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n)  := by
  dsimp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize h : scalarRTensor (generize m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h, LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d (fun _ _ hb ↦ by simp [if_neg hb,
    scalarRTensor_apply_tmul_apply]) (by simp), scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul]

theorem generize'_eq  :
    generize' m s f = (coeff m f).sum
      fun k n ↦ k.prod (fun i e ↦ s i ^ e) • (monomial k 1) ⊗ₜ n := by
  rw [generize'_eq_generize, generize_eq, map_finsuppSum]
  apply Finsupp.sum_congr
  intro k hk
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, Finsupp.prod_pow]
  congr
  simp only [aeval_monomial, map_one, Finsupp.prod_pow, one_mul]
  simp_rw [smul_pow, Algebra.smul_def]
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp [monomial_eq]

theorem coeff_eq :
  coeff m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i))) := by
  rw [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _

/- **MI**: these two lemmas seemed unused as well. -/
theorem coeff_comp_equiv {κ : Type*} [DecidableEq κ] [Fintype κ] (e : ι ≃ κ) (m : κ → M) :
    coeff m f (k.equivMapDomain e) = coeff (m.comp e) f (k) := by
  simp only [coeff, coe_comp, LinearEquiv.coe_coe, MvPolynomial.scalarRTensor_apply, Function.comp]
  let hf := f.isCompat_apply (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
    MvPolynomial ι R →ₐ[R] MvPolynomial κ R) (∑ i, X i ⊗ₜ[R] (m (e i)))
  suffices toFun f (MvPolynomial κ R) (∑ x, MvPolynomial.X (e x) ⊗ₜ[R] m (e x)) = generize m f by
    simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X, this] at hf
    rw [← hf]
    generalize h : generize (fun x ↦ m (e x)) f = g
    simp only [generize, coe_mk, AddHom.coe_mk] at h
    rw [h, EmbeddingLike.apply_eq_iff_eq, ← LinearMap.rTensor_comp_apply, ← h]
    congr
    ext p
    simp only [coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
      _root_.map_one, Finsupp.prod_pow, _root_.one_mul, MvPolynomial.lcoeff_apply]
    suffices ∏ x, MvPolynomial.X (e x) ^ p x =
        MvPolynomial.monomial (Finsupp.equivMapDomain e p) (1 : R) by
      simp only [this, MvPolynomial.coeff_monomial]
      by_cases h : p = k
      . rw [if_pos h, if_pos (by rw [h])]
      . rw [if_neg h, if_neg]
        intro h'; apply h
        ext i
        simpa [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using
          (DFunLike.ext_iff.mp h') (e i)
    . simp [monomial_eq, _root_.map_one, Finsupp.prod_pow, one_mul, prod_congr_equiv e,
        map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]
  . rw [generize, coe_mk, AddHom.coe_mk]
    apply congr_arg
    simp [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

theorem coeff_comp_equiv' {κ : Type*} [DecidableEq κ] [Fintype κ] (e : ι ≃ κ) (m : κ → M)
    (k : κ →₀ ℕ) : coeff m f k = coeff (m ∘ e) f (k.equivMapDomain e.symm) := by
  rw [coeff_comp_equiv]
  congr
  ext k
  simp [Function.comp_apply, Equiv.apply_symm_apply]

theorem toFun_sum_tmul_eq_coeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) :
    f.toFun S (∑ i, r i ⊗ₜ[R] m i) = (coeff m f).sum (fun k n ↦ (∏ i, r i ^ k i) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul]

theorem toFun_add_tmul_eq_coeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r s : S)
    (m₁ m₂ : M) : f.toFun S (r ⊗ₜ[R] m₁ + s ⊗ₜ[R] m₂) =
      (coeff ((finTwoArrowEquiv _).symm (m₁, m₂)) f).sum
        (fun k n ↦ (r ^ k 0 * s ^ k 1) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval ((finTwoArrowEquiv _).symm (r, s))))
    (X 0 ⊗ₜ[R] m₁ + X 1 ⊗ₜ[R] m₂)
  simp only [Function.comp_apply, map_add, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X, finTwoArrowEquiv_symm_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  let h := generize_eq ((finTwoArrowEquiv _).symm (m₁, m₂)) f
  simp only [generize, coe_mk, AddHom.coe_mk, finTwoArrowEquiv_symm_apply, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul]

theorem toFun_tmul_eq_coeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S)
    (m₁ : M) : f.toFun S (r ⊗ₜ[R] m₁) =
      (coeff (fun (_ : Unit) ↦ m₁) f).sum (fun k n ↦ (r ^ k 0) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval (fun (_ : Unit) ↦ r))) (X 0 ⊗ₜ[R] m₁)
  simp only [PUnit.zero_eq, Function.comp_apply, rTensor_tmul, AlgHom.toLinearMap_apply,
    aeval_X] at this
  let h := generize_eq (fun (_ : Unit) ↦ m₁) f
  simp only [generize, univ_unique, PUnit.default_eq_unit, sum_singleton, coe_mk,
    AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul]

theorem toFun_zero_of_constantCoeff_zero
    {M : Type*} [AddCommMonoid M] [Module R M] (f : M →ₚₗ[R] N)
    (hf : f.coeff (0 : ι → M) = 0)
    (S : Type*) [CommSemiring S] [Algebra R S] :
    f.toFun S 0 = 0 := by
  have : (0 : S ⊗[R] M) =
    ∑ (i : ι), ((0 : ι → S) i) ⊗ₜ[R] ((0 : ι → M) i) := by
    simp
  rw [this, toFun_sum_tmul_eq_coeff_sum, hf]
  simp

theorem toFun'_zero_of_constantCoeff_zero
    {M : Type*} [AddCommMonoid M] [Module R M] (f : M →ₚₗ[R] N)
    (hf : f.coeff (0 : ι → M) = 0)
    (S : Type u) [CommSemiring S] [Algebra R S] :
    f.toFun' S 0 = 0 := by
  rw [← toFun_eq_toFun', toFun_zero_of_constantCoeff_zero _ hf]

end coeff

end Fintype

open Function

/-- Variant of `toFun_sum_tmul_eq_coeff_sum` over a Finset -/
theorem toFun_sum_tmul_eq_coeff_finset_sum [DecidableEq ι] (m : ι → M) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) (s : Finset ι) :
    f.toFun S (∑ i ∈ s, r i ⊗ₜ[R] m i) = (coeff (fun i : s ↦ m i) f).sum
      (fun k n ↦ (∏ i ∈ s, r i ^ ((Function.extend (fun x ↦ x.val) k (Function.const ι 0)) i)) ⊗ₜ[R] n) := by
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
        (r i ^ ((Function.extend (fun x ↦ x.val) k (Function.const ι 0)) i))) ⊗ₜ[R] n) := by
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
    ground f (r₁ • m₁) = (coeff (Function.const Unit m₁) f).sum (fun k n ↦ r₁ ^ (k 0) • n) := by
  suffices r₁ • m₁ = ∑ i, (Function.const Unit r₁) i • (Function.const Unit m₁ i) by
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

variable {M N ι : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (S : Type*) [CommSemiring S] [Algebra R S]

/- When M is free, we can go in the other direction and construct,
  from a basis `b` of `M` and `N`-valued polynomials, a polynomial law. -/
variable (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) (m : S ⊗[R] M)

section Fintype

variable [Fintype ι]

-- BP
/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ N`, `Finsupp.polynomialLaw b h : M →ₚₗ[R] N` is
the polynomial law whose coefficients at `b` are given by `h`. -/
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
  `Finsupp.polynomialLaw b h : M →ₚₗ[R] N` is the polynomial law
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

#min_imports
