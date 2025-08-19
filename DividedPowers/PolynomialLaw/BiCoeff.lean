import DividedPowers.PolynomialLaw.Coeff
import DividedPowers.ForMathlib.Algebra.BigOperators.Finsupp.Fin

universe u

variable {R : Type u} [CommSemiring R]

/- # Polynomial laws. -/

namespace PolynomialLaw

open Finset MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {N M M' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R M']

open LinearMap

section biGenerize

noncomputable def biGenerize (m : M × M') :
    ((M × M') →ₚₗ[R] N) →ₗ[R] MvPolynomial (Fin 2) R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial (Fin 2) R) (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

end biGenerize

section biCoeff

variable (m : M × M') (f : (M × M') →ₚₗ[R] N)

private noncomputable def biCoeff_aux (g : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ) : N :=
  scalarRTensor.toLinearMap.comp (biGenerize m) g
      (Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _))

private lemma biCoeff_aux_apply (g : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ) :
  biCoeff_aux m g n = scalarRTensor.toLinearMap.comp (biGenerize m) g
      (Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _)) := rfl

private lemma finite_support_biCoeff_aux (g : (M × M') →ₚₗ[R] N) :
    (Function.support (biCoeff_aux m g)).Finite := by
  apply Set.Finite.of_injOn (f := (finTwoArrowEquiv' ℕ).symm) ?_
    (Equiv.injective (finTwoArrowEquiv' ℕ).symm).injOn (Finsupp.finite_support
    (scalarRTensor.toLinearMap.comp (biGenerize m) g))
  simp only [Set.MapsTo, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Function.mem_support,
    ne_eq, Finsupp.fun_support_eq, mem_coe, Finsupp.mem_support_iff, Prod.forall]
  exact fun _ _ hab ↦ by simpa using hab

/-- The b-coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def biCoeff : ((M × M') →ₚₗ[R] N) →ₗ[R] (ℕ × ℕ) →₀ N where
  toFun g := Finsupp.ofSupportFinite (fun n ↦ scalarRTensor.toLinearMap.comp (biGenerize m) g
      (Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _))) (finite_support_biCoeff_aux m g)
  map_add' mn mn' := by simp [Finsupp.ext_iff, Finsupp.ofSupportFinite_coe]
  map_smul' r nm := by simp [Finsupp.ext_iff, Finsupp.ofSupportFinite_coe]

lemma biCoeff_apply (g : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ) :
    biCoeff m g n = scalarRTensor.toLinearMap.comp (biGenerize m) g
      (Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _)) := rfl

theorem biGenerize_eq : biGenerize m f =
    (biCoeff m f).sum (fun k n ↦ (monomial ((finTwoArrowEquiv' ℕ).symm k) 1) ⊗ₜ n) := by
  dsimp only [biCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_mk, AddHom.coe_mk]
  generalize h : (Finsupp.ofSupportFinite (fun (n : ℕ × ℕ) ↦ (scalarRTensor ((biGenerize m) f))
    (Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _))) (finite_support_biCoeff_aux m f)) = p
  have h' : scalarRTensor.symm (Finsupp.equivMapDomain (finTwoArrowEquiv' ℕ).symm p) =
      (biGenerize m) f := by
    rw [← h]
    simp only [LinearEquiv.symm_apply_eq, Finsupp.ext_iff]
    intro d
    simp only [Finsupp.equivMapDomain_apply, Equiv.symm_symm, finTwoArrowEquiv', Fin.isValue,
      Equiv.coe_fn_mk]
    rw [Finsupp.ofSupportFinite_coe]
    congr
    rw [Finsupp.ext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  rw [← h', LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single (finTwoArrowEquiv' ℕ d) ?_ (fun _ ↦ by simp),
    scalarRTensor_apply_tmul_apply, coeff_monomial, if_pos (Equiv.symm_apply_apply _ _),
    _root_.one_smul, Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  · intro n hn hd
    have hd' : (finTwoArrowEquiv' ℕ).symm n ≠ d := by
      rw [ne_eq, Equiv.symm_apply_eq]
      exact hd
    simp [-finTwoArrowEquiv'_symm_apply, scalarRTensor_apply_tmul_apply, coeff_monomial,
      if_neg hd', _root_.zero_smul]

variable (k : ℕ × ℕ)

theorem biCoeff_eq :
  biCoeff m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R
    ((finTwoArrowEquiv' ℕ).symm k)))
      (f.toFun (MvPolynomial (Fin 2) R) (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)))) := by
  simp only [biCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_mk, AddHom.coe_mk,
    Fin.isValue]
  exact scalarRTensor_apply _ _

theorem toFun_add_tmul_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r s : S) :
    f.toFun S (r ⊗ₜ[R] (m.1, 0) + s ⊗ₜ (0, m.2)) =
      (biCoeff m f).sum (fun k n ↦ (r ^ k.1 * s ^ k.2) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval ((finTwoArrowEquiv' S).symm (r, s))))
     (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2))
  simp only [Fin.isValue, Function.comp_apply, map_add, rTensor_tmul, AlgHom.toLinearMap_apply,
    aeval_X] at this
  simp only [finTwoArrowEquiv', Fin.isValue, Equiv.coe_fn_symm_mk, Finsupp.ofSupportFinite_coe,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  let h := biGenerize_eq m f
  simp only [biGenerize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul, finTwoArrowEquiv',
    Finsupp.ofSupportFinite_coe ]

theorem toFun_tmul_fst_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) :
    f.toFun S (r ⊗ₜ[R] (m.1, 0)) =
      ((biCoeff (m.1, 0) f).sum fun k n ↦ (r ^ k.1 * r ^ k.2) ⊗ₜ[R] n) := by
  have : r ⊗ₜ[R] (m.1, (0 : M')) = (r, r).1 ⊗ₜ[R] (m.1, 0) + (r, r).2 ⊗ₜ[R] (0, 0) := by
    simp [Prod.mk_zero_zero, tmul_zero, add_zero]
  rw [this, toFun_add_tmul_eq_biCoeff_sum (m.1, 0)]

theorem toFun_tmul_snd_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) :
    f.toFun S (r ⊗ₜ[R] (0, m.2)) =
      ((biCoeff (0, m.2) f).sum fun k n ↦ (r ^ k.1 * r ^ k.2) ⊗ₜ[R] n) := by
  have : r ⊗ₜ[R] ((0 : M), m.2) = (r, r).1 ⊗ₜ[R] (0, 0) + (r, r).2 ⊗ₜ[R] (0, m.2) := by
    simp [Prod.mk_zero_zero, tmul_zero, zero_add]
  rw [this, toFun_add_tmul_eq_biCoeff_sum (0, m.2)]

end biCoeff

open Function

variable (r : R × R) (r₁ r₂ : R) (m m₁ m₂ : M × M') (k : ℕ × ℕ) (f : (M × M') →ₚₗ[R] N)

theorem ground_apply_sum_smul_eq_biCoeff_sum :
    ground f (r.1 • (m.1, 0) + r.2 • (0, m.2)) =
      (biCoeff m f).sum (fun k n ↦ (r.1 ^ k.1 * r.2 ^ k.2) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_add, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', toFun_add_tmul_eq_biCoeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ ↦ by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])

theorem ground_apply_smul_eq_biCoeff_sum :
    ground f (r₁ • m₁) = (biCoeff m₁ f).sum (fun k n ↦ r₁ ^ (k.1 + k.2) • n) := by
  suffices r₁ • m₁ = (r₁, r₁).1 • (m₁.1, 0) + (r₁, r₁).2 • (0, m₁.2) by
    rw [this, ground_apply_sum_smul_eq_biCoeff_sum]
    exact sum_congr rfl (by simp [pow_add])
  simp only [← smul_add, Prod.mk_add_mk, add_zero, zero_add]

variable {S : Type*} [CommSemiring S] [Algebra R S]

theorem biCoeff_injective {m : M × M'}
    (hm : Submodule.span R (Set.range ![(m.1, (0 : M')), ((0 : M), m.2)]) = ⊤) :
    Function.Injective (biCoeff m : ((M × M') →ₚₗ[R] N) →ₗ[R] (ℕ × ℕ) →₀ N) := fun f g h ↦ by
  ext S _ _ p
  suffices hp : p ∈ Submodule.span S
      (Set.range fun (i : Fin 2) ↦ (1 : S) ⊗ₜ[R] (![(m.1, (0 : M')), ((0 : M), m.2)]) i) by
    simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
    obtain ⟨r, rfl⟩ := hp
    set r' : S × S := finTwoArrowEquiv' S r with hr'
    have hr0 : r 0 = r'.1 := by simp [hr', finTwoArrowEquiv']
    have hr1 : r 1 = r'.2 := by simp [hr', finTwoArrowEquiv']
    rw [Finsupp.sum_of_support_subset _ (subset_univ _) _ (fun  i _ ↦ by
      rw [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul])]
    simp [smul_eq_mul, mul_one, ← toFun_eq_toFun'_apply, hr0, hr1, toFun_add_tmul_eq_biCoeff_sum, h]
  simp [Submodule.span_tensorProduct_eq_top_of_span_eq_top _ hm]

theorem biCoeff_inj {m : M × M'}
    (hm : Submodule.span R (Set.range ![(m.1, (0 : M')), ((0 : M), m.2)]) = ⊤)
    {f g : (M × M') →ₚₗ[R] N} :
    (biCoeff m f) = (biCoeff m g ) ↔ f = g := (biCoeff_injective hm).eq_iff

end Coefficients

end PolynomialLaw
