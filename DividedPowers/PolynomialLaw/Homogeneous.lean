/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.ForMathlib.RingTheory.TensorProduct.Polynomial
import DividedPowers.PolynomialLaw.Coeff
import DividedPowers.ForMathlib.Algebra.Polynomial.AlgebraMap
import DividedPowers.ForMathlib.Algebra.Algebra.Bilinear
import DividedPowers.ForMathlib.Algebra.BigOperators.Finsupp.Basic

universe u

/- # Homogeneous components of a polynomial map

Let `R` be a commutative ring, let `M` and `N` be `R`-modules, and let `f : M →ₚₗ[R] N` be a
polynomial law.

## Main Definitions

* `PolynomialLaw.IsHomogeneousOfDegree`: a polynomial law `f` is homogeneous of degree `p` if for
  all commutative `R`-algebras `S : Type u` and  all `s : S`,
  `f.toFun' S (s • m) = s ^ p (f.toFun' S m)` for all `m : S ⊗[R] M`. The property extends to all
  `R`-algebras for `f.toFun`.

## Main Results

* `PolynomialLaw.isHomogeneousOfDegree_of_coeff_iff`: A polynomial law `f` is homogeneous of
  degree `p` iff for all `m : ι → M`, and all `d : ι →₀ ℕ`, `f.coeff m d` vanishes unless the sum
  of `d` equals `p`.

* Homogeneous polynomial maps of degree 0 are constant polynomial maps.

* `LinearMap.baseChange` furnishes, for every linear map `M →ₗ[R] N`,
a polynomial map `f : M →ₚ[R] N` which is homogeneous of degree 1.
All homogeneous polynomial maps `f` of degree 1 are of this form,
associated with `f.ground`.

* For all `p : ℕ`, `f.component p` is a homogeneous polynomial map
of degree `p`, which we call the homogeneous components of `f`.
It is defined so that its coefficients are exactly those of degree `p`
of `f`.

* Any polynomial map is the sum of its homogeneous components, in the
following sense : for all `R`-algebras `S` and all `m : S ⊗[R] M`,
the function `p ↦ (f.component p).toFun' S m` has finite support,
and its sum is `f.toFun' S m`.

## TODO

* Characterize homogeneous polynomial maps of degree 2:
one should recover quadratic maps `M → N`
(whether this is exactly true depends on subtleties of the definition
of quadratic maps for modules).

## Construction of the homogeneous components

Let `S` be an `R`-algebra and let `j : S →ₐ[S] S[X]` be the canonical algebra map.

For `m : S ⊗[R] M`, we consider the element `X • (j m) : S[X] ⊗[R] M`
and its image `f.toFun' S[X] (X • (j m)) : S[X] ⊗[R] N`.
The components of `f` are defined so that
`f.toFun' S[X] (X • (j m)) = ∑ X ^ p • (j ((f.component p).toFun' S m))`.

If one consider the morphism of evaluation at 1, `ε : S[X] →ₐ[R] S`,
we have `ε ∘ j = @id S`, and the compatibility properties of `f` implies that
`f.toFun' S[X] m = ∑ (f.component p).toFun' S m`.

-/

open LinearMap TensorProduct

namespace PolynomialLaw

section Homogeneous

open Finsupp MvPolynomial

variable {R : Type u} {M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A polynomial map `f : M →ₚ[R] N` is homogeneous of degree `p`
  if the function `f.toFun' S` is homogeneous of degree `p` for all `S` -/
def IsHomogeneousOfDegree (p : ℕ) (f : M →ₚₗ[R] N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : S) (m : S ⊗[R] M),
    f.toFun' S (r • m) = r ^ p • f.toFun' S m

theorem IsHomogeneousOfDegree_add (p : ℕ) {f g : M →ₚₗ[R] N}
    (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree p) :
    (f + g).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp [hf S s m, hg S s m]

theorem IsHomogeneousOfDegree_smul (p : ℕ) (r : R) {f : M →ₚₗ[R] N}
    (hf : f.IsHomogeneousOfDegree p) : (r • f).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm r (s ^ p) (toFun' f S m)

/-- The submodule of homogeneous polynomial laws of degree `p`. -/
def grade (p : ℕ) : Submodule R (M →ₚₗ[R] N) where
  carrier            := IsHomogeneousOfDegree p
  add_mem' hf hg     := IsHomogeneousOfDegree_add p hf hg
  smul_mem' r f hf   := IsHomogeneousOfDegree_smul p r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

variable {p : ℕ} {f : M →ₚₗ[R] N}

lemma mem_grade: f ∈ grade p ↔ IsHomogeneousOfDegree p f := by rfl

/-- If `f` is homogeneous of degree `p`, then all `f.toFun S` are homogeneous of degree `p`. -/
lemma isHomogeneousOfDegree_toFun (hf : IsHomogeneousOfDegree p f) (S : Type*) [CommSemiring S]
    [Algebra R S] (r : S) (m : S ⊗[R] M) : f.toFun S (r • m) = r ^ p • f.toFun S m := by
  choose n ψ  m' r' hm' hr' using PolynomialLaw.exists_lift' m r
  simp only [← hm', ← hr', ← isCompat_apply, toFun_eq_toFun', TensorProduct.smul_rTensor]
  rw [hf, ← TensorProduct.smul_rTensor, map_pow]

/-- If `f` is homogeneous of degree `p`, then `f.ground` is too.  -/
lemma isHomogeneousOfDegree_ground (hf : IsHomogeneousOfDegree p f) (r : R) (m : M) :
    f.ground (r • m) = r ^ p • f.ground m := by simp [ground, hf R r]

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isHomogeneousOfDegree_coeff (hf : IsHomogeneousOfDegree p f) {ι : Type*} [DecidableEq ι]
    [Fintype ι] (m : ι → M) (d : ι →₀ ℕ) (hd : d.sum (fun _ n => n) ≠ p) :
    PolynomialLaw.coeff m f d = 0 := by
  classical
  let e (b : ι →₀ ℕ) (k : ℕ) : Option ι →₀ ℕ :=
    Finsupp.update (Finsupp.mapDomainEmbedding (Function.Embedding.some) b) none k
  have he : ∀ b k, (X none ^ k * (Finset.prod Finset.univ fun x => X (Option.some x) ^ b x) :
      MvPolynomial (Option ι) R) = monomial (e b k) 1 := fun b k ↦ by
    simp only [Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply, monomial_eq,
      map_one, Finsupp.prod_pow, Finsupp.coe_update, Fintype.prod_option, Function.update_self,
      ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, one_mul, e]
    exact congr_arg₂ _ rfl (Finset.prod_congr rfl (fun _ _ => by
      rw [Finsupp.mapDomain_apply (Option.some_injective ι)]))
  have he_some : ∀ b k i, e b k (some i) = b i := fun b k i ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, reduceCtorEq, ↓reduceDIte,
      Finsupp.mapDomain_apply (Option.some_injective ι), e]
  have he_none : ∀ b k, k = e b k none := fun b k ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, ↓reduceDIte, e]
   /-  On écrit l'homogénéité : f (∑ T ⬝ X_i m_i) = T ^ p ⬝ f(∑ X_i m_i)
   ∑ coeff f e (T X) ^ e = T ^ p ⬝ ∑ coeff f e X ^ e
   Identification : (coeff f e) T^|e| X^ e = coeff f e T ^ p X ^ e
   On en déduit coeff f e = 0 si |e| ≠ p .    -/
  let μ : MvPolynomial (Option ι) R ⊗[R] M := Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m i)
  have hf' := isHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (X none) μ
  simp only [μ, Finset.smul_sum, TensorProduct.smul_tmul', toFun_sum_tmul_eq_coeff_sum,
    Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [map_finsuppSum, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hφ
  rw [Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul,
    LinearMap.coe_mk, AddHom.coe_mk, lid_tmul, φ] at hφ
  rw [he, coeff_monomial, if_pos, _root_.one_smul, he, coeff_monomial, if_neg, _root_.zero_smul]
    at hφ
  exact hφ
  · intro hd'
    apply hd
    convert (DFunLike.ext_iff.mp hd'.symm) none <;> exact (he_none _ _)
  · simp only [Finset.mem_univ, implies_true,
    Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  all_goals
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, lid_tmul, φ]
    rw [he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i

/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isHomogeneousOfDegree_of_coeff_iff :
    IsHomogeneousOfDegree p f ↔ ∀ (n : ℕ) (m : (Fin n) → M) (d : (Fin n) →₀ ℕ)
      (_ : d.sum (fun _ n => n) ≠ p), PolynomialLaw.coeff m f d = 0 := by
  refine ⟨fun hf _ m d hd => isHomogeneousOfDegree_coeff hf m d hd, fun H S _ _ r μ => ?_⟩
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
  simp only [Finset.smul_sum, TensorProduct.smul_tmul']
  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro d hd
  rw [TensorProduct.smul_tmul']
  apply congr_arg₂ _ _ rfl
  simp only [smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  apply congr_arg₂ _ _ rfl
  rw [Finset.prod_pow_eq_pow_sum]
  apply congr_arg₂ _ rfl
  specialize H n m d
  rw [not_imp_comm, Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ ↦ rfl)] at H
  exact H (Finsupp.mem_support_iff.mp hd)

theorem IsHomogeneousOfDegree.comp {P : Type*} [AddCommMonoid P] [Module R P] {q : ℕ}
    {g : N →ₚₗ[R] P} (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsHomogeneousOfDegree (p * q) :=
  fun S _ _ r m ↦ by simp [comp_toFun', hf S, hg S, ← pow_mul]

end Homogeneous

section ConstantMap

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

open MvPolynomial

noncomputable def ofConstant (n : N) : M →ₚₗ[R] N where
  toFun' S _ _ _:= TensorProduct.tmul R 1 n
  isCompat' φ   := by ext; simp

@[simp]
lemma ofConstant_apply {S : Type u} [CommSemiring S] [Algebra R S] (n : N) (sm : S ⊗[R] M) :
  (ofConstant n).toFun' S sm = TensorProduct.tmul R 1 n := rfl

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantHom : N →ₗ[R] (grade 0 : Submodule R (M →ₚₗ[R] N)) := {
  toFun n := {
    val := ofConstant n
    property := by
      rw [grade, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
      intro S _ _ r sm
      rw [pow_zero, _root_.one_smul, ofConstant] }
  map_add' x y := by
    simp only [ofConstant, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    ext
    simp [add_def_apply, TensorProduct.tmul_add]
  map_smul' r x := by
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq]
    ext S _ _ sm
    simp }

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantEquiv :
    N ≃ₗ[R] (grade 0 : Submodule R (M →ₚₗ[R] N)) := {
  ofConstantHom with
  invFun f    := f.val.ground 0
  left_inv x  := by simp [ground, ofConstantHom]
  right_inv x := by
    obtain ⟨f, hf⟩ := x
    rw [mem_grade] at hf
    rw [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Subtype.ext_iff, Subtype.coe_mk]
    simp only [ofConstantHom, ground, Function.comp_apply, map_zero, coe_mk, AddHom.coe_mk]
    ext S _ _ m
    conv_rhs =>
      rw [← _root_.one_smul (M := S) (f.toFun' S m), ← pow_zero 0, ← hf S _ m, _root_.zero_smul]
    simp [ofConstant_apply, includeRight_lid, isCompat_apply'] }

end ConstantMap

section Linear

open scoped TensorProduct

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

section coeff

open Finsupp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : M →ₚₗ[R] N}

theorem isHomogeneousOfDegreeOne_coeff (hf : f.IsHomogeneousOfDegree 1) (m : ι → M) {d : ι →₀ ℕ}
    (hd : d.sum (fun _ n => n) ≠ 1) :
    (coeff m f) d = 0 :=
  isHomogeneousOfDegree_coeff hf m d hd

theorem isHomogeneousOfDegreeOne_coeff_support_le (hf : IsHomogeneousOfDegree 1 f) (m : ι → M) :
    (coeff m f).support ⊆ Finset.map
      ⟨fun i ↦ single i 1, single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [mem_support_iff, ne_eq] at hd
  simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
    true_and, sum_eq_one_iff] using (not_imp_comm.mp (isHomogeneousOfDegreeOne_coeff hf m)) hd

theorem isHomogeneousOfDegreeOne_coeff_single (hf : f.IsHomogeneousOfDegree 1) (m : ι → M) (i : ι) :
    (coeff m f) (single i 1) = f.ground (m i) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : Finset.sum Finset.univ (fun (j : ι) => (Pi.single i (1 : R) j) ⊗ₜ[R] m j) =
      1 ⊗ₜ[R] m i := by
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_tmul])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same]
  simp only [← this, toFun_sum_tmul_eq_coeff_sum, map_finsuppSum, lid_tmul]
  rw [sum_of_support_subset _ (isHomogeneousOfDegreeOne_coeff_support_le hf m) _ (by simp),
    Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_eq_single i _ (by simp)]
  · rw [Finset.prod_eq_single i (fun j _ hj => by rw [single_eq_of_ne hj.symm, pow_zero])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same,
      one_pow, _root_.one_smul]
  · intro j _ hj
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_univ _) (by simp [Pi.single_eq_of_ne hj]),
      _root_.zero_smul]

end coeff

variable (v : M →ₗ[R] N)

noncomputable def ofLinearMap : M →ₚₗ[R] N where
  toFun' S _ _ := v.baseChange S
  isCompat' φ  := by
    ext
    simp [← LinearMap.comp_apply, baseChange_eq_ltensor, Function.comp_apply]

lemma ofLinearMap_mem_grade_one : IsHomogeneousOfDegree 1 (ofLinearMap v) :=
  fun S _ _ r m => by simp [ofLinearMap]

theorem IsHomogeneousOfDegree.comp_ofLinearMap {P : Type*} [AddCommMonoid P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₚₗ[R] P} {q : ℕ} (hg : g.IsHomogeneousOfDegree q) :
    (g.comp (PolynomialLaw.ofLinearMap f)).IsHomogeneousOfDegree q := by
  simpa using IsHomogeneousOfDegree.comp (ofLinearMap_mem_grade_one f) hg

theorem IsHomogeneousOfDegree.ofLinearMap_comp {P : Type*} [AddCommMonoid P] [Module R P]
    {f : M →ₚₗ[R] N} {g : N →ₗ[R] P} {p : ℕ} (hf : f.IsHomogeneousOfDegree p) :
    ((PolynomialLaw.ofLinearMap g).comp f).IsHomogeneousOfDegree p := by
  simpa using IsHomogeneousOfDegree.comp hf (ofLinearMap_mem_grade_one g)

theorem ofLinearMap_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    (ofLinearMap v).toFun' S = LinearMap.baseChange S v := rfl

theorem ofLinearMap_toFun (S : Type*) [CommSemiring S] [Algebra R S] :
    (ofLinearMap v).toFun S = v.baseChange S := by
  ext sm
  obtain ⟨n, φ, p, rfl⟩ := exists_lift sm
  simp only [← isCompat_apply, toFun_eq_toFun', ofLinearMap_toFun', baseChange_eq_ltensor,
    ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

open MvPolynomial

open Finsupp LinearMap

theorem ofLinearMap_coeff_single (u : M →ₗ[R] N) (ι : Type*) [DecidableEq ι] [Fintype ι]
    (m : ι → M) (i : ι) : ((coeff m) (ofLinearMap u)) (single i 1) = u (m i) := by
  rw [coeff, generize, coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  simp only [ofLinearMap_toFun, map_sum, LinearMap.baseChange_tmul]
  rw [coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single i ?_ (fun hi => by simp at hi),
    scalarRTensor_apply_tmul_apply, coeff_X, _root_.one_smul]
  intro b _ hb
  have hb' : ¬ single b 1 = single i 1 := by rwa [Finsupp.single_left_inj]; norm_num
  rw [scalarRTensor_apply_tmul_apply, coeff_X', if_neg hb', _root_.zero_smul]

noncomputable def ofLinearMapHom :
    (M →ₗ[R] N) →ₗ[R] (grade 1 : Submodule R (M →ₚₗ[R] N)) where
  toFun         := fun u ↦ ⟨ofLinearMap u, ofLinearMap_mem_grade_one u⟩
  map_add' u v  := by
    ext S _ _ m
    simp [ofLinearMap_toFun']
  map_smul' a v := by
    ext S _ _ m
    simp [ofLinearMap_toFun']

theorem ofLinearMapHom_apply : ofLinearMapHom v = ofLinearMap v := rfl

private lemma zero_pow_add_zero_pow (a b : ℕ) (h : a + b = 1) :
    0 ^ a + 0 ^ b = (1 : R) := by
  suffices (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) by
    cases this with
    | inl h => rw [h.1, h.2, pow_one, pow_zero, zero_add]
    | inr h => rw [h.1, h.2, pow_one, pow_zero, add_zero]
  by_cases ha : a = 0
  · exact Or.inr ⟨ha, by simpa [ha, zero_add] using h⟩
  · have ha : a = 1 := le_antisymm (h ▸  Nat.le_add_right a b) (Nat.pos_of_ne_zero ha)
    exact Or.inl ⟨ha, by simpa [ha, add_eq_left] using h⟩

noncomputable def toLinearMap (f : (grade 1 : Submodule R (M →ₚₗ[R] N))) :
    M →ₗ[R] N := {
  toFun    := ground (f : M →ₚₗ[R] N)
  map_add' m n := by
    obtain ⟨f, hf⟩ := f
    rw [mem_grade, isHomogeneousOfDegree_of_coeff_iff] at hf
    let h := fun (r s : R) ↦ f.ground_apply_add_smul r s m n
    have h11 := h 1 1; simp only [_root_.one_smul] at h11
    have h10 := h 1 0; simp only [_root_.one_smul, _root_.zero_smul, _root_.add_zero] at h10
    have h01 := h 0 1; simp only [_root_.one_smul, _root_.zero_smul, _root_.zero_add] at h01
    rw [h01, h10, h11, ← sum_add]
    apply sum_congr
    intro x hx
    rw [← _root_.add_smul]
    apply congr_arg₂ _ _ rfl
    simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, one_pow, Matrix.cons_val_one,
      mul_one, one_mul]
    refine (zero_pow_add_zero_pow _ _ ?_).symm
    suffices x.sum (fun _ n => n) = 1 by
      rw [sum_of_support_subset _ (Finset.subset_univ _) _ (fun _ ↦ by simp)] at this
      simpa only [add_comm, Function.comp_apply, Fin.sum_univ_two] using this
    simp only [Finsupp.mem_support_iff, ne_eq] at hx
    exact not_imp_comm.mp (hf _ _ x) hx
  map_smul' r x := by
    obtain ⟨f, hf⟩ := f
    simp [isHomogeneousOfDegree_ground hf] }

lemma toLinearMap_eq_ground (f : (grade 1 : Submodule R (M →ₚₗ[R] N))) :
   toLinearMap f = (f.1).ground := rfl

noncomputable def ofLinearMapEquiv :
    (M →ₗ[R] N) ≃ₗ[R] (grade 1 : Submodule R (M →ₚₗ[R] N)) := {
  ofLinearMapHom with
  invFun := toLinearMap
  left_inv f := by
    ext m
    simp [toLinearMap, ground, ofLinearMapHom, ofLinearMap]
  right_inv f := by
    ext S _ _ sm
    obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S sm
    simp only [AddHom.toFun_eq_coe, ofLinearMapHom, AddHom.coe_mk, ← toFun_eq_toFun',
      ofLinearMap_toFun, map_sum, LinearMap.baseChange_tmul]
    rw [toFun_sum_tmul_eq_coeff_sum, sum_of_support_subset _
      (isHomogeneousOfDegreeOne_coeff_support_le f.prop m) _ (by simp), Finset.sum_map,
      Function.Embedding.coeFn_mk]
    apply Finset.sum_congr rfl
    · intro i _
      rw [isHomogeneousOfDegreeOne_coeff_single f.prop, Finset.prod_eq_single i ?_ (by simp),
        single_eq_same, pow_one, toLinearMap_eq_ground]
      intro j _ hj
      rw [single_eq_of_ne (ne_comm.mp hj), pow_zero] }

end Linear

section Quadratic

end Quadratic

section Components

open Polynomial

/- Here we define the homogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N] (p : ℕ) (r : R) (f g : M →ₚₗ[R] N)

theorem Polynomial.baseChange_comp_monomial_eq {S : Type*} [CommSemiring S] [Algebra R S]
    {S' : Type*} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') (p : ℕ) :
    (Polynomial.baseChange φ).toLinearMap ∘ₗ ((monomial p).restrictScalars R) =
      ((monomial p).restrictScalars R) ∘ₗ φ.toLinearMap := by
  ext
  simp [baseChange_monomial]

/-- The homogeneous component of degree `p` of a `PolynomialLaw`. -/
@[simps] noncomputable def component : M →ₚₗ[R] N where
  toFun' S _ _ m := rTensor R N S
    (f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M m)) p
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    simp only [Function.comp_apply, rTensor_apply, ← rTensor_comp_apply]
    rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply', ← rTensor_comp_apply,
      Polynomial.baseChange_comp_monomial_eq]

theorem component.toFun'_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
  (f.component p).toFun' S m =
    rTensor R N S (f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M m)) p := rfl

theorem component_toFun_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (f.component p).toFun S m = Polynomial.rTensor R N S
      (f.toFun S[X] (((monomial 1).restrictScalars R).rTensor M m)) p := by
  obtain ⟨n, ψ, q, rfl⟩ :=  exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, component.toFun'_apply,
    ← LinearMap.rTensor_comp_apply, ← Polynomial.baseChange_comp_monomial_eq,
    LinearMap.rTensor_comp_apply, ← PolynomialLaw.isCompat_apply]
  simp only [rTensor_apply, ← rTensor_comp_apply]
  rw [lcoeff_comp_baseChange_eq, toFun_eq_toFun'_apply]

-- TODO: continue from here.

/-- `f.component p` is homogeneous of degree `p`. -/
lemma component_isHomogeneous : IsHomogeneousOfDegree p (f.component p) := by
  intro S _ _ s sm
  dsimp only [component]
  let ψ := ((aeval (R := S) (monomial 1 s : S[X])).restrictScalars R)
  suffices  (rTensor M ((monomial 1).restrictScalars R)) (s • sm)
      = (rTensor M ψ.toLinearMap) (rTensor M ((monomial 1).restrictScalars R) sm) by
    rw [this, ← f.isCompat_apply' ψ]
    generalize toFun' f S[X] (rTensor M ((monomial 1).restrictScalars R) sm) = t
    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (s ^ p)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    rw [eq_comm, LinearMap.rTensor, TensorProduct.map]
    apply TensorProduct.lift.unique
    intro f n
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, lift.tmul,
      lcoeff_apply, mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply,
      TensorProduct.smul_tmul']
    apply congr_arg₂ _ _ rfl
    -- ψ f = f (s • X)
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | monomial n a =>
        simp only [ψ, coeff_monomial]
        split_ifs with h
        . rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial, monomial_pow,
            one_mul, ← C_eq_algebraMap, C_mul_monomial, coeff_monomial, if_pos rfl]
        . simp [coeff_monomial, if_neg h]
  .  --
    suffices ∀ (sm : S ⊗[R] M), s • sm =
        rTensor M (((IsLinearMap.isLinearMap_smul s).mk').restrictScalars R) sm by
      simp only [this, ← rTensor_comp_apply]
      exact LinearMap.congr_fun
        (congr_arg _ (LinearMap.ext_iff.mpr fun r ↦ by simp [mul_comm s r, ψ])) _
    --
    intro sm
    rw [← (IsLinearMap.isLinearMap_smul s).mk'_apply, ← LinearMap.coe_restrictScalars R]
    apply LinearMap.congr_fun
    dsimp only [LinearMap.rTensor, TensorProduct.map, smul_eq_mul]
    exact lift.unique fun _ _ ↦ by simp [smul_tmul']

theorem component_add : (f + g).component p = f.component p + g.component p := by
  ext S _ _ sm
  simp

theorem component_smul : (r • f).component p = r • f.component p := by
  ext S _ _ sm
  simp [rTensor_apply]

theorem support_component' {S : Type u} [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    Function.support (fun i => ((fun p => component p f) i).toFun' S m) =
    (rTensor R N S ((f.toFun' S[X] ((rTensor M ((monomial 1).restrictScalars R)) m)))).support := by
  ext n
  simp

theorem support_component {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    Function.support (fun i => ((fun p => component p f) i).toFun S m) =
    (rTensor R N S ((f.toFun S[X] ((rTensor M ((monomial 1).restrictScalars R)) m)))).support := by
  ext i
  rw [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_iff_not,
    component_toFun_apply]

theorem LocFinsupp_component : LocFinsupp (fun p ↦ f.component p) := fun S _ _ m ↦ by simp

theorem LocFinsupp_component_eq {S : Type u} [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (Finsupp.ofSupportFinite (fun i => (component i f).toFun' S m)
      (LocFinsupp_component f S m)) =
    rTensor R N S ((f.toFun' S[X] ((rTensor M ((monomial 1).restrictScalars R)) m))) := by
  ext n
  simp [Finsupp.ofSupportFinite_coe]

/-- A polynomial map is the locally finite sum of its homogeneous components.
(PolynomialLaw lies in between the direct sum and the product of its graded submodules,
hence there is no graded module structure.) -/
theorem recompose_component : lfsum (fun p ↦ f.component p) = f := by
  ext S _ _ sm
  rw [lfsum_eq_of_locFinsupp (LocFinsupp_component f), LocFinsupp_component_eq]
  have hsm : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor M
    (((monomial 1).restrictScalars R).rTensor M sm) := by
    rw [← LinearMap.rTensor_comp_apply, LinearMap.rTensor, eq_comm]
    convert DFunLike.congr_fun TensorProduct.map_id sm
    ext s
    simp
  conv_rhs => rw [hsm, ← f.isCompat_apply']
  generalize f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M sm) = sn
  convert rTensor'_sum (R := R) (fun _ ↦ 1) sn
  rw [_root_.one_smul]
  ext p
  simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', coe_aeval_eq_eval,
    Polynomial.lsum_apply, coe_restrictScalars, lsmul_apply, smul_eq_mul, one_mul, eval_eq_sum]
  exact congr_arg₂ _ rfl (by simp)

end Components

end PolynomialLaw
