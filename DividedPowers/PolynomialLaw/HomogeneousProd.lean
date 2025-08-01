/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.PolynomialLaw.MultiHomogeneous
import Mathlib.LinearAlgebra.TensorProduct.Prod

universe u uι

/- # Multihomogeneous components of a polynomial map

Let `S` be an `R`-algebra and let `j : S →ₐ[S] S[X]` be the canonical algebra map.

For `m : S ⊗[R] M`, we consider the element `X • (j m) : S[X] ⊗[R] M`
and its image `f.toFun' S[X] (X • (j m)) : S[X] ⊗[R] N`.
The components of `f` are defined so that
`f.toFun' S[X] (X • (j m)) = ∑ X ^ p • (j ((f.multiComponent n).toFun' S m))`.

If one consider the morphism of evaluation at 1, `ε : S[X] →ₐ[R] S`,
we have `ε ∘ j = @id S`, and the compatibility properties of `f` implies that
`f.toFun' S[X] m = ∑ (f.multiComponent n).toFun' S m`.
-/

open LinearMap TensorProduct

noncomputable section

namespace PolynomialLaw

open PolynomialLaw

section MultiHomogeneous

section

open Finsupp MvPolynomial

-- **MI**: I replaced  `CommRing R` by `CommSemiring R`.
variable {R : Type u} [CommSemiring R]

variable {M M' N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  {N : Type*} [AddCommMonoid N] [Module R N]

open TensorProduct

-- **MI**: I replaced  `CommRing S` by `CommSemiring S`.
-- TODO: fix docstring
/-- A polynomial map `f : Π (i : ι), M i →ₚ[R] N` is multihomogeneous of multidegree `n : ι → ℕ`
  if for all families `{z_i : R ⊗ M i}_{i : ι}`, `{r_i : R}_{i : ι}`, one has
  `f (r_1 • z_1, r_2 • z_2, ...) = Π i r_i^(n i) • f (z_1, z_2, ...)`. -/
def IsMultiHomogeneousOfDegree' (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (s : S × S) (m : S ⊗[R] (M × M')),
    f.toFun' S ((prodRight R S S M M').symm
      ((s.1 • (prodRight R S _ M M') m).fst, (s.2 • (prodRight R S _ M M') m).snd)) =
      (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun' S m

theorem IsMultiHomogeneousOfDegree_add' (n : ℕ × ℕ) {f g : PolynomialLaw R (M × M') N}
    (hf : f.IsMultiHomogeneousOfDegree' n) (hg : g.IsMultiHomogeneousOfDegree' n) :
    (f + g).IsMultiHomogeneousOfDegree' n := fun S _ _ s m ↦ by
  simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsMultiHomogeneousOfDegree_smul' (n : ℕ × ℕ) (r : R) {f : PolynomialLaw R (M × M') N}
    (hf : f.IsMultiHomogeneousOfDegree' n) :
    (r • f).IsMultiHomogeneousOfDegree' n := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm _ _ _

/-- The submodule of homogeneous polynomial laws of degree `p`. -/
def multiGrade' (n : ℕ × ℕ) : Submodule R (PolynomialLaw R (M × M') N) where
  carrier            := IsMultiHomogeneousOfDegree' n
  add_mem' hf hg     := IsMultiHomogeneousOfDegree_add' n hf hg
  smul_mem' r f hf   := IsMultiHomogeneousOfDegree_smul' n r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_multiGrade' (f : PolynomialLaw R (M × M') N) (n : ℕ × ℕ) :
    f ∈ multiGrade' n ↔ IsMultiHomogeneousOfDegree' n f := by rfl

-- **MI**: I replaced  `CommRing S` by `CommSemiring S`.
-- TODO: generalize `PolynomialLaw.exists_lift'` to this context.
/-- If `f` is multihomogeneous of multidegree `n`, then all `f.toFun S` are multihomogeneous of
  multidegree `n`. -/
lemma isMultiHomogeneousOfDegree_toFun' {n : ℕ × ℕ} {f : PolynomialLaw R (M × M') N}
    (hf : IsMultiHomogeneousOfDegree' n f) (S : Type*) [CommSemiring S] [Algebra R S] (s : S × S)
    (m : S ⊗[R] (M × M')) :
    f.toFun S ((prodRight R S S M M').symm
      ((s.1 • (prodRight R S _ M M') m).fst, s.2 • (prodRight R S _ M M') m).snd) =
      (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun S m :=
  sorry

/-- If `f` is multihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isMultiHomogeneousOfDegree_ground' {n : ℕ × ℕ} {f : PolynomialLaw R (M × M') N}
    (hf : IsMultiHomogeneousOfDegree' n f) (r : R × R) (m : (M × M')) :
    f.ground ((r.1 • m.1, r.2 • m.2)) = (r.1^n.1 * r.2^n.2) • f.ground m := by
  sorry/- have hfrm := hf R r  ((TensorProduct.piRight R R _ _)
    ((TensorProduct.lid R (Π i, M i)).symm m))
  simp only [lid_symm_apply, piRight_apply, piRightHom_tmul, piRight_symm_apply] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply]
  rw [← map_smul, ← hfrm]
  congr
  simp only [← tmul_smul, piRight_symm_apply]
  rfl -/

theorem IsMultiHomogeneousOfDegree.comp' {P : Type*} [AddCommMonoid P] [Module R P]
    {f : (M × M') →ₚₗ[R] N} {g : N →ₚₗ[R] P} {p : ℕ × ℕ} {q : ℕ}
    (hf : f.IsMultiHomogeneousOfDegree' p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsMultiHomogeneousOfDegree' (q • p) := by
  intro S _ _ r m
  sorry --simp [comp_toFun', Function.comp_apply, hf S, hg S, mul_comm q, pow_mul, Finset.prod_pow]

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isMultiHomogeneousOfDegree_coeff' {n : ℕ × ℕ} {f : PolynomialLaw R (M × M') N}
    (hf : IsMultiHomogeneousOfDegree' n f)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (m : ι → (M × M')) (d : ι →₀ ℕ)
    (hd : d.sum (fun _ m => m) ≠ n.1 + n.2) :
    PolynomialLaw.coeff m f d = 0 := by
  classical
  let e (b : ι →₀ ℕ) (k : ℕ) : Option ι →₀ ℕ :=
    Finsupp.update (Finsupp.mapDomainEmbedding (Function.Embedding.some) b) none k
  have he : ∀ b k, (X none ^ k * (Finset.prod Finset.univ
      fun x => X (some x) ^ b x) : MvPolynomial (Option ι) R) = monomial (e b k) 1 := fun b k ↦ by
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
  let μ : MvPolynomial (Option ι) R ⊗[R] (M × M') :=
    Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m i)
  have hf' := isMultiHomogeneousOfDegree_toFun' hf (MvPolynomial (Option ι) R) (X none, X none) μ
  simp only [map_sum, prodRight_tmul, Finset.smul_sum, Prod.smul_mk, smul_tmul', smul_eq_mul,
    prodRight_symm_tmul, Prod.mk.eta, toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum, μ] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [map_finsuppSum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hφ
  rw [Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
    AddHom.coe_mk, lid_tmul, φ] at hφ
  rw [← pow_add] at hφ
  rw [he, coeff_monomial, if_pos, _root_.one_smul, he, coeff_monomial, if_neg, _root_.zero_smul]
    at hφ
  exact hφ
  · intro hd'
    apply hd
    convert (DFunLike.ext_iff.mp hd'.symm) none <;> exact (he_none _ _)
  · simp only [Finset.mem_univ, implies_true,
      Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
      AddHom.coe_mk, lid_tmul, φ]
    rw [← pow_add, he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
      AddHom.coe_mk, lid_tmul, φ]
    rw [he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i

theorem toFun_sum_tmul_eq_coeff_sum' (f : PolynomialLaw R (M × M') N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M × M') (S : Type*)
    [CommSemiring S] [Algebra R S] (r : ι → S) :
    f.toFun S (∑ i, r i ⊗ₜ[R] m i) = (coeff m f).sum (fun k n ↦ (∏ i, r i ^ k i) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [aeval_monomial]

theorem toFun_sum_tmul_eq_coeff_sum'' (f : PolynomialLaw R (M × M') N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M × M') (S : Type*)
    [CommSemiring S] [Algebra R S] (r : ι → S × S) :
    f.toFun S (∑ i,((r i).1 ⊗ₜ[R] ((m i).1, 0) + (r i).2 ⊗ₜ[R] (0, (m i).2))) =
      (coeff m f).sum (fun k n ↦ (∏ i, (r i).1 ^ k i) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [aeval_monomial]

/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isMultiHomogeneousOfDegree_of_coeff_iff' (f : PolynomialLaw R (M × M') N) (p : ℕ × ℕ) :
    IsMultiHomogeneousOfDegree' p f ↔ ∀ (n : ℕ)
      (m : (Fin n) → M × M') (d : (Fin n) →₀ ℕ)
      (_ : d.sum (fun _ n => n) ≠ p.1 + p.2), PolynomialLaw.coeff m f d = 0 := by
  refine ⟨fun hf _ m d hd => isMultiHomogeneousOfDegree_coeff' hf m d hd, fun H S _ _ r μ => ?_⟩
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
  simp only [map_sum, prodRight_tmul, /- Prod.smul_fst, Prod.smul_snd -/]
  simp only [Finset.smul_sum, Prod.smul_mk]
  simp only [Prod.fst_sum, Prod.snd_sum, prod_mk_sum, map_sum]

  have : (∑ x, (prodRight R S S M M').symm (r.1 • s x ⊗ₜ[R] (m x).1, r.2 • s x ⊗ₜ[R] (m x).2)) =
      ∑ x, ((r.1 • s x) ⊗ₜ[R] ((m x).1, 0) + (r.2 • s x) ⊗ₜ[R] (0, (m x).2)) := by
    calc _
      _ = ∑ x, (prodRight R S S M M').symm (r.1 • s x ⊗ₜ[R] (m x).1, 0) +
          ∑ x, (prodRight R S S M M').symm (0, r.2 • s x ⊗ₜ[R] (m x).2) := by
        rw [← Finset.sum_add_distrib]
        congr
      _ = ∑ x, (prodRight R S S M M').symm (r.1 • s x ⊗ₜ[R] (m x).1, r.1 • s x ⊗ₜ[R] 0) +
          ∑ x, (prodRight R S S M M').symm (r.2 • s x ⊗ₜ[R] 0, r.2 • s x ⊗ₜ[R] (m x).2) := by simp
      _ = ∑ x, (prodRight R S S M M').symm ((r.1 • s x) ⊗ₜ[R] (m x).1, (r.1 • s x) ⊗ₜ[R] 0) +
          ∑ x, (prodRight R S S M M').symm ((r.2 • s x) ⊗ₜ[R] 0, (r.2 • s x) ⊗ₜ[R] (m x).2) := by
        simp [smul_tmul']
      _ = ∑ x, ((r.1 • s x) ⊗ₜ[R] ((m x).1, 0)) + ∑ x, ((r.2 • s x) ⊗ₜ[R] (0, (m x).2)) := by
          simp_rw [prodRight_symm_tmul]
      _ = ∑ x, ((r.1 • s x) ⊗ₜ[R] ((m x).1, 0) + (r.2 • s x) ⊗ₜ[R] (0, (m x).2)) := by
        rw [← Finset.sum_add_distrib]
  rw [this]

  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum]

  sorry
  #exit

  --simp only [Finset.smul_sum, TensorProduct.smul_tmul']
  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum]
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

end Homogeneous


/- TODO
section Linear

open scoped TensorProduct

open Finset LinearMap

variable {R : Type u} [CommRing R]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

theorem Finsupp.sum_eq_one_iff {α : Type*} [DecidableEq α] (d : α →₀ ℕ) :
    Finsupp.sum d (fun _ n ↦ n) = 1 ↔ ∃ a, Finsupp.single a 1 = d := by
  constructor
  · intro h1
    have hd0 : d ≠ 0 := by
      intro h
      simp only [h, Finsupp.sum_zero_index, zero_ne_one] at h1
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hd0
    rw [Finsupp.coe_zero, Pi.zero_apply, ne_eq] at ha
    rw [← Finsupp.add_sum_erase' _ a, Nat.add_eq_one_iff] at h1
    rcases h1 with (⟨ha', _⟩ | ⟨ha, ha'⟩)
    · exact absurd ha' ha
    · use a
      simp only [Finsupp.sum, Finsupp.support_erase, sum_eq_zero_iff, mem_erase] at ha'
      ext b
      by_cases hb : a = b
      · rw [← hb, Finsupp.single_eq_same, ha]
      · rw [Finsupp.single_eq_of_ne hb]
        apply symm
        rw [← Finsupp.not_mem_support_iff, Finsupp.mem_support_iff, ne_eq, not_not]
        simp only [ne_eq, Finsupp.mem_support_iff, and_imp] at ha'
        simpa only [Finsupp.erase_ne (ne_comm.mp hb), _root_.not_imp_self] using ha' b (ne_comm.mp hb)
    exact fun _ ↦ rfl
  · rintro ⟨a, rfl⟩
    rw [Finsupp.sum_eq_single a _ (fun _ ↦ rfl), Finsupp.single_eq_same]
    intro b _ hba
    rw [Finsupp.single_eq_of_ne hba.symm]

theorem isHomogeneousOfDegreeOne_coeff {f : PolynomialLaw R M N} (hf : f.IsHomogeneousOfDegree 1)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (m : ι → M) {d : ι →₀ ℕ}
    (hd : Finsupp.sum d (fun _ n => n) ≠ 1) : (coeff m f) d = 0 :=
  isHomogeneousOfDegree_coeff hf m d hd

-- **MI**: I replaced `ι : Type*` by `ι : Type u`.
theorem isHomogeneousOfDegreeOne_coeff_support_le {f : PolynomialLaw R M N}
    (hf : IsHomogeneousOfDegree 1 f) {ι : Type u} [Fintype ι] [DecidableEq ι] (m : ι → M) :
    (coeff m f).support ⊆ Finset.map
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [Finsupp.mem_support_iff, ne_eq] at hd
  simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
    true_and, Finsupp.sum_eq_one_iff] using
      (not_imp_comm.mp (isHomogeneousOfDegreeOne_coeff hf m)) hd

theorem isHomogeneousOfDegreeOne_coeff_single {f : PolynomialLaw R M N}
    (hf : f.IsHomogeneousOfDegree 1) {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M) (i : ι) :
    (coeff m f) (Finsupp.single i 1) = f.ground (m i) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : Finset.sum Finset.univ (fun (j : ι) => (Pi.single i (1 : R) j) ⊗ₜ[R] m j) =
      1 ⊗ₜ[R] m i := by
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_tmul])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same]
  simp only [← this, image_eq_coeff_sum, map_finsuppSum, lid_tmul]
  sorry
  /- rw [Finsupp.sum_of_support_subset _ (isHomogeneousOfDegreeOne_coeff_support_le hf m),
    sum_map, Function.Embedding.coeFn_mk, sum_eq_single i]
  · rw [Finset.prod_eq_single i (fun j _ hj => by rw [Finsupp.single_eq_of_ne hj.symm, pow_zero])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same,
      one_pow, _root_.one_smul]
  · intro j _ hj
    rw [Finset.prod_eq_zero (i := j), _root_.zero_smul]
    exact Finset.mem_univ _
    rw [Finsupp.single_eq_same, Pi.single_eq_of_ne hj, pow_one]
  · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, smul_zero,
    forall_exists_index, implies_true, forall_const] -/

noncomputable def ofLinearMap (v : M →ₗ[R] N) : PolynomialLaw R M N where
  toFun' S _ _ := v.baseChange S
  isCompat' φ  := by
    ext
    simp only [← LinearMap.comp_apply, baseChange_eq_ltensor, Function.comp_apply,
      rTensor_comp_lTensor, lTensor_comp_rTensor]

lemma ofLinearMap_mem_grade_one (v : M →ₗ[R] N) :
    IsHomogeneousOfDegree 1 (ofLinearMap v) :=
  fun S _ _ r m => by simp only [ofLinearMap, LinearMapClass.map_smul, pow_one]

theorem IsHomogeneousOfDegree.comp_ofLinearMap {P : Type*} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₚₗ[R] P} {q : ℕ} (hg : g.IsHomogeneousOfDegree q) :
    (g.comp (PolynomialLaw.ofLinearMap f)).IsHomogeneousOfDegree q := by
  simpa using IsHomogeneousOfDegree.comp (ofLinearMap_mem_grade_one f) hg

theorem IsHomogeneousOfDegree.ofLinearMap_comp {P : Type*} [AddCommGroup P] [Module R P]
    {f : M →ₚₗ[R] N} {g : N →ₗ[R] P} {p : ℕ} (hf : f.IsHomogeneousOfDegree p) :
    ((PolynomialLaw.ofLinearMap g).comp f).IsHomogeneousOfDegree p := by
  simpa using IsHomogeneousOfDegree.comp hf (ofLinearMap_mem_grade_one g)

theorem ofLinearMap_toFun' (u : M →ₗ[R] N)
    (S : Type u) [CommSemiring S] [Algebra R S] :
    (ofLinearMap u).toFun' S = LinearMap.baseChange S u := rfl

-- **MI**: I replaced `S : Type*` by `S : Type u`.
theorem ofLinearMap_toFun (u : M →ₗ[R] N) (S : Type u) [CommSemiring S] [Algebra R S] :
    (ofLinearMap u).toFun' S = u.baseChange S := rfl
  /- ext sm
  obtain ⟨n, φ, p, rfl⟩ := exists_lift sm
  simp only [← isCompat_apply, toFun_eq_toFun', ofLinearMap_toFun', baseChange_eq_ltensor,
    ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor] -/

open MvPolynomial

theorem ofLinearMap_coeff_single (u : M →ₗ[R] N) (ι : Type*) [DecidableEq ι] [Fintype ι]
    (m : ι → M) (i : ι) : ((coeff m) (ofLinearMap u)) (Finsupp.single i 1) = u (m i) := by
  rw [coeff, generize, coe_comp, LinearEquiv.coe_coe, coe_mk, AddHom.coe_mk, Function.comp_apply]
  sorry/- simp only [ofLinearMap_toFun, map_sum, LinearMap.baseChange_tmul]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single i _ (fun hi => by
    simp only [mem_univ, not_true_eq_false] at hi), scalarRTensor_apply_tmul_apply,
      coeff_X, _root_.one_smul]
  · intro b _ hb
    have hb' : ¬ Finsupp.single b 1 = Finsupp.single i 1 := by
      rwa [Finsupp.single_left_inj]; norm_num
    rw [scalarRTensor_apply_tmul_apply, coeff_X', if_neg hb', _root_.zero_smul] -/

noncomputable def ofLinearMapHom :
    (M →ₗ[R] N) →ₗ[R] (grade 1 : Submodule R (PolynomialLaw R M N)) where
  toFun         := fun u ↦ ⟨ofLinearMap u, ofLinearMap_mem_grade_one u⟩
  map_add' u v  := by
    ext S _ _ m
    simp only [ofLinearMap_toFun', baseChange_add, add_apply, Submodule.coe_add, add_def_apply]
  map_smul' a v := by
    ext S _ _ m
    simp only [smul_def, ofLinearMap_toFun', LinearMap.baseChange_smul]
    rfl

theorem ofLinearMapHom_apply (v : M →ₗ[R] N) : ofLinearMapHom v = ofLinearMap v := rfl

variable {R : Type u} [CommRing R]
  {M N : Type _} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

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

noncomputable def toLinearMap (f : (grade 1 : Submodule R (PolynomialLaw R M N))) :
    M →ₗ[R] N := {
  toFun    := ground (f : PolynomialLaw R M N)
  map_add' := fun m n => by
    obtain ⟨f, hf⟩ := f
    rw [mem_grade, isHomogeneousOfDegree_of_coeff_iff] at hf
    let h := fun (r s : R) ↦ ground_image_eq_coeff_sum_two r s m n f
    have h11 := h 1 1; simp only [_root_.one_smul] at h11
    have h10 := h 1 0; simp only [_root_.one_smul, _root_.zero_smul, _root_.add_zero] at h10
    have h01 := h 0 1; simp only [_root_.one_smul, _root_.zero_smul, _root_.zero_add] at h01
    rw [h01, h10, h11, ← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro x hx
    rw [← _root_.add_smul]
    apply congr_arg₂ _ _ rfl
    simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, one_pow, Matrix.cons_val_one,
      Matrix.head_cons, mul_one, one_mul]
    refine (zero_pow_add_zero_pow _ _ ?_).symm
    suffices Finsupp.sum x (fun _ n => n) = 1 by
      rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)] at this
      simpa only [add_comm, Function.comp_apply, Fin.sum_univ_two] using this
      · exact fun _ ↦ by simp only [mem_univ, forall_true_left]
    simp only [Finsupp.mem_support_iff, ne_eq] at hx
    exact not_imp_comm.mp (hf _ _ x) hx
  map_smul' := fun r x => by
    obtain ⟨f, hf⟩ := f
    rw [mem_grade] at hf
    simp only [RingHom.id_apply, isHomogeneousOfDegree_ground hf, pow_one] }

noncomputable def ofLinearMapEquiv :
    (M →ₗ[R] N) ≃ₗ[R] (grade 1 : Submodule R (PolynomialLaw R M N)) := {
  ofLinearMapHom with
  invFun := toLinearMap
  left_inv := fun f ↦ by
    ext m
    simp only [toLinearMap, ground, ofLinearMapHom, ofLinearMap, AddHom.toFun_eq_coe, AddHom.coe_mk,
      coe_mk, Function.comp_apply, lid_symm_apply, baseChange_tmul, lid_tmul, _root_.one_smul]
  right_inv := fun f ↦ by
    ext S _ _ sm
    obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S sm
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, ofLinearMapHom, LinearMap.coe_mk, AddHom.coe_mk,
      ← toFun_eq_toFun', ofLinearMap_toFun, map_sum, LinearMap.baseChange_tmul]
    sorry
    /- rw [image_eq_coeff_sum, Finsupp.sum_of_support_subset _
      (isHomogeneousOfDegreeOne_coeff_support_le f.prop m), sum_map, Function.Embedding.coeFn_mk]
    apply sum_congr rfl
    · intro i _
      rw [isHomogeneousOfDegreeOne_coeff_single f.prop, prod_eq_single i, Finsupp.single_eq_same,
      pow_one]
      rfl
      · intro j _ hj
        rw [Finsupp.single_eq_of_ne (ne_comm.mp hj), pow_zero]
      · simp only [mem_univ, not_true_eq_false, Finsupp.single_eq_same, pow_one, IsEmpty.forall_iff]
    · simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, tmul_zero,
      forall_exists_index, implies_true, forall_const] -/ }

end Linear
 -/


/- /-- The homogeneous component of degree `p` of a `PolynomialLaw`. -/
@[simps] noncomputable def component (p : ℕ) (f : PolynomialLaw R M N) :
    PolynomialLaw R M N where
  toFun' S _ _ := fun m ↦ rTensor R N S
    (f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M m)) p
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    simp only [Function.comp_apply, rTensor_apply, ← rTensor_comp_apply]
    rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply', ← rTensor_comp_apply,
      Polynomial.baseChange_comp_monomial_eq]-/

/- The multihomogeneous component of degree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def multiComponent' (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N) :
    PolynomialLaw R (M × M') N where
  toFun' S _ _ := fun m ↦ MvPolynomial.rTensor (R := R) (N := N) (S := S)
      (f.toFun' (MvPolynomial (Fin 2) S)
      ((((monomial (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _)))).restrictScalars R).rTensor
        (M × M') m)) (Finsupp.ofSupportFinite (![n.1, n.2]) (Set.toFinite _))
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    simp only [Function.comp_apply, rTensor_apply, ← rTensor_comp_apply]
    rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply', ← rTensor_comp_apply,
      MvPolynomial.baseChange_comp_monomial_eq]

theorem multiComponent_toFun'_apply' (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N)
  (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M')) :
  (f.multiComponent' n).toFun' S m =
  MvPolynomial.rTensor (R := R) (N := N) (S := S)
      (f.toFun' (MvPolynomial (Fin 2) S)
      ((((monomial (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _)))).restrictScalars R).rTensor
        (M × M') m)) (Finsupp.ofSupportFinite (![n.1, n.2]) (Set.toFinite _)) := rfl

theorem multiComponent_toFun_apply' (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N)
  (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M')) :
  (f.multiComponent' n).toFun S m =
  MvPolynomial.rTensor (R := R) (N := N) (S := S)
      (f.toFun (MvPolynomial (Fin 2) S)
      (((monomial (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _))).restrictScalars R).rTensor
        (M × M') m)) (Finsupp.ofSupportFinite (![n.1, n.2]) (Set.toFinite _)) := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, multiComponent_toFun'_apply']
  sorry

lemma multiComponentIsMultiHomogeneousProd (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N) :
    IsMultiHomogeneousOfDegree' n (multiComponent' n f) := by
  --simp only [multiComponent']
  intro S _ _ s sm
  simp only [multiComponent', Nat.succ_eq_add_one, Nat.reduceAdd, Prod.smul_fst, Prod.smul_snd]
  set m11 := (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _))
  let m : MvPolynomial (Fin 2) S :=
    (monomial (R := S) (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _))) s.1

  let ψ : MvPolynomial (Fin 2) S →ₐ[R] MvPolynomial (Fin 2) S :=
    (MvPolynomial.aeval ![s.1 • X 0, 1]).restrictScalars R

  let ψ' : MvPolynomial (Fin 2) S →ₐ[R] MvPolynomial (Fin 2) S :=
    (MvPolynomial.aeval ![1, s.2 • X 1]).restrictScalars R


  suffices (LinearMap.rTensor (M × M')-- (R := R) (N := N) (S := S)
   (((monomial m11).restrictScalars R))
     ((prodRight R S S M M').symm
      ((s.1 • (prodRight R S _ M M') sm).fst, (s.2 • (prodRight R S _ M M') sm).snd))) =
    (rTensor (M × M') (ψ.toLinearMap)) (LinearMap.rTensor (M × M')
      (((monomial m11).restrictScalars R)) ((prodRight R S _ M M').symm
       (((prodRight R S _ M M') sm).fst, 0)))  +
    (rTensor (M × M') (ψ'.toLinearMap)) (LinearMap.rTensor (M × M')
      (((monomial m11).restrictScalars R)) ((prodRight R S _ M M').symm
       (0, ((prodRight R S _ M M') sm).snd))) by
    /- (rTensor (M × M') (ψ.toLinearMap + ψ'.toLinearMap)) (LinearMap.rTensor (M × M')
      (((monomial m11).restrictScalars R)) sm) by -/

    sorry


  /- simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Prod.smul_fst, Prod.smul_snd, Fin.isValue,
    ψ] -/
  simp only [ψ, ψ']
  induction sm using TensorProduct.induction_on with
    | zero => sorry
    | add => sorry
    | tmul t m =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, prodRight_tmul, Prod.smul_mk, Fin.isValue,
        rTensor_tmul, coe_restrictScalars,]

      simp only [smul_tmul', smul_eq_mul, Fin.isValue]
      have h : ((prodRight R S S M M').symm ((s.1 * t) ⊗ₜ[R] m.1, (s.2 * t) ⊗ₜ[R] m.2)) =
         ((s.1 * t) ⊗ₜ[R] (m.1, 0) + (s.2 * t) ⊗ₜ[R] (0, m.2)) := by

        sorry
      have h2 : (prodRight R S S M M').symm (0, t ⊗ₜ[R] m.2) = t ⊗ₜ[R] (0, m.2) := by
        have : (0 : S ⊗ M) = t ⊗ₜ[R] 0 := sorry
        rw [this, prodRight_symm_tmul]

      have h1 : (prodRight R S S M M').symm (t ⊗ₜ[R] m.1, 0) = t ⊗ₜ[R] (m.1, 0) := by
        have : (0 : S ⊗ M') = t ⊗ₜ[R] 0 := sorry
        rw [this, prodRight_symm_tmul]

      /- have h1 : ((prodRight R S S M M').symm (0, ((prodRight R S S M M') (t ⊗ₜ[R] m)).2)) =
        (t ⊗ₜ[R] (0, m.2)) := by
        have : (0 : S ⊗ M) = t ⊗ₜ[R] 0 := sorry
        simp only [prodRight_tmul, this]
        rw [prodRight_symm_tmul] -/
      rw [h, map_add, h1, h2]
      simp only [rTensor_tmul, coe_restrictScalars, Fin.isValue, ]
      simp only [Fin.isValue,  AlgHom.toLinearMap_apply,
        AlgHom.coe_restrictScalars']
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
      have : ((algebraMap S (MvPolynomial (Fin 2) S)) t * m11.prod
        fun i k ↦ ![s.1 • X 0, s.2 • X 1] i ^ k) ⊗ₜ[R] m =
          ((algebraMap S (MvPolynomial (Fin 2) S)) t *
            m11.prod fun i k ↦ ![s.1 • X 0, s.2 • X 1] i ^ k) ⊗ₜ[R]
          (m.1, 0) + ((algebraMap S (MvPolynomial (Fin 2) S)) t * m11.prod
          fun i k ↦ ![s.1 • X 0, s.2 • X 1] i ^ k) ⊗ₜ[R] (0, m.2) := by
          simp [← tmul_add]
      simp only [algebraMap_eq, Fin.isValue, Finsupp.prod_pow, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hm110 : m11 0 = 1 := by
        calc m11 0
          _ = ![1, 1] 0 := rfl
          _ = 1 := by simp

      have hm111 : m11 1 = 1 := by
        calc m11 1
          _ = ![1, 1] 1 := rfl
          _ = 1 := by simp
      simp only [Fin.isValue, hm110, pow_one, hm111, mul_one, Algebra.mul_smul_comm,
        one_mul]
      congr
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, m11]
        sorry

      sorry
      --have : (monomial m11) (s.1 * t) ⊗ₜ[R] (m.1, 0) =
      --rw [this]
      /- congr
      · ext d
        simp only [coeff_monomial, algebraMap_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
          Finsupp.prod_pow, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, coeff_C_mul]
        simp only [Fin.isValue, coeff_mul]

        have hm110 : m11 0 = 1 := by
          calc m11 0
            _ = ![1, 1] 0 := rfl
            _ = 1 := by simp

        have hm111 : m11 1 = 1 := by
          calc m11 1
            _ = ![1, 1] 1 := rfl
            _ = 1 := by simp

        simp only [Fin.isValue, hm110, pow_one, coeff_smul, smul_eq_mul, hm111]

        sorry
      · sorry -/
      /- rw [← rTensor_comp_apply, LinearMap.rTensor_def]
      simp only [← rTensor_comp_apply] -/


  --apply LinearMap.congr_fun



  #exit

  /- simp only [this, ← rTensor_comp_apply]
      apply LinearMap.congr_fun
      apply congr_arg
      rw [LinearMap.ext_iff]
      intro r
      simp only [smul_eq_mul, coe_comp, coe_restrictScalars, Function.comp_apply,
        IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply]
      rw [mul_comm]
      simp only [AlgHom.coe_restrictScalars', aeval_monomial, pow_one, ψ, ← smul_eq_mul,
        algebraMap_smul, Polynomial.smul_monomial] -/

  intro sm
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

  have : ((prodRight R S S M M').symm
    ((s.1 • (prodRight R S S M M') sm).fst, (s.2 • (prodRight R S S M M') sm).snd)) =
      (s.1 * s.2) • sm := by
    have hinj : Function.Injective (prodRight R S S M M') :=
      LinearEquiv.injective (prodRight R S S M M')
    rw [← Function.Injective.eq_iff hinj]
    simp only [Prod.smul_fst, Prod.smul_snd, LinearEquiv.apply_symm_apply, map_smul]
    induction sm using TensorProduct.induction_on with
    | zero => sorry
    | add => sorry
    | tmul =>
      simp only [prodRight_tmul, Prod.smul_mk, Prod.mk.injEq]

    sorry
  sorry


  #exit
  suffices  (MvPolynomial.rTensor-- (R := R) (N := N) (S := S)
   ((monomial (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _))).restrictScalars R))
    ((s.1 • (prodRight R S _ M M') sm).fst, (s.2 • (prodRight R S _ M M') sm).snd)
      = 0/- (rTensor M ψ.toLinearMap) (MvPolynomial.rTensor
      -- (R := R) (N := N) (S := S)
       ((monomial (Finsupp.ofSupportFinite (![1, 1]) (Set.toFinite _))).restrictScalars R) sm) -/ by
    rw [this, ← f.isCompat_apply' ψ]
    generalize toFun' f S[X] (rTensor M ((monomial 1).restrictScalars R) sm) = t
    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (s ^ p)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    apply symm
    dsimp only [LinearMap.rTensor, TensorProduct.map]
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
            one_mul, ← C_eq_algebraMap]
          simp only [C_mul_monomial, coeff_monomial, if_pos]
        . simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, ← C_eq_algebraMap,
            monomial_pow, one_mul, C_mul_monomial, coeff_monomial, if_neg h]
  .  --
    suffices ∀ (sm : S ⊗[R] M), s • sm =
        rTensor M (((IsLinearMap.isLinearMap_smul s).mk').restrictScalars R) sm by
      sorry/- simp only [this, ← rTensor_comp_apply]
      apply LinearMap.congr_fun
      apply congr_arg
      rw [LinearMap.ext_iff]
      intro r
      simp only [smul_eq_mul, coe_comp, coe_restrictScalars, Function.comp_apply,
        IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply]
      rw [mul_comm]
      simp only [AlgHom.coe_restrictScalars', aeval_monomial, pow_one, ψ, ← smul_eq_mul,
        algebraMap_smul, Polynomial.smul_monomial] -/
    --
    /- intro sm
    rw [← (IsLinearMap.isLinearMap_smul s).mk'_apply, ← LinearMap.coe_restrictScalars R]
    apply LinearMap.congr_fun
    dsimp only [LinearMap.rTensor, TensorProduct.map, smul_eq_mul]
    apply lift.unique
    intro r m
    simp only [coe_restrictScalars, IsLinearMap.mk'_apply, compl₂_id, coe_comp, Function.comp_apply,
      mk_apply, smul_tmul', smul_eq_mul] -/


    sorry


end




#exit

section Components

-- I need `ι : Type u` to be able to apply `f.toFun'`.
-- Update: I changed to `ι : Type*` and using `toFun`.
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

open MvPolynomial

noncomputable def el (m : Π i, M i) : MvPolynomial ι R ⊗[R] (Π i, M i) :=
  ∑ (i : ι), (X i) ⊗ₜ Pi.single i (m i)

noncomputable def el' (m : Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    MvPolynomial ι R ⊗[R] N := f.toFun (MvPolynomial ι R) (el m)

noncomputable def coeff_el' (m : Π i, M i) (f : PolynomialLaw R (Π i, M i) N) (n : ι →₀ ℕ) : N :=
  TensorProduct.lid R N (MvPolynomial.rTensor (el' m f) n)

variable {S : Type*} [CommSemiring S] [Algebra R S]

/- noncomputable def el_S (m : S ⊗[R] Π i, M i) : MvPolynomial ι R ⊗[R] (S ⊗[R] (Π i, M i)) :=
  ∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
    (Pi.single (M := fun i ↦  S ⊗[R] M i) i (TensorProduct.piRight R R S _ m i))

noncomputable def el_S' (m : S ⊗[R] Π i, M i) : (MvPolynomial ι R ⊗[R] S) ⊗[R] (Π i, M i) :=
  (TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm (el_S m)

example : (MvPolynomial ι R ⊗[R] S) ≃ₐ[R] (MvPolynomial ι S) := by
  exact scalarRTensorAlgEquiv

noncomputable def el_S'' (m : S ⊗[R] Π i, M i) : (MvPolynomial ι S) ⊗[R] (Π i, M i) :=
  LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv (el_S' m) -/

/- noncomputable def el_S''' (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    MvPolynomial ι S ⊗[R] N := f.toFun' (MvPolynomial ι S) (el_S'' m) -/

variable (ι R S M)

noncomputable def el_S_hom : (S ⊗[R] Π i, M i) →ₗ[R] MvPolynomial ι R ⊗[R] (S ⊗[R] (Π i, M i)) where
  toFun := fun m ↦ ∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
    (Pi.single (M := fun i ↦  S ⊗[R] M i) i (TensorProduct.piRight R R S _ m i))
  map_add' m m'  := by
    simp only [piRight_apply, map_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← TensorProduct.tmul_add]
    congr
    simp only [Pi.single_add, map_add]
  map_smul' r m := by
    simp only [map_smul, piRight_apply, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← tmul_smul, Pi.single_smul, map_smul]

noncomputable def el_S'_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι R ⊗[R] S) ⊗[R] (Π i, M i) :=
  (TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm.comp (el_S_hom ι R M S)

noncomputable def el_S''_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι S) ⊗[R] (Π i, M i) :=
  (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv).comp (el_S'_hom ι R M S)

variable {ι R M S}

noncomputable def el_S''' (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    MvPolynomial ι S ⊗[R] N := f.toFun (MvPolynomial ι S) (el_S''_hom ι R M S m)

noncomputable def coeff_el'_S (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N)
    (n : ι →₀ ℕ) : S ⊗[R] N := MvPolynomial.rTensor (el_S''' m f) n

lemma coeff_el'_S_apply (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) (n : ι →₀ ℕ) :
  coeff_el'_S m f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
    (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
    ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
    (∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
    (Pi.single (M := fun i ↦  S ⊗[R] M i) i (TensorProduct.piRight R R S _ m i)))))) n := rfl

lemma coeff_el'_S_def (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    coeff_el'_S m f = (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))) := by
  ext n
  simp only [coeff_el'_S_apply, piRight_apply, map_sum]

/- Here we define the multihomogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

-- **MI**: this proof is really slow.
theorem bar (n : ι →₀ ℕ) (f : ((i : ι) → M i) →ₚₗ[R] N) {S' : Type*} [CommSemiring S']
    [Algebra R S'] (φ : S →ₐ[R] S')
    (sm : S ⊗[R] ((i : ι) → M i)) :
    (LinearMap.rTensor N φ.toLinearMap) (coeff_el'_S sm f n) =
    coeff_el'_S ((LinearMap.rTensor ((i : ι) → M i) φ.toLinearMap) sm) f n := by
  simp only [coeff_el'_S_def, rTensor_apply, ← rTensor_comp_apply]
  rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply, map_sum]
  congr 3
  ext i
  induction sm using TensorProduct.induction_on with
  | zero => simp [map_zero, Pi.single_zero, tmul_zero]
  | tmul s m =>
      simp only [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul, rTensor_tmul,
        AlgHom.toLinearMap_apply]
      apply foo
  | add sm sm' hsm hsm' =>
      simp [map_add, Pi.add_apply, Pi.single_add, tmul_add, ← hsm, ← hsm']

/- The multihomogeneous component of degree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def multiComponent (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    PolynomialLaw R (Π i, M i) N where
  toFun' S _ _ := fun m ↦ coeff_el'_S m f n
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    apply bar

theorem multiComponent.toFun'_apply (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N)
  (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
  (f.multiComponent n).toFun' S m = coeff_el'_S m f n := rfl

-- **MI**: I replaced  `CommRing S` by `CommSemiring S` and `S : Type u` by `S : Type*`.
theorem multiComponent_toFun_apply (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N)
    (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (f.multiComponent n).toFun S m = coeff_el'_S m f n := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, multiComponent.toFun'_apply]
  exact bar n f ψ q

lemma multiComponentIsMultiHomogeneous [Fintype ι] (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    IsMultiHomogeneousOfDegree n (multiComponent n f) := by
  simp only [multiComponent, coeff_el'_S_apply]
  intro S _ _ s sm
  -- simp only [finsum_eq_sum_of_fintype, finprod_eq_prod_of_fintype]
  have that : (∏ (i : ι), s i ^ n i) •
    ((MvPolynomial.rTensor
        (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i,
                X i ⊗ₜ[R] (piRight R R S M).symm (Pi.single i ((piRight R R S M)
                ((piRight R R S M).symm sm) i))))))) n) =
    ((∏ (i : ι), s i ^ n i) •
    (MvPolynomial.rTensor
        (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i,
                X i ⊗ₜ[R] (piRight R R S M).symm (Pi.single i ((piRight R R S M)
                ((piRight R R S M).symm sm) i)))))))) n := rfl -- TODO: Extract general rw lemma

  rw [that, ← map_smul]
  simp only [LinearEquiv.apply_symm_apply, map_sum, rTensor_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply]
  clear that
  rw [← rTensor_smul']
  sorry


/- lemma multiComponentIsMultiHomogeneous [Fintype ι] (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    IsMultiHomogeneousOfDegree n (multiComponent n f) := by
  intro S _ _ s sm
  simp only [multiComponent, coeff_el'_S_apply]
  simp only [finsum_eq_sum_of_fintype, finprod_eq_prod_of_fintype]
  simp only [map_sum]
  have (i : ι) : (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (X i ⊗ₜ[R]
                (piRight R R S M).symm
                  (Pi.single i ((piRight R R S M) ((piRight R R S M).symm fun i ↦ s i • sm i) i)))) = ?_RHS := by
    simp
    sorry
  have (i : ι) : (piRight R R S M).symm
                  (Pi.single i ((piRight R R S M) ((piRight R R S M).symm fun i ↦ s i • sm i) i)) =
      ?A := by -- (Pi.single i (sm i)) := by
    rw [LinearEquiv.symm_apply_eq]
    simp
    ext j
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same]
      sorry
    · rw [Pi.single_eq_of_ne hj]
      sorry



  have that : (∏ᶠ (i : ι), s i ^ n i) •
    ((MvPolynomial.rTensor
        (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i,
                X i ⊗ₜ[R] (piRight R R S M).symm (Pi.single i ((piRight R R S M)
                ((piRight R R S M).symm sm) i))))))) n) =
    ((∏ᶠ (i : ι), s i ^ n i) •
    (MvPolynomial.rTensor
        (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i,
                X i ⊗ₜ[R] (piRight R R S M).symm (Pi.single i ((piRight R R S M)
                ((piRight R R S M).symm sm) i)))))))) n := rfl -- TODO: Extract general rw lemma

  rw [that, ← map_smul]
  simp only [LinearEquiv.apply_symm_apply, map_sum, rTensor_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply]
  sorry -/

theorem multiComponent_add (n : ι →₀ ℕ) (f g : PolynomialLaw R (Π i, M i) N) :
    (f + g).multiComponent n = f.multiComponent n + g.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, coeff_el'_S_apply, piRight_apply, map_sum, add_toFun_apply, map_add,
    Finsupp.coe_add, Pi.add_apply, add_def]

theorem multiComponent_smul (n : ι →₀ ℕ) (r : R) (f : PolynomialLaw R (Π i, M i) N) :
    (r • f).multiComponent n = r • f.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, coeff_el'_S_apply, piRight_apply, map_sum, smul_toFun, Pi.smul_apply,
    rTensor_apply, map_smul, smul_def]

-- Perhaps I should just use `ι →₀ ℕ` everywhere, but since I am usually assuming `Fintype ι`,
-- this seemed redundant.
-- For now, I used it in the def. of `multiComponent` to avoid this error:
/- ... has Finset (ι →₀ ℕ) : Type u but is expected to have type Set (ι → ℕ) : Type u-/
 theorem support_multiComponent' (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun' S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))).support := by
  ext n
  simp [multiComponent, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, coeff_el'_S_def]

-- **MI**: I replaced  `CommRing S` by `CommSemiring S`.
theorem support_multiComponent (f : (Π i, M i) →ₚₗ[R] N) {S : Type*} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))).support := by
  ext i
  rw [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_iff_not,
    multiComponent_toFun_apply, coeff_el'_S_def]

theorem LocFinsupp_multiComponent (f : PolynomialLaw R (Π i, M i) N) :
    LocFinsupp (fun n ↦ f.multiComponent n) := fun S _ _ m ↦ by
  rw [support_multiComponent']
  exact Finset.finite_toSet _

 theorem LocFinsupp_multiComponent_eq (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (Finsupp.ofSupportFinite (fun i => (multiComponent i f).toFun' S m)
      (LocFinsupp_multiComponent f S m)) =
    MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x)))))) := by
  ext n
  simp only [multiComponent, coeff_el'_S_apply, piRight_apply, map_sum, Finsupp.ofSupportFinite_coe]

open Finsupp

-- TODO: golf, extract lemmas
theorem asdf (S : Type u) [CommSemiring S] [Algebra R S] (s : S) (m : (i : ι) → M i) :
  s ⊗ₜ[R] m =
    ∑ i, (aeval 1) (scalarRTensorAlgEquiv (X i ⊗ₜ[R] s)) ⊗ₜ[R] Pi.single i (m i) := by
  by_cases hR : Nontrivial R
  · have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
    conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    --simp only [aeval_def, Algebra.id.map_eq_id, eval₂_map, RingHomCompTriple.comp_eq]
    simp only [rTensorAlgHom_apply_eq]
    --simp_rw [map_finsuppSum]

    simp only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul]
    simp only [Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    have : Finsupp.support (X (R := R) i) = {Finsupp.single i 1} := by
      rw [← support_X (R := R)]; rfl

    rw [this]
    simp only [Finset.sum_singleton, map_zero, Finsupp.prod_single_index, mul_one,
      Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]
    have : s = (1 : R) • s := by simp only [_root_.one_smul]
    convert this
    rw [X]
    simp only [monomial, AddMonoidAlgebra.lsingle, Finsupp.lsingle, Finsupp.singleAddHom,
      ZeroHom.toFun_eq_coe, ZeroHom.coe_mk]
    change (Finsupp.single (Finsupp.single i 1) 1) (Finsupp.single i 1) = 1
    simp only [Finsupp.single_eq_same]
  · simp only [nontrivial_iff, ne_eq, not_exists, not_not] at hR
    have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
    conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    --simp only [aeval_def, Algebra.id.map_eq_id, eval₂_map, RingHomCompTriple.comp_eq]
    simp only [rTensorAlgHom_apply_eq]
    --simp_rw [map_finsuppSum]

    simp only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul]
    simp only [Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    have : Finsupp.support (X (R := R) i) = ∅ := by
      have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X (R := R) i) := by
        rw [support]
      classical rw [this, X, support_monomial, if_pos (hR 1 0)]
    rw [this]
    simp only [Finset.sum_empty, Finsupp.sum_zero_index]
    have h1 : (1 : S) = algebraMap R S 1 := by simp only [map_one]
    rw [← mul_one s, ← map_one (algebraMap R S), hR 1 0, map_zero, mul_zero]

/-- A polynomial law is the locally finite sum of its homogeneous components.
(PolynomialLaw lies in between the direct sum and the product of its graded submodules,
hence there is no graded module structure.) -/
theorem recompose_multiComponent {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type u}
  [CommSemiring R] {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (f : PolynomialLaw R (Π i, M i) N) :
    PolynomialLaw.lfsum (fun n ↦ f.multiComponent n) = f := by
  ext S _ _ sm
  rw [lfsum_eq_of_locFinsupp (LocFinsupp_multiComponent f), LocFinsupp_multiComponent_eq]
  have hsm' : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor (Π i, M i) (∑ x,
    (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) sm x))))) := by
    simp only [map_sum]
    simp only [LinearMap.rTensor]
    induction sm using TensorProduct.induction_on with
    | zero =>  simp [map_zero, Pi.single_zero, tmul_zero, Finset.sum_const_zero]
    | tmul s m =>
        simp only [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul]
        simp only [LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_tmul,
          AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', id_coe, id_eq]
        apply asdf
    | add sm₁ sm₂ hsm₁ hsm₂ => simp [map_add, Pi.add_apply, Pi.single_add, tmul_add, Finset.sum_add_distrib,
        ← hsm₁, ← hsm₂]
  conv_rhs => rw [← toFun_eq_toFun', hsm', ← f.isCompat_apply]
  generalize f.toFun (MvPolynomial ι S)
    (∑ x,
            (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
              ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
                (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) sm x))))) = sn
  convert rTensor'_sum (R := R) (fun _ ↦ 1) sn
  · simp only [_root_.one_smul]
  · ext p
    simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', aeval_eq_eval₂Hom,
      Algebra.algebraMap_self, coe_eval₂Hom, eval₂_id, eval_eq, Pi.ofNat_apply, one_pow,
      Finset.prod_const_one, mul_one, MvPolynomial.lsum, coe_restrictScalars, lsmul_apply,
      smul_eq_mul, one_mul, coe_mk, AddHom.coe_mk]
    rfl
end Components

end MultiHomogeneous

end PolynomialLaw

#exit



/-- `f.multiComponent n` is homogeneous of degree `n`. -/
lemma multiComponentIsMultiHomogeneous (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    IsMultiHomogeneousOfDegree n (f.multiComponent n) := by
  intro S _ _ s sm
  dsimp [multiComponent]
  have := (fun (i : ι) ↦ (monomial (R := S) (σ := ι)
    (Finsupp.ofSupportFinite (fun _ ↦ 1) (Set.toFinite _))))
  let ψ : MvPolynomial ι S →ₐ[R] MvPolynomial ι S :=
    (aeval (R := S) (S₁ := MvPolynomial ι S) (fun i ↦ (monomial
      (Finsupp.ofSupportFinite (fun _ ↦ 1) (Set.toFinite _))) (s i))).restrictScalars R
  suffices (rTensor (Π i, M i) ((monomial (R := S) (σ := ι)
      (Finsupp.ofSupportFinite (fun _ ↦ 1) (Set.toFinite _))).restrictScalars R))
        ((TensorProduct.piRight R R _ _).symm (s • sm))
      = (rTensor (Π i, M i) ψ.toLinearMap) ((rTensor (Π i, M i) ((monomial (R := S) (σ := ι)
        (Finsupp.ofSupportFinite (fun _ ↦ 1) (Set.toFinite _))).restrictScalars R)
          ((TensorProduct.piRight R R _ _).symm sm))) by
    sorry
  --
  sorry
  /- intro sm
  rw [← (IsLinearMap.isLinearMap_smul s).mk'_apply, ← LinearMap.coe_restrictScalars R]
  apply LinearMap.congr_fun
  dsimp only [LinearMap.rTensor, TensorProduct.map, smul_eq_mul]
  apply lift.unique
  intro r m
  simp only [coe_restrictScalars, IsLinearMap.mk'_apply, compl₂_id, coe_comp, Function.comp_apply,
    mk_apply, smul_tmul', smul_eq_mul]  -/
    /- rw [this, ← f.isCompat_apply' ψ]
    generalize toFun' f S[X] (rTensor M ((monomial 1).restrictScalars R) sm) = t
    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (s ^ p)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    apply symm
    dsimp only [LinearMap.rTensor, TensorProduct.map]
    apply TensorProduct.lift.unique
    intro f n
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, lift.tmul,
      lcoeff_apply, mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply,
      AlgHom.coe_restrictScalars', TensorProduct.smul_tmul']
    apply congr_arg₂ _ _ rfl
    -- ψ f = f (s • X)
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | monomial n a =>
        simp only [ψ, aeval_monomial, ← smul_eq_mul, algebraMap_smul, coeff_smul, monomial_pow,
          one_mul, coeff_monomial]
        split_ifs with h
        . rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial, monomial_pow,
            one_mul, ← C_eq_algebraMap]
          simp only [C_mul_monomial, coeff_monomial, if_pos]
        . simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, ← C_eq_algebraMap,
            monomial_pow, one_mul, C_mul_monomial, coeff_monomial, if_neg h]
  .  --
    suffices ∀ (sm : S ⊗[R] M), s • sm =
        rTensor M (((IsLinearMap.isLinearMap_smul s).mk').restrictScalars R) sm by
      simp only [this, ← rTensor_comp_apply]
      apply LinearMap.congr_fun
      apply congr_arg  /- have hsm : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor (Π i, M i) (((monomial
      (Finsupp.ofSupportFinite (fun (_ : ι) ↦ 1) (Set.toFinite _))).restrictScalars R).rTensor
        (Π i, M i) sm) := by
    rw [← LinearMap.rTensor_comp_apply, LinearMap.rTensor, eq_comm]
    convert DFunLike.congr_fun TensorProduct.map_id sm
    ext s
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.coe_restrictScalars', aeval_monomial, Algebra.id.map_eq_id, RingHom.id_apply,
      Finsupp.prod, Pi.ofNat_apply, one_pow, Finset.prod_const_one, mul_one, id_coe, id_eq] -/

  -- This might not be right
      rw [LinearMap.ext_iff]
      intro r
      simp only [compl₂_id, smul_eq_mul, lift.tmul, coe_comp, coe_restrictScalars,
        Function.comp_apply, IsLinearMap.mk'_apply, mk_apply, AlgHom.toLinearMap_apply,
        AlgHom.coe_restrictScalars', aeval_monomial, pow_one]
      rw [mul_comm]
      simp only [AlgHom.coe_restrictScalars', aeval_monomial, pow_one, ψ, ← smul_eq_mul,
        algebraMap_smul, Polynomial.smul_monomial]
    --
    intro sm
    rw [← (IsLinearMap.isLinearMap_smul s).mk'_apply, ← LinearMap.coe_restrictScalars R]
    apply LinearMap.congr_fun
    dsimp only [LinearMap.rTensor, TensorProduct.map, smul_eq_mul]
    apply lift.unique
    intro r m
    simp only [coe_restrictScalars, IsLinearMap.mk'_apply, compl₂_id, coe_comp, Function.comp_apply,
      mk_apply, smul_tmul', smul_eq_mul] -/
