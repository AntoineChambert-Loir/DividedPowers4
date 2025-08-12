/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.PolynomialLaw.MultiHomogeneous
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod

universe u uι

/- # Bihomogeneous components of a polynomial map

-/

noncomputable section

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R]

variable {M M' N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N] [Module R N]

open LinearMap TensorProduct

section BiHomogeneous

open Finsupp MvPolynomial

open TensorProduct

def IsBiHomogeneousOfDegree (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (s : S × S) (m : S ⊗[R] (M × M')),
    f.toFun' S (s.1 • TensorProduct.compFstRight R S S M M' m +
      s.2 • TensorProduct.compSndRight R S S M M' m) = (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun' S m

theorem IsBiHomogeneousOfDegree_add (n : ℕ × ℕ) {f g : PolynomialLaw R (M × M') N}
    (hf : f.IsBiHomogeneousOfDegree n) (hg : g.IsBiHomogeneousOfDegree n) :
    (f + g).IsBiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsBiHomogeneousOfDegree_smul (n : ℕ × ℕ) (r : R) {f : PolynomialLaw R (M × M') N}
    (hf : f.IsBiHomogeneousOfDegree n) :
    (r • f).IsBiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp [smul_def, Pi.smul_apply, hf S, smul_comm r]

/-- The submodule of bihomogeneous polynomial laws of degree `n`. -/
def biGrade (n : ℕ × ℕ) : Submodule R (PolynomialLaw R (M × M') N) where
  carrier            := IsBiHomogeneousOfDegree n
  add_mem' hf hg     := IsBiHomogeneousOfDegree_add n hf hg
  smul_mem' r f hf   := IsBiHomogeneousOfDegree_smul n r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_biGrade (f : PolynomialLaw R (M × M') N) (n : ℕ × ℕ) :
    f ∈ biGrade n ↔ IsBiHomogeneousOfDegree n f := by rfl

lemma isBiHomogeneousOfDegree_toFun {n : ℕ × ℕ} {f : PolynomialLaw R (M × M') N}
    (hf : IsBiHomogeneousOfDegree n f) (S : Type*) [CommSemiring S] [Algebra R S] (s : S × S)
    (m : S ⊗[R] (M × M')) :
    f.toFun S (s.1 • TensorProduct.compFstRight R S S M M' m +
      s.2 • TensorProduct.compSndRight R S S M M' m) =
      (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun S m := by
  choose d ψ m' r' hm' hr1 hr2 using PolynomialLaw.exists_lift_pair m s
  simp only [← hr1, ← hm', ← hr2, ← map_pow, ← map_mul, ← isCompat_apply, toFun_eq_toFun',
    smul_rTensor]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  simp only [compFstRight, inlRight, fstRight, coe_comp, LinearEquiv.coe_coe, coe_inl, coe_fst,
    Function.comp_apply, compSndRight, inrRight, sndRight, coe_inr, coe_snd]
  apply congr_arg
  simp only [map_add, ← smul_rTensor]
  congr <;>
  rw [LinearEquiv.symm_apply_eq] <;>
  simp [Prod.ext_iff, prodRight_rTensor_fst_eq_rTensor_prodRight',
      LinearEquiv.apply_symm_apply, prodRight_rTensor_snd_eq_rTensor_prodRight']

/-- If `f` is bihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isBiHomogeneousOfDegree_ground {n : ℕ × ℕ} {f : PolynomialLaw R (M × M') N}
    (hf : IsBiHomogeneousOfDegree n f) (r : R × R) (m : (M × M')) :
    f.ground ((r.1 • m.1, r.2 • m.2)) = (r.1^n.1 * r.2^n.2) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (M × M')).symm m)
  simp only [lid_symm_apply] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply, ← map_smul, ← hfrm]
  congr
  simp only [prod_right_ext_iff R, map_add, fstRight_compFstRight_eq, fstRight_compSndRight_eq,
    sndRight_compFstRight_eq, sndRight_compSndRight_eq]
  simp [fstRight, sndRight]

theorem IsBiHomogeneousOfDegree.comp {P : Type*} [AddCommMonoid P] [Module R P]
    {f : (M × M') →ₚₗ[R] N} {g : N →ₚₗ[R] P} {p : ℕ × ℕ} {q : ℕ}
    (hf : f.IsBiHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsBiHomogeneousOfDegree (q • p) := by
  intro S _ _ r m
  simp [comp_toFun', Function.comp_apply, hf S, hg S, nsmul_eq_mul, Prod.fst_mul,
    Prod.fst_natCast, Nat.cast_id, mul_comm q, pow_mul, Prod.snd_mul, Prod.snd_natCast, mul_pow]

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isBiHomogeneousOfDegree_coeff {n : ℕ × ℕ} {f : PolynomialLaw R (M × M') N}
    (hf : IsBiHomogeneousOfDegree n f)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (m : ι → (M × M')) (d : ι →₀ ℕ)
    (hd : d.sum (fun _ m => m) ≠ n.1 + n.2) :
    PolynomialLaw.coeff m f d = 0 := by
  sorry
  /- classical
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
  have hf' := isBiHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (X none, X none) μ
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
    exact he_some d _ i -/

theorem toFun_sum_tmul_eq_coeff_sum' (f : PolynomialLaw R (M × M') N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M × M') (S : Type*)
    [CommSemiring S] [Algebra R S] (r : ι → S) :
    f.toFun S (∑ i, r i ⊗ₜ[R] m i) = (coeff m f).sum (fun k n ↦ (∏ i, r i ^ k i) ⊗ₜ[R] n) := by
  sorry/- have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [aeval_monomial] -/

theorem toFun_sum_tmul_eq_coeff_sum'' (f : PolynomialLaw R (M × M') N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M × M') (S : Type*)
    [CommSemiring S] [Algebra R S] (r : ι → S × S) :
    f.toFun S (∑ i,((r i).1 ⊗ₜ[R] ((m i).1, 0) + (r i).2 ⊗ₜ[R] (0, (m i).2))) =
      (coeff m f).sum (fun k n ↦ (∏ i, (r i).1 ^ k i) ⊗ₜ[R] n) := by
  sorry/- have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [aeval_monomial] -/

/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isBiHomogeneousOfDegree_of_coeff_iff (f : PolynomialLaw R (M × M') N) (p : ℕ × ℕ) :
    IsBiHomogeneousOfDegree p f ↔ ∀ (n : ℕ)
      (m : (Fin n) → M × M') (d : (Fin n) →₀ ℕ)
      (_ : d.sum (fun _ n => n) ≠ p.1 + p.2), PolynomialLaw.coeff m f d = 0 := by
  refine ⟨fun hf _ m d hd => isBiHomogeneousOfDegree_coeff hf m d hd, fun H S _ _ r μ => ?_⟩
  /- obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
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

  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum] -/

  sorry

end BiHomogeneous
