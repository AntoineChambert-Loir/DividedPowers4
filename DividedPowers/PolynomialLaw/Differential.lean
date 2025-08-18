import DividedPowers.PolynomialLaw.BiHomogeneous
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

open MvPolynomial TensorProduct

universe u

variable (R : Type u) [CommSemiring R] (M M' : Type*) [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {N : Type*} [AddCommGroup N] [Module R N]
  (f : M →ₚₗ[R] N) (n p : ℕ)

namespace PolynomialLaw

section Polarized

/-- `fst R M M'` is the polynomial law `M × M' →ₚₗ[R] M` obtained by prolonging the
`i`th canonical projection. -/
def fst : M × M' →ₚₗ[R] M where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.fst R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma fst_apply (m : M × M') : fst R M M' m = m.1 := by simp [fst, ground_apply]

lemma fst_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (fst R M M').toFun' S m =
    ((TensorProduct.prodRight R R S M  M') m).fst := by
  simp only [fst, TensorProduct.prodRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

lemma fst_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (fst R M M').toFun S m =
    ((TensorProduct.prodRight R R S M  M') m).fst := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (fst R M M').isCompat_apply, PolynomialLaw.toFun_eq_toFun']
  simp only [fst_toFun'_apply, prodRight_rTensor_fst_eq_rTensor_prodRight]

/-- `fst R M M'` is the polynomial law `M × M' →ₚₗ[R] M` obtained by prolonging the
`i`th canonical projection. -/
def snd : M × M' →ₚₗ[R] M' where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.snd R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma snd_apply (m : M × M') : snd R M M' m = m.2 := by simp [snd, ground_apply]

lemma snd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (snd R M M').toFun' S m =
    ((TensorProduct.prodRight R R S M  M') m).snd := by
  simp only [snd, TensorProduct.prodRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

lemma snd_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (snd R M M').toFun S m =
    ((TensorProduct.prodRight R R S M  M') m).snd := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (snd R M M').isCompat_apply, PolynomialLaw.toFun_eq_toFun']
  simp only [snd_toFun'_apply, prodRight_rTensor_snd_eq_rTensor_prodRight]

/-- `sum_proj R M ι` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] M` defined as the sum of all the
coordinate laws from  `(Π (_ : ι), M)`to `M`. -/
def sum_fst_snd : M × M →ₚₗ[R] M := fst R M M + snd R M M

lemma sum_fst_snd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M)} : (sum_fst_snd R M).toFun' S m =
    ((TensorProduct.prodRight R R S M M) m).fst +
      ((TensorProduct.prodRight R R S M M) m).snd := by
  rw [sum_fst_snd, TensorProduct.prodRight]
  simp only [add_def, Pi.add_apply, fst_toFun'_apply, snd_toFun'_apply, LinearEquiv.ofLinear_apply,
    TensorProduct.AlgebraTensorModule.lift_apply, LinearMap.restrictScalars_comp]
  congr 1

def inl : M →ₚₗ[R] M × M' where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.inl R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma inl_apply (m : M) : inl R M M' m = (m, 0) := by simp [inl, ground_apply]

lemma inl_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M} :
    (inl R M M').toFun' S m = ((TensorProduct.inlRight R R S M M') m) := by
  simp only [inl, TensorProduct.inlRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have h0 : (0 : S ⊗[R] M') = s ⊗ₜ 0 := by simp
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.coe_inl,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h0,
      TensorProduct.prodRight_symm_tmul]
  | add m m' hm hm' =>
    simp [map_add, hm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hm']

lemma inl_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M} :
    (inl R M M').toFun S m = ((TensorProduct.inlRight R R S M M') m) := by sorry

def inr : M' →ₚₗ[R] M × M' where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.inr R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma inr_apply (m : M') : inr R M M' m = (0, m) := by simp [inr, ground_apply]

lemma inr_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M'} :
    (inr R M M').toFun' S m = ((TensorProduct.inrRight R R S M M') m) := by
  simp only [inr, TensorProduct.inrRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have h0 : (0 : S ⊗[R] M) = s ⊗ₜ 0 := by simp
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.coe_inr,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h0,
      TensorProduct.prodRight_symm_tmul]
  | add m m' hm hm' =>
    simp [map_add, hm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hm']

lemma inr_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M'} :
    (inr R M M').toFun S m = ((TensorProduct.inrRight R R S M M') m) := by sorry

variable {R M}

/-- Given a polynomial law `f : M →ₚₗ[R] N` and a finite type `ι`, the `ι`-polarized of `f`
is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] N` obtained by composing `f` and `sum_proj R M ι`.
This is denoted by `Π_p` in Roby63 (where `p` corresponds to the size of `ι`). -/
def polarizedProd : (M →ₚₗ[R] N) →ₗ[R] (M × M →ₚₗ[R] N) where
  toFun f := f.comp (sum_fst_snd R M)
  map_add' f g := by
    ext S _ _ sm
    simp [comp_toFun']
  map_smul' r f := by
    ext S _ _ sm
    simp [comp_toFun']

lemma polarizedProd_apply (m : M × M) : f.polarizedProd m = f (m.fst + m.snd):= by
  simp only [polarizedProd, sum_fst_snd, fst, snd, LinearMap.coe_mk, AddHom.coe_mk, ground_apply,
    comp_toFun', add_def, Function.comp_apply, Pi.add_apply, map_tmul, LinearMap.id_coe, id_eq,
    LinearMap.fst_apply, LinearMap.snd_apply, EmbeddingLike.apply_eq_iff_eq]
  congr 1
  rw [TensorProduct.tmul_add]

-- Not needed?
lemma map_add_eq_polarizedprod_two_apply (m m' : M) :
    f (m + m') = (f.polarizedProd) (m, m') := by
  simp only [polarizedProd_apply]

lemma polarizedProd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M)} : (polarizedProd f).toFun' S m =
      f.toFun' S (((TensorProduct.prodRight R R S M M) m).fst +
        ((TensorProduct.prodRight R R S M  M) m).snd) := by
  simp [polarizedProd, comp_toFun', sum_fst_snd_toFun'_apply]

variable {f p}

--TODO: move
variable (R M) in
lemma _root_.TensorProduct.prodRight_smul {S : Type*} [CommSemiring S]
    [Algebra R S] (s : S) (m : TensorProduct R S (M × M'))  :
    ((TensorProduct.prodRight R R S M M') (s • m)) =
      (s • (TensorProduct.prodRight R R S M M') m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s' m => simp only [TensorProduct.prodRight_tmul]; rfl
  | add m m' hm hm' => simp only [smul_add, map_add, hm, hm']

lemma isHomogeneousOfDegree_polarizedProd (hf : IsHomogeneousOfDegree p f) :
    IsHomogeneousOfDegree p (polarizedProd f) := fun S _ _ s m ↦ by
  simp [polarizedProd_toFun'_apply,
    ← hf S s ((((TensorProduct.prodRight R R S M M) m).fst +
      ((TensorProduct.prodRight R R S M  M) m).snd)), smul_add, TensorProduct.prodRight_smul]

-- Roby63, example in pg 234
lemma coeff_polarizedProd_eq_zero_of_ne {n : ℕ} (m : (Fin n) → M × M) (d : (Fin n) →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≠ p) (hf : IsHomogeneousOfDegree p f) :
    coeff m (polarizedProd f) d = 0 := by
  revert n
  rw [← isHomogeneousOfDegree_of_coeff_iff]
  exact isHomogeneousOfDegree_polarizedProd hf

end Polarized

variable {R M}

-- I am not sure whether it is useful to add this.
/-- The bihomogeneous component of bidegree `n : ℕ × ℕ` of `f.polarized n`.
  This is denoted by `Π^{n_1, ..., n_p}f` in Roby63. -/
abbrev polarizedProd_biComponent (n : ℕ × ℕ) (f : PolynomialLaw R M N) :
    PolynomialLaw R (M × M) N := PolynomialLaw.biComponent n f.polarizedProd

theorem locFinsupp_polarizedProd_biComponent (f : PolynomialLaw R M N) :
    LocFinsupp (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f) := fun S _ _ m ↦ by
  have hss : (fun p ↦ (p, n)) ''
      (Function.support fun i ↦ (biComponent (i, n) (polarizedProd f)).toFun' S m) ⊆
        (Function.support fun d ↦ (biComponent d (polarizedProd f)).toFun' S m) := fun _ hd ↦ by
    obtain ⟨x, hx, rfl⟩ := hd
    simpa [biComponent_apply_toFun', finTwoArrowEquiv', Fin.isValue,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]

  exact ((LocFinsupp_biComponent f.polarizedProd _ _ ).subset hss).of_finite_image
    (fun _ _ _ _ h ↦ by simpa using h)

/- def differential : (M × M) →ₚₗ[R] N :=
  PolynomialLaw.lfsum (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f)
 -/
-- TODO: rename, avoid (?)
lemma hf (r : R) : LocFinsupp fun p ↦ (r • polarizedProd f).biComponent (p, n) := by
  have hf' : LocFinsupp (r • (fun p ↦ (polarizedProd f).biComponent (p, n))) := by
    exact locFinsupp_smul r (locFinsupp_polarizedProd_biComponent n f)
  convert hf'
  simp

-- TODO: golf
def differential : (M →ₚₗ[R] N) →ₗ[R] ((M × M) →ₚₗ[R] N) where
  toFun f := PolynomialLaw.lfsum (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f)
  map_add' f g := by
    ext S _ _ sm
    simp only [add_def, Pi.add_apply]
    simp only [polarizedProd_biComponent, map_add]
    simp only [← toFun_eq_toFun']
    have hfg : LocFinsupp fun p ↦ (polarizedProd f).biComponent (p, n) +
        (polarizedProd g).biComponent (p, n) :=
      locFinsupp_add (locFinsupp_polarizedProd_biComponent n f)
        (locFinsupp_polarizedProd_biComponent n g)
    rw [← lfsumHom_apply hfg, ← lfsumHom_apply (locFinsupp_polarizedProd_biComponent n f),
      ← lfsumHom_apply (locFinsupp_polarizedProd_biComponent n g), ← add_toFun_apply]
    simp only [polarizedProd_biComponent]
    rw [← map_add]
    rfl -- TODO: expand API
  map_smul' r f := by
    ext S _ _ sm
    simp only [RingHom.id_apply, smul_def, Pi.smul_apply]
    simp only [polarizedProd_biComponent]
    simp only [← toFun_eq_toFun']
    set t : LocFinsupp fun p ↦ (polarizedProd (r • f)).biComponent (p, n) := by
      exact hf f n r
    set t' := (locFinsupp_polarizedProd_biComponent n f)
    rw [← lfsumHom_apply t, ← lfsumHom_apply t']
    simp only [toFun_eq_toFun', polarizedProd_biComponent]
    rw [← PolynomialLaw.smul_def_apply]
    congr -- TODO: expand API
    rw [← map_smul]
    have : r • (⟨fun p ↦ (polarizedProd f).biComponent (p, n), t'⟩ :
      (Submodule.locFinsupp R (M × M) N ℕ)) =
        ⟨r • fun p ↦ (polarizedProd f).biComponent (p, n),
        Submodule.smul_mem (Submodule.locFinsupp R (M × M) N ℕ) r t'⟩ := rfl
    rw [this]
    simp only [map_smul]
    rfl

-- TODO: rename, golf
lemma asdf (a n : ℕ) (m m' : M) :
    biCoeff_S ((1 : R) ⊗ₜ[R] (m, m')) (a, n) f.polarizedProd =
      1 ⊗ₜ[R] ((coeff ![m, m']) f) ((finTwoArrowEquiv' ℕ).symm (a, n)) := by
  rw [biCoeff_S_apply_tmul]
  have h0 : (0 : R ⊗[R] M) = 1 ⊗ₜ 0 := sorry
  simp only [Fin.isValue, compFstRight, inlRight, fstRight, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearMap.coe_inl, LinearMap.coe_fst, Function.comp_apply, prodRight_tmul, tmul_zero,
    compSndRight, inrRight, sndRight, LinearMap.coe_inr, LinearMap.coe_snd, map_add,
    Nat.succ_eq_add_one, Nat.reduceAdd]
  simp_rw [h0, prodRight_symm_tmul]
  simp only [Fin.isValue, assoc_symm_tmul, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply]
  simp only [MvPolynomial.scalarRTensorAlgEquiv, Fin.isValue, AlgEquiv.trans_apply,
    MvPolynomial.rTensorAlgEquiv_apply, MvPolynomial.rTensorAlgHom, Algebra.TensorProduct.lift_tmul,
    MvPolynomial.mapAlgHom_apply, MvPolynomial.eval₂_X, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq, Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, MvPolynomial.mapAlgEquiv_apply, map_mul,
    MvPolynomial.map_X, MvPolynomial.map_C, RingHom.coe_coe, Algebra.TensorProduct.lid_tmul,
    smul_eq_mul, mul_one, MvPolynomial.C_1, MvPolynomial.rTensor_apply]
  rw [toFun_eq_toFun', polarizedProd_toFun'_apply]
  simp only [Fin.isValue, map_add, prodRight_tmul, tmul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [← toFun_eq_toFun']
  rw [toFun_add_tmul_eq_coeff_sum]
  simp only [finTwoArrowEquiv_symm_apply, Fin.isValue]
  rw [Finsupp.sum]
  simp only [Fin.isValue, map_sum, LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars,
    MvPolynomial.lcoeff_apply]
  have h2' (e : Fin 2 →₀ ℕ) : X (R := R) (0 : Fin 2) ^ e 0 * X 1 ^ e 1 =
      ∏ (i : Fin 2), X i ^ e i := by
    simp only [Fin.isValue, Fin.prod_univ_two]
  simp_rw [h2']
  simp_rw [prod_X_pow_eq_monomial', coeff_monomial]
  simp only [ite_tmul, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  intro h0
  rw [h0, tmul_zero]

-- TODO: rename, golf, extract lemmas
lemma differential_eq_coeff (n : ℕ) (m m' : M) :
    f.differential n (m, m') =
      Polynomial.scalarRTensor R N (f.toFun' (Polynomial R)
          ((1 : Polynomial R) ⊗ₜ[R] m + Polynomial.X (R := R) ⊗ₜ[R] m')) n := by
  have hf : LocFinsupp fun p ↦ f.polarizedProd.biComponent (p, n) :=
    locFinsupp_polarizedProd_biComponent n f
  simp only [differential, LinearMap.coe_mk, AddHom.coe_mk, ground_apply]
  simp only [Polynomial.scalarRTensor_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_eq_of_locFinsupp hf]
  simp only [Finsupp.sum]
  conv_rhs => {
    simp only [← toFun_eq_toFun']
    rw [toFun_add_tmul_eq_coeff_sum]
    rw [map_finsuppSum]
    simp only [Finsupp.sum, finTwoArrowEquiv_symm_apply, Fin.isValue, one_pow, one_mul,
    LinearMap.rTensor_tmul, Polynomial.lcoeff_apply, Polynomial.coeff_X_pow]
    simp only [Fin.isValue, ite_tmul] }
  rw [Finset.sum_ite]
  simp only [Fin.isValue, Finset.sum_const_zero, add_zero]
  set V := (Finsupp.ofSupportFinite (fun i ↦ (f.polarizedProd.biComponent
    (i, n)).toFun' R (1 ⊗ₜ[R] (m, m'))) (hf _ _)).support with hV
  have : ∑ x ∈ ((coeff ![m, m']) f).support with n = x 1, (1 : R) ⊗ₜ[R] ((coeff ![m, m']) f) x =
      ∑ a ∈ V, 1 ⊗ₜ[R] ((coeff ![m, m']) f) ((finTwoArrowEquiv' ℕ).symm (a, n)) := by
    refine (Finset.sum_bij (fun x _ ↦ x 0) (fun a ↦ ?_) ?_ ?_ ?_)
    · intro ha
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq] at ha
      simp only [hV, biComponent_apply_toFun', Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq]
      rw [asdf, ha.2]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, finTwoArrowEquiv', Fin.isValue,
        Equiv.coe_fn_symm_mk]
      intro ha'
      have h0 : (0 : R ⊗[R] N) = 1 ⊗ₜ 0 := sorry
      rw [h0] at ha'
      rw [← (TensorProduct.lid R N).injective.eq_iff] at ha'
      simp only [Fin.isValue, lid_tmul, _root_.one_smul, tmul_zero, map_zero] at ha'
      apply ha.1
      convert ha'
      -- TODO: lemma
      refine Finsupp.ext ?_
      simp [Fin.forall_fin_two, Finsupp.ofSupportFinite_coe]
    · intro a ha b hb h
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue] at h
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq] at ha hb
      refine Finsupp.ext ?_
      simp [Fin.forall_fin_two, h, ← ha.2, ← hb.2]
    · intro a ha
      simp only [hV, biComponent_apply_toFun', Finsupp.mem_support_iff, ne_eq,
        Finsupp.ofSupportFinite_coe] at ha
      use (finTwoArrowEquiv' ℕ).symm (a, n)
      constructor
      · simp [finTwoArrowEquiv', Finsupp.ofSupportFinite_coe]
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, finTwoArrowEquiv',
          Equiv.coe_fn_symm_mk, Finset.mem_filter, Finsupp.mem_support_iff, ne_eq,
          Finsupp.ofSupportFinite_coe, Matrix.cons_val_one, Matrix.cons_val_fin_one, and_true]
        by_contra ha'
        apply ha
        simp [asdf, finTwoArrowEquiv', ha']
    · intro x hx
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.mem_filter,
        Finsupp.mem_support_iff, ne_eq] at hx
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, finTwoArrowEquiv', Fin.isValue,
        Equiv.coe_fn_symm_mk]
      rw [hx.2]
      congr
      refine Finsupp.ext ?_
      simp [Fin.forall_fin_two, Finsupp.ofSupportFinite_coe]
  rw [this]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finsupp.ofSupportFinite_coe]
  rw [biComponent.toFun'_apply]
  rw [asdf]

lemma differential_map_add_snd'' (m m₁ m₂ : M) :
    f.differential 1 (m, m₁ + m₂) = f.differential 1 (m, m₁) + f.differential 1 (m, m₂) := by
  simp only [differential, LinearMap.coe_mk, AddHom.coe_mk]
  rw [lfsum_ground_eq_of_locFinsupp, lfsum_ground_eq_of_locFinsupp, lfsum_ground_eq_of_locFinsupp]
  simp only [Finsupp.sum, Finsupp.ofSupportFinite_coe]
  sorry
  sorry
  sorry
  sorry

-- Roby63, pg 239
lemma differential_map_add_snd' (m m₁ m₂ : M) :
    f.differential 1 (m, m₁ + m₂) = f.differential 1 (m, m₁) + f.differential 1 (m, m₂) := by
  classical
  simp only [differential_eq_coeff]
  simp only [← toFun_eq_toFun', toFun_add_tmul_eq_coeff_sum, finTwoArrowEquiv_symm_apply,
    Fin.isValue, one_pow, one_mul, Polynomial.scalarRTensor_apply, ← map_add,
    EmbeddingLike.apply_eq_iff_eq]
  simp only [Finsupp.sum, Fin.isValue, map_sum, LinearMap.rTensor_tmul, Polynomial.lcoeff_apply,
    Polynomial.coeff_X_pow, map_add]
  simp only [Fin.isValue, ite_tmul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have (x : Fin 2 →₀ ℕ) (hx : x 1 = 1) : x ∈ ((coeff ![m, m₁ + m₂]) f).support := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finsupp.mem_support_iff, ne_eq]
    simp only [coeff_eq, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, EmbeddingLike.map_eq_zero_iff, ne_eq]
    sorry
  sorry

-- Roby63, pg 239 (?)
lemma differential_map_add_snd {S : Type*} [CommSemiring S] [Algebra R S] (m m₁ m₂ : S ⊗[R] M) :
    (f.differential 1).toFun S ((inl R M M ).toFun S m + (inr R M M ).toFun S (m₁ + m₂)) =
      (f.differential 1).toFun S ((inl R M M ).toFun S m + (inr R M M ).toFun S m₁) +
      (f.differential 1).toFun S ((inl R M M ).toFun S m + (inr R M M ).toFun S m₂) := by
  classical
  sorry

-- Roby63, pg 239
lemma differential_map_smul_snd' (r : R) (m m' : M) :
    f.differential 1 (m, r • m') = r • f.differential 1 (m, m') := by
  classical
  sorry

-- Roby63, pg 239 (?)
lemma differential_map_smul_snd {S : Type*} [CommSemiring S] [Algebra R S] (s : S)
    (m m' : S ⊗[R] M) :
    (f.differential 1).toFun S ((inl R M M ).toFun S m + (inr R M M ).toFun S (s • m')) =
      s • (f.differential 1).toFun S
        ((inl R M M ).toFun S m + (inr R M M ).toFun S m') := by
  classical
  sorry

  variable {f n p}

-- Roby63, pg 239
lemma differential_eq_biComponent_of_le (hf : IsHomogeneousOfDegree p f) (hnp : n ≤ p) :
    (f.differential n) = (polarizedProd f).biComponent (p - n, n) := by
  classical
  sorry

-- **MI** : TODO: add id_toFun_apply, fst_toFun_apply, snd_toFun_apply, add_toFun'

lemma polarizedProd_id_eq : id.polarizedProd = fst R M M + snd R M M := by
  ext S _ _ sm
  simp only [polarizedProd_toFun'_apply, id_apply']
  simp only [id_eq, ← toFun_eq_toFun', add_toFun, Pi.add_apply]
  simp only [toFun_eq_toFun', fst_toFun'_apply, snd_toFun'_apply]

lemma fst_biComponent_eq_zero (p : ℕ) : (fst R M M).biComponent (p, 1) = 0 := by
  ext S _ _ sm
  simp only [biComponent, zero_def, Pi.zero_apply]
  simp only [biCoeff_S_apply, Fin.isValue, map_add, rTensor_apply]
  simp only [Fin.isValue, toFun_eq_toFun', LinearMap.coe_mk, AddHom.coe_mk, fst_toFun'_apply,
    map_add, Prod.fst_add]
  convert add_zero _
  · induction sm using TensorProduct.induction_on with
    | zero => simp only [Fin.isValue, map_zero, tmul_zero, Prod.fst_zero]
    | tmul s m =>
      simp only [Fin.isValue, compSndRight_tmul, inrRight_tmul, assoc_symm_tmul,
        LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, prodRight_tmul, tmul_zero, map_zero]
    | add sm sm' hsm hsm' =>
      simp only [Fin.isValue, map_add, tmul_add, Prod.fst_add, hsm, hsm', add_zero]
  · induction sm using TensorProduct.induction_on with
    | zero => simp only [Fin.isValue, map_zero, tmul_zero, Prod.fst_zero]
    | tmul s m =>
      have h0 : MvPolynomial.coeff ((finTwoArrowEquiv' ℕ).symm (p, 1))
          (scalarRTensorAlgEquiv (X 0 ⊗ₜ[R] s)) = 0 := by
        simp only [scalarRTensorAlgEquiv, Fin.isValue, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
          mapAlgEquiv_apply, coeff_map, coeff_rTensorAlgHom_tmul, coeff_X', RingHom.coe_coe,
          Algebra.TensorProduct.lid_tmul, ite_smul, _root_.one_smul, _root_.zero_smul]
        rw [if_neg]
        rw [Finsupp.ext_iff]
        simp only [Fin.isValue, finTwoArrowEquiv', Equiv.coe_fn_symm_mk,
          Finsupp.ofSupportFinite_coe, Fin.forall_fin_two, Finsupp.single_eq_same,
          Matrix.cons_val_zero, ne_eq, zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, and_false]
      simp only [Fin.isValue, compFstRight_tmul, inlRight_tmul, assoc_symm_tmul,
        LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, prodRight_tmul, tmul_zero,
        LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars, lcoeff_apply, h0, zero_tmul]
    | add sm sm' hsm hsm' =>
      simp only [← hsm, ← hsm', Fin.isValue, map_add, tmul_add, Prod.fst_add, zero_add]

-- TODO: golf
lemma biCoeff_S_snd_eq_zero_of_ne {S : Type*} [CommSemiring S] [Algebra R S]
    (sm : S ⊗[R] (M × M)) {n : ℕ × ℕ} (hn : n.2 ≠ 1) : (biCoeff_S sm n) (snd R M M) = 0 := by
  induction sm using TensorProduct.induction_on with
  | zero =>
    simp only [biCoeff_S_apply, Fin.isValue, map_zero, tmul_zero, add_zero, rTensor_apply]
    simp only [snd_toFun_apply, map_zero, Prod.snd_zero]
  | tmul s m =>
    simp only [biCoeff_S_apply_tmul, Fin.isValue, map_add, rTensor_apply]
    simp only [Fin.isValue, snd_toFun_apply, map_add, Prod.snd_add]
    simp only [scalarRTensorAlgEquiv, AlgEquiv.toLinearEquiv_trans, Fin.isValue, compFstRight_tmul,
      inlRight_tmul, assoc_symm_tmul, LinearEquiv.rTensor_tmul, LinearEquiv.trans_apply,
      AlgEquiv.toLinearEquiv_apply, rTensorAlgEquiv_apply, mapAlgEquiv_apply, prodRight_tmul,
      tmul_zero, map_zero, compSndRight_tmul, inrRight_tmul, LinearMap.rTensor_tmul,
      LinearMap.coe_restrictScalars, lcoeff_apply, coeff_map, coeff_rTensorAlgHom_tmul, coeff_X',
      RingHom.coe_coe, Algebra.TensorProduct.lid_tmul, ite_smul, _root_.one_smul, _root_.zero_smul,
      zero_add]
    rw [if_neg, zero_tmul]
    rw [Finsupp.ext_iff]
    simp only [Fin.isValue, finTwoArrowEquiv', Equiv.coe_fn_symm_mk, Finsupp.ofSupportFinite_coe,
      Fin.forall_fin_two, ne_eq, one_ne_zero, not_false_eq_true, Finsupp.single_eq_of_ne,
      Matrix.cons_val_zero, Finsupp.single_eq_same, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      (Ne.symm hn), and_false]
  | add sm sm' hsm hsm' =>
    simp only [biCoeff_S_apply, Fin.isValue, map_add, rTensor_apply] at hsm hsm' ⊢
    simp only [Fin.isValue, tmul_add, map_add]
    simp only [Fin.isValue, snd_toFun_apply, map_add, Prod.snd_add] at hsm hsm' ⊢
    rw [add_add_add_comm, hsm, hsm', zero_add]

-- TODO: golf
-- Roby63, pg 239
lemma differential_id_eq : id.differential 1 = snd R M M := by
  ext S _ _ sm
  simp only [differential, polarizedProd_biComponent, LinearMap.coe_mk, AddHom.coe_mk,
    polarizedProd_id_eq, biComponent_add, fst_biComponent_eq_zero, zero_add]
  rw [← recompose_biComponent (snd R M M)]
  rw [lfsum_eq_of_locFinsupp (LocFinsupp_biComponent (snd R M M)), lfsum_eq_of_locFinsupp]
  simp only [Finsupp.sum, biComponent_apply_toFun']
  simp only [Finsupp.ofSupportFinite_coe]
  apply Finset.sum_of_injOn (fun p ↦ (p, 1))
  · simp only [Prod.mk.injEq, and_true, implies_true, Set.injOn_of_eq_iff_eq]
  · simp only [Set.MapsTo, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
    intro p hp
    simpa [recompose_biComponent, Finsupp.ofSupportFinite_coe] using hp
  · intro n hn hn'
    simp only [Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe, ne_eq, Set.mem_image,
      Finset.mem_coe, not_exists, not_and] at hn hn'
    simp_rw [recompose_biComponent] at hn'
    by_cases hn1 : n.2 = 1
    · rw [← hn1] at hn'
      exact absurd rfl (hn' n.1 hn)
    · exact biCoeff_S_snd_eq_zero_of_ne sm hn1
  · intro p hp
    rw [recompose_biComponent]
  · intro T _ _ tm
    set U := (Function.support fun i ↦ ((fun n ↦ (snd R M M).biComponent n) i).toFun' T tm)
      with hU_def
    suffices hU : Finite U by
      apply Set.Finite.of_injOn (f := fun p ↦ (p, 1)) ?_ ?_ hU
      · simp only [Set.MapsTo, biComponent_apply_toFun', Function.mem_support, ne_eq]
        intro p hp
        simpa [hU_def, biComponent_apply_toFun', Function.mem_support, ne_eq,
          recompose_biComponent] using hp
      apply Function.Injective.injOn
      exact Prod.mk_left_injective 1
    apply LocFinsupp_biComponent (snd R M M) _

open TensorProduct

lemma locFinsupp_differential (f : M →ₚₗ[R] N) : LocFinsupp fun n ↦ f.differential n := by
  simp only [LocFinsupp]
  intro S _ _ sm
  simp only [differential, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [lfsum_eq_of_locFinsupp (locFinsupp_polarizedProd_biComponent _ f)]
  have : (Function.support fun i ↦ (Finsupp.ofSupportFinite (fun i_1 ↦
    (polarizedProd_biComponent (i, i_1) f).toFun' S sm) (by sorry)).sum fun x m ↦
      m) = ?_ := by
    let g := (polarizedProd f)
    --let e := el_S''' (N := N) sm g
    -- Ideal: take the RHS to be the Set.range of the total degree of `e`, and show
    -- that LHS ⊆ RHS
    ext x
    simp only [biComponent_apply_toFun', Function.mem_support, ne_eq]
    sorry
  sorry
  sorry

def setprod (x : Unit →₀ ℕ) : Finset (Fin 2 →₀ ℕ) := by
  apply Set.Finite.toFinset (s := {y : Fin 2 →₀ ℕ | y 0 + y 1 = x 0})
  sorry

--open Classical in
theorem bar [DecidableEq N] (f : M →ₚₗ[R] N) (m m' : M) (x : Unit →₀ ℕ) :
  ((coeff fun (x : Unit) ↦ m + m') f) x =
    ∑ y ∈ setprod x, ((coeff ![m, m']) f) y  := sorry

theorem bar' [DecidableEq N] (f : M →ₚₗ[R] N) (m m' : M) :
  ∑ x ∈ ((coeff fun x ↦ m + m') f).support, ((coeff fun (x : Unit) ↦ m + m') f) x =
    ∑ y ∈ ((coeff ![m, m']) f).support with
      ¬∑ x ∈ ((coeff ![m, m']) f).support with y 1 = x 1, ((coeff ![m, m']) f) x = 0,
      ((coeff ![m, m']) f) y  := by
  -- **MI**: I am not sure about this
  have : ∑ x ∈ ((coeff fun x ↦ m + m') f).support, ∑ y ∈ setprod x, ((coeff ![m, m']) f) y =
      ∑ y ∈ ((coeff ![m, m']) f).support, ((coeff ![m, m']) f) y := by
    have (x : Unit →₀ ℕ) (y : Fin 2 →₀ ℕ) (hy : y ∈ setprod x) :
        x ∈ ((coeff fun x ↦ m + m') f).support ↔ y ∈ ((coeff ![m, m']) f).support := by
      simp only [Finsupp.mem_support_iff, ne_eq, Nat.succ_eq_add_one, Nat.reduceAdd]
      simp only [coeff_eq, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
        EmbeddingLike.map_eq_zero_iff, ne_eq, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      set g : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial Unit R :=
        MvPolynomial.aeval ![X 0, X 0] with hg_def
      have hg := f.isCompat_apply g
      have : (f.toFun (MvPolynomial Unit R) (X PUnit.unit ⊗ₜ[R] (m + m'))) =
        f.toFun (MvPolynomial Unit R) ((LinearMap.rTensor M g.toLinearMap)
          (X 0 ⊗ₜ[R] m + X 1 ⊗ₜ[R] m')) := by simp [hg_def, tmul_add]
      simp_rw [this, ← hg]
      rw [not_iff_not]
      simp only [setprod, Fin.isValue, PUnit.zero_eq, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq] at hy
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · sorry
      · sorry
    sorry
  simp_rw [bar, this]
  congr
  ext z
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finsupp.mem_support_iff, ne_eq, Fin.isValue,
    Finset.mem_filter, iff_self_and]
  intro hz
  sorry

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') = lfsum (fun n ↦ f.differential n) (m, m') := by
  classical
  rw [lfsum_ground_eq_of_locFinsupp (locFinsupp_differential f)]
  rw [Finsupp.sum]
  simp only [Finsupp.ofSupportFinite_coe, differential_eq_coeff]
  simp only [ground_apply]
  simp only [← toFun_eq_toFun']
  simp only [toFun_tmul_eq_coeff_sum, PUnit.zero_eq, one_pow]
  simp only [toFun_add_tmul_eq_coeff_sum, finTwoArrowEquiv_symm_apply, Fin.isValue, one_pow,
    one_mul]
  simp only [map_finsuppSum, lid_tmul, _root_.one_smul, Fin.isValue, Finsupp.sum_apply]
  simp only [Finsupp.sum, Fin.isValue]
  rw [Finset.sum_comm]
  simp only [Fin.isValue, Polynomial.scalarRTensor_apply, LinearMap.rTensor_tmul,
    Polynomial.lcoeff_apply, Polynomial.coeff_X_pow, lid_tmul, ite_smul, _root_.one_smul,
    _root_.zero_smul, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq]
  simp only [Fin.isValue, Finset.sum_ite, Finset.sum_const_zero, add_zero, ite_not, zero_add]
  simp only [Fin.isValue, Finsupp.ofSupportFinite_coe]
  exact bar' f m m'

-- TODO: move
variable (R M N) in
/-- The constant polynomial law.-/
def const (n : N) : M →ₚₗ[R] N where
  toFun' S _ _ sm := 1 ⊗ₜ n
  isCompat' φ := by ext; simp

lemma const_toFun {S : Type*} [CommSemiring S] [Algebra R S] (m : M) (sm : S ⊗[R] M) :
    (const R M M m).toFun S sm = (1 : S) ⊗ₜ[R] m := sorry

-- Section II.5

/-- The nth partial derivative of `f` at `x`. -/
def partialDerivative (n : ℕ) (x : M) : (M →ₚₗ[R] N) →ₗ[R] (M →ₚₗ[R] N) where
  toFun f := (f.differential n).comp (inl R M M + (inr R M M).comp (const R M M x))
  map_add' f g := by
    ext S _ _ sm
    simp [map_add, comp_toFun', add_def, Function.comp_apply, Pi.add_apply]
  map_smul' r f := by
    ext S _ _ sm
    simp [map_smul, comp_toFun', smul_def, add_def, Function.comp_apply, Pi.add_apply,
      Pi.smul_apply, RingHom.id_apply]

-- TODO: correct RHS
lemma differential_toFun_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S] (n : ℕ)
    (m m' : S ⊗[R] M) :
    (f.differential n).toFun S ((inl R M M).toFun S m + (inr R M M).toFun S m') =
    Polynomial.rTensor _ _ _ (f.toFun _ ((LinearEquiv.rTensor M
      (Polynomial.scalarRTensorAlgEquiv _ _).toLinearEquiv)
        (((TensorProduct.assoc R (Polynomial R) S M).symm ((1 : Polynomial R) ⊗ₜ m)) +
          ((TensorProduct.assoc R (Polynomial R) S M).symm
            ((Polynomial.X : Polynomial R) ⊗ₜ m'))))) n := by
  sorry

-- TODO: golf
-- pg 239
lemma partialDerivative_eq_coeff {S : Type*} [CommSemiring S] [Algebra R S] (x : M)
    (sm : S ⊗[R] M) : (partialDerivative n x f).toFun S sm =
    Polynomial.rTensor _ _ _ (f.toFun _ ((LinearEquiv.rTensor M
      (Polynomial.scalarRTensorAlgEquiv _ _).toLinearEquiv)
        (((TensorProduct.assoc R (Polynomial R) S M).symm ((1 : Polynomial R) ⊗ₜ sm))) +
          (Polynomial.X ⊗ₜ[R] x))) n := by
  have : (Polynomial.scalarRTensorAlgEquiv R S) (Polynomial.X ⊗ₜ[R] 1) ⊗ₜ[R] x =
      (Polynomial.X) ⊗ₜ[R] x  := by
    simp only [Polynomial.scalarRTensorAlgEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv]
    simp only [Polynomial.rTensorAlgEquiv, AlgEquiv.ofLinearEquiv_apply]
    congr
    ext d
    rw [Polynomial.coeff_map]
    rw [Polynomial.rTensorLinearEquiv_coeff_tmul]
    simp only [RingHom.coe_coe, Algebra.TensorProduct.lid_tmul]
    simp [Polynomial.coeff_X, ite_smul, _root_.one_smul, _root_.zero_smul]
  simp only [partialDerivative, LinearMap.coe_mk, AddHom.coe_mk, comp_toFun, Function.comp_apply]
  simp only [add_toFun, comp_toFun, Pi.add_apply, Function.comp_apply, const_toFun]
  rw [differential_toFun_eq_coeff]
  simp only [assoc_symm_tmul, map_add, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, this]

-- Roby63, pg 240
-- **MI**: something is off here.
lemma differential_isHomogeneousOfDegree_of_le [Nontrivial R]
    (hf : IsHomogeneousOfDegree p f) (hnp : n ≤ p) (x : M) :
    (partialDerivative n x f).IsHomogeneousOfDegree (p - n) := by
  simp only [partialDerivative, LinearMap.coe_mk, AddHom.coe_mk]
  rw [differential_eq_biComponent_of_le hf hnp]

  have hf' := biComponentIsMultiHomogeneous f.polarizedProd (p - n, n)
  have hf'' := hf'.isHomogeneousOfDegree
  simp only [hnp, Nat.sub_add_cancel] at hf''
  --have := IsHomogeneousOfDegree.comp hf'.isHomogeneousOfDegree
  · sorry

  --have := IsBiHomogeneousOfDegree.isHomogeneousOfDegree hf'
  --sorry

lemma differential_eq_zero_of_gt (hf : IsHomogeneousOfDegree p f) (hnp : p < n) (x : M) :
    partialDerivative n x f = 0 := by
  sorry


-- Section II.9

lemma partialDerivative_prod_eq (f : (M × M') →ₚₗ[R] N) (x : M × M') :
    f.partialDerivative 1 x =
      f.partialDerivative 1 (x.1, 0) + f.partialDerivative 1 (0, x.2) := by
  ext S _ _ sm
  simp only [partialDerivative, LinearMap.coe_mk, AddHom.coe_mk, add_def, Pi.add_apply]
  simp only [comp_toFun', add_def, Function.comp_apply, Pi.add_apply]
  simp only [const]
  simp only [← toFun_eq_toFun']
  have hx : (1 : S) ⊗ₜ[R] x = 1 ⊗ₜ[R] (x.1, 0) + 1 ⊗ₜ[R] (0, x.2) := by
    simp [← tmul_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
  rw [hx, differential_map_add_snd]


end PolynomialLaw
