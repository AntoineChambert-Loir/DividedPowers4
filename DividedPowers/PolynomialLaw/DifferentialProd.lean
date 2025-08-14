import DividedPowers.PolynomialLaw.BiHomogeneous
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

open MvPolynomial TensorProduct

universe u

variable (R : Type u) [CommSemiring R] (M M' : Type*) [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {N : Type*} [AddCommGroup N] [Module R N]

variable (f : M →ₚₗ[R] N) (n p : ℕ)
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

variable {R M}

/-- Given a polynomial law `f : M →ₚₗ[R] N` and a finite type `ι`, the `ι`-polarized of `f`
is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] N` obtained by composing `f` and `sum_proj R M ι`.
This is denoted by `Π_p` in Roby63 (where `p` corresponds to the size of `ι`). -/
def polarizedProd : M × M →ₚₗ[R] N := f.comp (sum_fst_snd R M)

lemma polarizedProd_apply (m : M × M) : f.polarizedProd m = f (m.fst + m.snd):= by
  simp only [polarizedProd, sum_fst_snd, fst, snd, ground_apply, comp_toFun', add_def,
    Function.comp_apply, Pi.add_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearMap.fst_apply, LinearMap.snd_apply, EmbeddingLike.apply_eq_iff_eq]
  congr 1
  rw [TensorProduct.tmul_add]

-- Not needed?
lemma map_add_eq_polarized_two_apply (m m' : M) :
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
    PolynomialLaw R (M × M) N := PolynomialLaw.biComponent f.polarizedProd n

def differential : (M × M) →ₚₗ[R] N :=
  PolynomialLaw.lfsum (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f)

-- TODO: golf
theorem locFinsupp_polarizedProd_biComponent (f : PolynomialLaw R M N) :
    LocFinsupp (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f) := fun S _ _ m ↦ by
  sorry
  /- set g : ℕ → (ULift.{u, 0} (Fin 2) →₀ ℕ) := fun p ↦ (map_pair n p)
  set s := (Function.support fun i ↦ (multiComponent (map_pair n i)
    (polarized (ULift.{u, 0} (Fin 2)) f)).toFun' S m)
  have hg : Set.InjOn g s := by
    intro a ha b hb h
    simp only [map_pair, Finsupp.ext_iff, ULift.forall, g] at h
    exact h 0
  have hss : g '' (Function.support fun i ↦ (multiComponent (map_pair n i)
      (polarized (ULift.{u, 0} (Fin 2)) f)).toFun' S m) ⊆
      (Function.support fun d ↦ (multiComponent (d : ULift.{u, 0} (Fin 2) →₀ ℕ)
        (polarized (ULift.{u, 0} (Fin 2)) f)).toFun' S m) := by
    intro d hd
    simp only [Set.mem_image] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    simpa only [multiComponent_toFun', Function.mem_support, ne_eq, g]
  apply Set.Finite.of_finite_image _ hg
  apply Set.Finite.subset _ hss
  exact LocFinsupp_multiComponent _ _ _ -/

-- TODO: rename, golf
lemma asdf (a n : ℕ) (m m' : M) :
    biCoeff_S ((1 : R) ⊗ₜ[R] (m, m')) f.polarizedProd (a, n) =
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
lemma foo (n : ℕ) (m m' : M) :
    f.differential n (m, m') =
      Polynomial.scalarRTensor R N
        (f.toFun' (Polynomial R)
          ((1 : Polynomial R) ⊗ₜ[R] m + Polynomial.X (R := R) ⊗ₜ[R] m')) n := by
  have hf : LocFinsupp fun p ↦ f.polarizedProd.biComponent (p, n) :=
    locFinsupp_polarizedProd_biComponent n f
  simp only [differential, ground_apply]
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
      simp only [hV, biComponent_toFun', Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
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
      simp only [hV, biComponent_toFun', Finsupp.mem_support_iff, ne_eq,
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

open TensorProduct

lemma locFinsupp_differential (f : M →ₚₗ[R] N) : LocFinsupp fun n ↦ f.differential n := by
  simp only [LocFinsupp]
  intro S _ _ sm
  simp only [differential]
  simp_rw [lfsum_eq_of_locFinsupp (locFinsupp_polarizedProd_biComponent _ f)]
  have : (Function.support fun i ↦ (Finsupp.ofSupportFinite (fun i_1 ↦
    (polarizedProd_biComponent (i, i_1) f).toFun' S sm) (by sorry)).sum fun x m ↦
      m) = ?_ := by
    let g := (polarizedProd f)
    --let e := el_S''' (N := N) sm g
    -- Ideal: take the RHS to be the Set.range of the total degree of `e`, and show
    -- that LHS ⊆ RHS
    ext x
    simp only [biComponent_toFun', Function.mem_support, ne_eq]
    sorry
  sorry
  sorry

--open Classical in
theorem bar [DecidableEq N] (f : M →ₚₗ[R] N) (m m' : M) :
  ∑ x ∈ ((coeff fun x ↦ m + m') f).support, ((coeff fun (x : Unit) ↦ m + m') f) x =
    ∑ y ∈ ((coeff ![m, m']) f).support with
      ¬∑ x ∈ ((coeff ![m, m']) f).support with y 1 = x 1, ((coeff ![m, m']) f) x = 0,
      ((coeff ![m, m']) f) y  := sorry

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') = lfsum (fun n ↦ f.differential n) (m, m') := by
  classical
  rw [lfsum_ground_eq_of_locFinsupp (locFinsupp_differential f)]
  rw [Finsupp.sum]
  simp only [Finsupp.ofSupportFinite_coe, foo]
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
  have h : (Finsupp.ofSupportFinite
          (fun i ↦ ∑ x ∈ ((coeff ![m, m']) f).support, if i = x 1 then
            ((coeff ![m, m']) f) x else 0) (by sorry)).support =
          (Finsupp.ofSupportFinite
          (fun i ↦ ∑ x ∈ ((coeff ![m, m']) f).support with i = x 1,
          ((coeff ![m, m']) f) x) (by sorry)).support := by
    congr
    ext n
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finset.sum_ite,
      Finset.sum_const_zero, add_zero]

  have h' (y : Fin 2 →₀ ℕ) : y 1 ∈ (Finsupp.ofSupportFinite
      (fun i ↦ ∑ x ∈ ((coeff ![m, m']) f).support with i = x 1, ((coeff ![m, m']) f) x)
        (by sorry)).support ↔
        ∑ x ∈ ((coeff ![m, m']) f).support with y 1 = x 1, ((coeff ![m, m']) f) x ≠ 0 := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finsupp.mem_support_iff,
      Finsupp.ofSupportFinite_coe, ne_eq]
  --classical
  /- have h'' : ∑ x ∈ ((coeff ![m, m']) f).support with x 1 ∈ (Finsupp.ofSupportFinite
      (fun i ↦ ∑ x ∈ ((coeff ![m, m']) f).support with i = x 1, ((coeff ![m, m']) f) x)
        (by sorry)).support, ((coeff ![m, m']) f) x =
      ∑ y ∈ ((coeff ![m, m']) f).support with
        (∑ x ∈ ((coeff ![m, m']) f).support with y 1 = x 1,
          ((coeff ![m, m']) f) x ≠ 0), ((coeff ![m, m']) f) y := by
    congr
    ext y
    rw [h' y] -/

  /- have h' : ∑ x ∈ ((coeff ![m, m']) f).support with x 1 ∈ (Finsupp.ofSupportFinite
      (fun i ↦ ∑ x ∈ ((coeff ![m, m']) f).support with i = x 1, ((coeff ![m, m']) f) x)
        (by sorry)).support, ((coeff ![m, m']) f) x =
      ∑ x ∈ ((coeff ![m, m']) f).support, ((coeff ![m, m']) f) x := by
    congr
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Finsupp.mem_support_iff, ne_eq]
    ext d
    simp only [Fin.isValue, Finsupp.mem_support_iff, ne_eq, Finset.mem_filter, and_iff_left_iff_imp]
    intro hd h
    simp only [Fin.isValue, Finsupp.ofSupportFinite_coe] at h
    apply hd

    sorry -/


  /- simp_rw [h, h']
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  simp only [Fin.isValue, ne_eq]

  exact bar f m m' -/
  simp only [Fin.isValue, Finsupp.ofSupportFinite_coe]
  exact bar f m m'

lemma map_add_eq_sum_differential_apply''' (m m' : M) :
    f (m + m') = lfsum (fun n ↦ f.differential n) (m, m') := by
  simp only [ground_apply]
  rw [← toFun_eq_toFun']
  rw [toFun_tmul_eq_coeff_sum]
  simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, one_pow]
  simp only [generize, LinearMap.coe_mk, AddHom.coe_mk]
  have : (TensorProduct.lid R N) ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial Unit R)
          ( MvPolynomial.X 0 ⊗ₜ[R] (m + m')))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) =
    (TensorProduct.lid R N) ((Polynomial.scalarRTensor _ _
        (f.toFun (Polynomial R)
          ( Polynomial.X ⊗ₜ[R] (m + m')))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) := sorry
  change (TensorProduct.lid R N) ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial Unit R)
          ( MvPolynomial.X 0 ⊗ₜ[R] (m + m')))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) = _
  rw [this]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_eq_of_locFinsupp]
  · rw [toFun_tmul_eq_coeff_sum]

    sorry
    /- simp only [foo, lid_symm_apply]
    rw [Finsupp.sum, Finsupp.sum]
    congr
    · sorry
    · ext a
      simp?
      sorry -/
  · exact locFinsupp_differential f


#exit

/- lemma map_add_eq_sum_differential_apply'''' (m m' : M) :
    f (m + m') =
      ∑ᶠ n, f.differential n ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [ground_apply]
  have : ((1 : R) ⊗ₜ[R] (m + m')) =
    ∑ i : ULift.{u} Unit, 1 ⊗ₜ[R] match i with | 0 => m + m' := rfl
  rw [this]
  rw [← toFun_eq_toFun']
  rw [toFun_sum_tmul_eq_coeff_sum]
  simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, one_pow,
    Finset.prod_const_one]
  simp only [generize, LinearMap.coe_mk, AddHom.coe_mk]
  have : (TensorProduct.lid R N) ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial (ULift.{u} Unit) R)
          ( MvPolynomial.X 0 ⊗ₜ[R] (m + m')))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) =
    (TensorProduct.lid R N) ((Polynomial.scalarRTensor _ _
        (f.toFun (Polynomial R)
          ( Polynomial.X ⊗ₜ[R] (m + m')))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) := sorry
  change (TensorProduct.lid R N) ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial (ULift.{u} Unit) R)
          ( MvPolynomial.X 0 ⊗ₜ[R] (m + m')))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) = _
  rw [this]
  simp only [foo', TensorProduct.lid_symm_apply]
  rw [Finsupp.sum]
  simp only [map_sum, lid_tmul, _root_.one_smul]
  rw [finsum_eq_finset_sum_of_support_subset]
  split_ifs with h
  · rw [toFun_eq_toFun']
    congr
    sorry
  · sorry -/

lemma map_add_eq_sum_differential_apply' (m m' : M) :
    f (m + m') =
      ∑ᶠ n, f.differential n ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [ground_apply]
  have : ((1 : R) ⊗ₜ[R] m + (1 : R) ⊗ₜ[R] m') =
    ∑ i : (ULift.{u} (Fin 2)), 1 ⊗ₜ[R] match i with | 0 => m | 1 => m' := rfl
  simp_rw [TensorProduct.tmul_add, this,]
  rw [← toFun_eq_toFun']
  rw [toFun_sum_tmul_eq_coeff_sum]
  simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, one_pow,
    Finset.prod_const_one]
  simp only [generize, LinearMap.coe_mk, AddHom.coe_mk]
  change (TensorProduct.lid R N) ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial (ULift.{u, 0} (Fin 2)) R)
          ( MvPolynomial.X 0 ⊗ₜ[R] m + MvPolynomial.X 1 ⊗ₜ[R] m'))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) = _
  simp only [foo', TensorProduct.lid_symm_apply]
  rw [Finsupp.sum]
  simp only [map_sum, lid_tmul, _root_.one_smul]
  simp only [finsum]
  split_ifs with h
  · congr!
    sorry
  · sorry

  lemma map_add_eq_sum_differential_apply'' (m m' : M) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [ground_apply, EmbeddingLike.apply_eq_iff_eq]
  have : ((1 : R) ⊗ₜ[R] m + (1 : R) ⊗ₜ[R] m') =
    ∑ i : (ULift.{u} (Fin 2)), 1 ⊗ₜ[R] match i with | 0 => m | 1 => m' := rfl
  simp_rw [TensorProduct.tmul_add, this,]
  rw [← toFun_eq_toFun']
  rw [toFun_sum_tmul_eq_coeff_sum]
  simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, one_pow,
    Finset.prod_const_one]
  simp only [generize, LinearMap.coe_mk, AddHom.coe_mk]
  change ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial (ULift.{u, 0} (Fin 2)) R)
          (MvPolynomial.X 0 ⊗ₜ[R] m + MvPolynomial.X 1 ⊗ₜ[R] m'))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) = _
  rw [lfsum_eq_of_locFinsupp]
  simp only [foo', TensorProduct.lid_symm_apply]
  rw [Finsupp.sum]
  rw [Finsupp.sum]
  sorry
  /- simp only [map_sum, lid_tmul, _root_.one_smul]
  simp only [finsum]
  split_ifs with h -/
  sorry

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [ground_apply, EmbeddingLike.apply_eq_iff_eq]
  have : ((1 : R) ⊗ₜ[R] m + (1 : R) ⊗ₜ[R] m') =
    ∑ i : (ULift.{u} (Fin 2)), 1 ⊗ₜ[R] match i with | 0 => m | 1 => m' := rfl
  simp_rw [TensorProduct.tmul_add, this,]
  rw [← toFun_eq_toFun']
  rw [toFun_sum_tmul_eq_coeff_sum]
  simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, one_pow,
    Finset.prod_const_one]
  simp only [generize, LinearMap.coe_mk, AddHom.coe_mk]
  change ((MvPolynomial.scalarRTensor
        (f.toFun (MvPolynomial (ULift.{u, 0} (Fin 2)) R)
          ( MvPolynomial.X 0 ⊗ₜ[R] m + MvPolynomial.X 1 ⊗ₜ[R] m'))).sum
    fun k n ↦ 1 ⊗ₜ[R] n) = _
  rw [lfsum_eq_of_locFinsupp]
  simp only [foo', TensorProduct.lid_symm_apply]
  rw [Finsupp.sum]
  rw [Finsupp.sum]
  have : (MvPolynomial.scalarRTensor
          (f.toFun (MvPolynomial (ULift.{u, 0} (Fin 2)) R)
            (MvPolynomial.X 0 ⊗ₜ[R] m + MvPolynomial.X 1 ⊗ₜ[R] m'))).support = ?_ := by
    ext d
    simp only [Finsupp.mem_support_iff, MvPolynomial.scalarRTensor_apply, ne_eq,
      EmbeddingLike.map_eq_zero_iff]
    simp only [LinearMap.rTensor_def]


    sorry
  sorry

  /- rw [lfsum_eq_of_locFinsupp]
  simp only [foo']

  simp only [coeff, generize, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply, one_pow, Finset.prod_const_one,
    TensorProduct.lid_symm_apply] -/


  /- rw [lfsum_eq_of_locFinsupp]
  --rw [Finsupp.sum]
  simp only [foo', TensorProduct.lid_symm_apply]
  simp only [Polynomial.scalarRTensor_apply] -/

  sorry

  · simp only [LocFinsupp]
    intro S _ _ m
    simp only [differential]
    simp only [lfsum, multiComponent_toFun']
    --simp only [polarized_multiComponent]
    have hf (i : ℕ) : LocFinsupp fun p ↦ polarized_multiComponent (map_pair i p) f := by
      exact locFinsupp_polarized_multiComponent i f
    have : (Function.support fun i ↦
        ((Finsupp.ofSupportFinite _ (hf i S m)).sum fun _ m ↦ m)).Finite := by
      simp only [polarized_multiComponent, multiComponent_toFun', polarized]
      sorry
    convert this
    simp only [multiComponent_toFun']
    split_ifs with h
    · rfl

    · exfalso
      apply h
      exact hf _

#exit

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [ground_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_eq_of_locFinsupp]
  --rw [Finsupp.sum]
  simp only [foo', TensorProduct.lid_symm_apply]
  simp only [Polynomial.scalarRTensor_apply]
  have : ((1 : R) ⊗ₜ[R] m + (1 : R) ⊗ₜ[R] m') =
    ∑ i : (ULift.{u} (Fin 2)), 1 ⊗ₜ[R] match i with | 0 => m | 1 => m' := sorry
  simp_rw [TensorProduct.tmul_add, this,]
  rw [← toFun_eq_toFun']
  rw [toFun_sum_tmul_eq_coeff_sum ]
  sorry

  · sorry

#exit

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [ground_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_eq_of_locFinsupp]
  rw [Finsupp.sum]
  have : (Finsupp.ofSupportFinite (fun i ↦
            (f.differential i).toFun' R
              (1 ⊗ₜ[R] fun i ↦
                match i with
                | { down := 0 } => m
                | { down := 1 } => m'))
          (by sorry)).support = ?_ := by sorry
  sorry
  sorry
  · sorry

lemma map_add_eq_sum_differential_apply (m m' : M) (f : M →ₚₗ[R] N) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by

  rw [map_add_eq_polarized_two_apply]
  simp only [ground_apply, EmbeddingLike.apply_eq_iff_eq]
  simp only [polarized_toFun'_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]

  simp only [differential, polarized_multiComponent, map_pair]
  rw [lfsum_eq_of_locFinsupp]
  --simp? [polarized_toFun'_apply]

  /- simp only [differential, polarized_multiComponent, map_pair]
  have := (f.polarized (ULift.{u} (Fin 2)))
  rw [← recompose_multiComponent (f.polarized (ULift (Fin 2)))]
  simp only [ground_apply, EmbeddingLike.apply_eq_iff_eq]
  simp? [polarized_toFun'_apply] -/
  /- congr
  ext x
  simp only [lfsum_eq_of_locFinsupp (LocFinsupp_multiComponent (polarized _ f)),
    multiComponent_toFun']
  rw [lfsum_eq_of_locFinsupp ] -/


  sorry
  ·
    sorry

lemma lground_apply (f : M →ₚₗ[R] N) : f.lground = f.ground := rfl

example : M → M →ₗ[R] N := fun m ↦ {
  toFun :=  fun (m' : M) ↦ (differential f 1)
    (fun (i : (ULift.{u} (Fin 2))) ↦ match i with | 0 => m | 1 => m')
  map_add' x y := by
    /- simp only [differential, ground_apply, map_pair_def]
    rw [← map_add]
    congr
    simp only [polarized_multiComponent, polarized]
    simp only [lfsum]
    rw [dif_pos]
    rw [← Finsupp.sum_add_index (by intros; rfl) (by intros; rfl)]
    simp only [multiComponent_toFun', LinearMap.rTensor_tmul,
      LinearMap.coe_restrictScalars]
    congr!
    ext n
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_add, Pi.add_apply]
    simp only [MvPolynomial.rTensor_apply]
    rw [← map_add]
    congr
    have : lfsum (fun (i : ULift.{u} (Fin 2)) ↦ proj R M i) =
      ∑ i,  proj R M i := sorry
    simp only [sum_proj, this]
    simp only [comp_toFun', Function.comp_apply] -/

    --simp only [proj_apply]
    sorry
  map_smul' r x := by
    /- simp only [differential, ground_apply, RingHom.id_apply]/-map_pair_def -/
    rw [← map_smul]
    congr
    rw [← lLfsum_apply]
    sorry -/
    sorry
}

/- Soit /'€ ^(M, N).
Considérons la loi polynôme sur le couple (M, N) égale à (D/*) (m, rc),
où m est la loi linéaire définie par l'injection identique de M dans Mi
et x la loi constante définie par l'application constante de M sur l'élé-
ment ^€Ms. Cette loi polynôme se notera (D^/*) (m) et s'appellera la
dérivée partielle de f par rapport à Isolément x de M. On la notera  -/

def partial_derivative (x : M) : M →ₚₗ[R] N := by
  set m : M → (ULift.{u, 0} (Fin 2) → M) := fun y ↦
    (fun (i : (ULift.{u} (Fin 2))) ↦ match i with | 0 => y | 1 => 0)
  set cx : M → (ULift.{u, 0} (Fin 2) → M) := fun y ↦
    (fun (i : (ULift.{u} (Fin 2))) ↦ match i with | 0 => 0 | 1 => x)
  have := (differential f 1).toFun'

  sorry

end PolynomialLaw
