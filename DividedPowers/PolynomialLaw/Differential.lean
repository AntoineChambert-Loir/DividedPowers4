import DividedPowers.PolynomialLaw.MultiHomogeneous

noncomputable section

universe u

variable {ι : Type u} -- Should we instead assume `[Finite ι]`?

variable (R : Type u) [CommSemiring R] (M : Type*) [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

variable (f : M →ₚₗ[R] N) (n p : ℕ)
namespace PolynomialLaw

section Polarized

/-- `proj R M i` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] M` obtained by prolonging the
`i`th canonical projection. -/
def proj (i : ι) : (Π (_ : ι), M) →ₚₗ[R] M where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.proj i))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma proj_apply (i : ι) (m : ι → M) : proj R M i m = m i := by simp [proj, ground_apply]

lemma proj_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommSemiring S] [Algebra R S]
    (i : ι) {m : TensorProduct R S (ι → M)} : (proj R M i).toFun' S m =
    (TensorProduct.piRight R R S fun _ ↦ M) m i := by
  simp only [proj, TensorProduct.piRight_apply]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

-- TODO: add a lemma lfsum_eq_sum_of_fintype and use it instead of lfsum_eq below.

variable (ι) in
/-- `sum_proj R M ι` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] M` defined as the sum of all the
coordinate laws from  `(Π (_ : ι), M)`to `M`. -/
def sum_proj : (Π (_ : ι), M) →ₚₗ[R] M := lfsum (fun i ↦ proj R M i)

lemma sum_proj_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (ι → M)} : (sum_proj ι R M).toFun' S m =
    (∑ i, (TensorProduct.piRight R R S fun _ ↦ M) m i) := by
  rw [sum_proj, TensorProduct.piRight_apply,
    lfsum_eq_of_locFinsupp (locFinsupp_of_fintype _), Finsupp.sum_fintype _ _ (by intro; rfl)]
  exact Finset.sum_congr rfl (fun i _ ↦ proj_toFun'_apply R M i)

variable (ι) {R M}

/-- Given a polynomial law `f : M →ₚₗ[R] N` and a finite type `ι`, the `ι`-polarized of `f`
is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] N` obtained by composing `f` and `sum_proj R M ι`.
This is denoted by `Π_p` in Roby63 (where `p` corresponds to the size of `ι`). -/
def polarized : (Π (_ : ι), M) →ₚₗ[R] N := f.comp (sum_proj ι R M)

lemma polarized_apply [Fintype ι] {m : ι → M} : polarized ι f m = f (∑ (i : ι), m i):= by
  simp only [polarized, ground_apply, sum_proj, comp_toFun',
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  congr 1
  rw [lfsum_eq_of_locFinsupp (locFinsupp_of_fintype _), Finsupp.sum_fintype _ _ (by intro; rfl),
    TensorProduct.tmul_sum]
  rfl

lemma polarized_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (ι → M)} : (polarized ι f).toFun' S m =
      f.toFun' S (∑ i, (TensorProduct.piRight R R S fun _ ↦ M) m i) := by
  simp [polarized, comp_toFun', sum_proj_toFun'_apply]

variable {f p}

variable (R M) in
lemma _root_.TensorProduct.piRightHom_smul_proj [Fintype ι] {S : Type u} [CommSemiring S]
    [Algebra R S] (s : S) (m : TensorProduct R S (ι → M)) (i : ι) :
    (TensorProduct.piRightHom R R S fun _ ↦ M) (s • m) i =
      s • (TensorProduct.piRightHom R R S fun _ ↦ M) m i := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s' m => simp only [TensorProduct.piRightHom_tmul]; rfl
  | add m m' hm hm' => simp only [smul_add, map_add, Pi.add_apply, hm, hm']

lemma isHomogeneousOfDegree_polarized [Fintype ι] (hf : IsHomogeneousOfDegree p f) :
    IsHomogeneousOfDegree p (polarized ι f) := by
  classical
  rw [IsHomogeneousOfDegree] at hf ⊢
  intro S _ _ s m
  simp only [polarized_toFun'_apply, ← hf S s (∑ (i : ι), (TensorProduct.piRight R R _ _) m i)]
  congr
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ TensorProduct.piRightHom_smul_proj ι R M s _ i)

-- Roby63, example in pg 234
lemma coeff_component_eq_zero_of_ne [Fintype ι] {n : ℕ} (m : (Fin n) → ι → M) (d : (Fin n) →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≠ p) (hf : IsHomogeneousOfDegree p f) :
    coeff m (polarized ι f) d = 0 := by
  revert n
  rw [← isHomogeneousOfDegree_of_coeff_iff]
  exact isHomogeneousOfDegree_polarized ι hf

end Polarized

-- Π^{n_1, ..., n_p}
/- def foo (m : ι → M) : PolynomialLaw R M N →ₗ[R] (ι →₀ ℕ) →₀ N where
  toFun := fun f ↦ PolynomialLaw.coeff m (f.component p)
  map_add' := sorry
  map_smul' := sorry -/

-- ∀ (n : ℕ) (m : (Fin n) → M) (d : (Fin n) →₀ ℕ)
  --    (_ : d.sum (fun _ n => n) ≠ p), PolynomialLaw.coeff m f d = 0

def map_pair (n p : ℕ) : (ULift.{u} (Fin 2)) →₀ ℕ :=
  (Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _))

lemma map_pair_def (n p : ℕ) : map_pair n p =
  (Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _)) := rfl

/- def foo (n p : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _) -/

variable {R M}

-- I am not sure whether it is useful to add this.
/-- The multihomogeneous component of multidegree `n : ι →₀ ℕ` of `f.polarized ι`.
  This is denoted by `Π^{n_1, ..., n_p}f` in Roby63. -/
abbrev polarized_multiComponent [Fintype ι] [DecidableEq ι] (n : ι →₀ ℕ)
    (f : PolynomialLaw R M N) :
    PolynomialLaw R (Π (_ : ι), M) N := PolynomialLaw.multiComponent n (f.polarized ι)

-- Ideally I would like to write M × M
def differential : (Π (_ : ULift (Fin 2)), M) →ₚₗ[R] N :=
  PolynomialLaw.lfsum (fun (p : ℕ) ↦ polarized_multiComponent (map_pair n p) f)

lemma map_add_eq_polarized_two_apply (m m' : M) :
    f (m + m') = (f.polarized (ULift (Fin 2))) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  simp only [polarized_apply]
  congr 1
  change m + m' = m + (m' + 0)
  simp

lemma foo (n : ℕ) (m m' : M) :
    f.differential n ((fun i ↦ match i with | 0 => m | 1 => m')) =
      Polynomial.scalarRTensor R N
        (f.toFun' (Polynomial R) (1 ⊗ₜ m + Polynomial.X ⊗ₜ m')) n := by
  /- simp only [differential, ground_apply, Polynomial.scalarRTensor_apply,
    EmbeddingLike.apply_eq_iff_eq, map_pair_def]
  rw [lfsum_eq_of_locFinsupp] -/

  simp only [ground_apply, Polynomial.scalarRTensor_apply, EmbeddingLike.apply_eq_iff_eq]

  sorry


lemma foo' (n : ℕ) (m m' : M) :
   ((f.differential n).toFun' R
      (1 ⊗ₜ[R] fun i ↦ match i with | { down := 0 } => m | { down := 1 } => m')) =
      (TensorProduct.lid R N).symm
        (Polynomial.scalarRTensor R N (f.toFun' (Polynomial R) (1 ⊗ₜ m + Polynomial.X ⊗ₜ m')) n) :=
  sorry

open TensorProduct
/-


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
    multiComponent_toFun_apply, coeff_el'_S_def] -/

/- theorem support_polatized_multiComponent' (f : M →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] M) :
    Function.support (fun (p : ℕ) ↦ polarized_multiComponent (map_pair n p) f) =
    ?_ := by
  ext n
  simp [multiComponent, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, coeff_el'_S_def] -/

-- TODO: golf
theorem locFinsupp_polarized_multiComponent (f : PolynomialLaw R M N) :
    LocFinsupp (fun (p : ℕ) ↦ polarized_multiComponent (map_pair n p) f) := fun S _ _ m ↦ by
  set g : ℕ → (ULift.{u, 0} (Fin 2) →₀ ℕ) := fun p ↦ (map_pair n p)
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
  exact LocFinsupp_multiComponent _ _ _

/- noncomputable def el_S''' (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    MvPolynomial ι S ⊗[R] N := f.toFun (MvPolynomial ι S) (el_S''_hom ι R M S m)-/

lemma locFinsupp_differential {M N : Type u} [AddCommGroup M] [Module R M]
 [AddCommGroup N] [Module R N] (f : M →ₚₗ[R] N) (n : ℕ) : LocFinsupp fun n ↦ f.differential n := by
  simp only [LocFinsupp]
  intro S _ _ sm
  simp only [differential]
  simp_rw [lfsum_eq_of_locFinsupp (locFinsupp_polarized_multiComponent _ f)]
  have : (Function.support fun i ↦ (Finsupp.ofSupportFinite (fun i_1 ↦
    (polarized_multiComponent (map_pair i i_1) f).toFun' S sm) (by sorry)).sum fun x m ↦
      m) = ?_ := by
    let g := (polarized ((ULift.{u, 0} (Fin 2))) f)
    let e := el_S''' (N := N) sm g
    -- Ideal: take the RHS to be the Set.range of the total degree of `e`, and show
    -- that LHS ⊆ RHS
    ext x
    simp only [multiComponent_toFun', Function.mem_support, ne_eq]
    sorry
  sorry
  sorry

lemma map_add_eq_sum_differential_apply''' (m m' : M) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
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
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [lfsum_eq_of_locFinsupp]
  · rw [toFun_eq_toFun']
    simp only [foo', lid_symm_apply]
    rw [Finsupp.sum, Finsupp.sum]
    congr
    · sorry
    · ext a
      simp?
      sorry
  · sorry

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
