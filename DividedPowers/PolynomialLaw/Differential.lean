import DividedPowers.PolynomialLaw.MultiHomogeneous

noncomputable section

universe u

variable {ι : Type u} -- Should we instead assume `[Finite ι]`?

variable (R : Type u) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
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

lemma proj_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommRing S] [Algebra R S]
    (i : ι) {m : TensorProduct R S (ι → M)} : (proj R M i).toFun' S m =
    (TensorProduct.piRight R R S fun i ↦ M) m i := by
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

lemma sum_proj_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommRing S] [Algebra R S]
    {m : TensorProduct R S (ι → M)} : (sum_proj ι R M).toFun' S m =
    (∑ i, (TensorProduct.piRight R R S fun _ ↦ M) m i) := by
  rw [sum_proj, TensorProduct.piRight_apply,
    lfsum_eq (locFinsupp_of_fintype _), Finsupp.sum_fintype _ _ (by intro; rfl)]
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
  rw [lfsum_eq (locFinsupp_of_fintype _), Finsupp.sum_fintype _ _ (by intro; rfl),
    TensorProduct.tmul_sum]
  rfl

lemma polarized_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommRing S] [Algebra R S]
    {m : TensorProduct R S (ι → M)} : (polarized ι f).toFun' S m =
      f.toFun' S (∑ i, (TensorProduct.piRight R R S fun _ ↦ M) m i) := by
  simp [polarized, comp_toFun', sum_proj_toFun'_apply]

variable {f p}

variable (R M) in
lemma _root_.TensorProduct.piRightHom_smul_proj [Fintype ι] {S : Type u} [CommRing S]
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

def map_pair (n p : ℕ) : (ULift (Fin 2)) → ℕ := (fun i ↦ match i with | 0 => p | 1 => n)

lemma map_pair_def (n p : ℕ) : map_pair n p = (fun i ↦ match i with | 0 => p | 1 => n) := rfl

/- def foo (n p : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _) -/

variable {R M}

-- I am not sure whether it is useful to add this.
/-- The multihomogeneous component of multidegree `n : ι →₀ ℕ` of `f.polarized ι`.
  This is denoted by `Π^{n_1, ..., n_p}f` in Roby63. -/
abbrev polarized_multiComponent [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
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

lemma map_add_eq_sum_differential_apply (m m' : M) :
    f (m + m') =
      lfsum (fun n ↦ f.differential n) ((fun i ↦ match i with | 0 => m | 1 => m')) := by
  rw [map_add_eq_polarized_two_apply]
  simp only [differential, polarized_multiComponent]
  rw [← recompose_multiComponent (f.polarized (ULift (Fin 2)))]
  congr
  ext x
  simp only [lfsum_eq (LocFinsupp_multiComponent (polarized _ f)), multiComponent_toFun']
  rw [lfsum_eq]
  sorry
  sorry

lemma lground_apply (f : M →ₚₗ[R] N) : f.lground = f.ground := rfl

example : M → M →ₗ[R] N := fun m ↦ {
  toFun :=  fun (m' : M) ↦ (differential f 1)
    (fun (i : (ULift.{u} (Fin 2))) ↦ match i with | 0 => m | 1 => m')
  map_add' x y := by
    simp only [differential, ground_apply, map_pair_def]
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
    simp only [comp_toFun', Function.comp_apply]

    --simp only [proj_apply]
    sorry

    · sorry

    -- simp only [differential, ground_apply,/-map_pair_def -/]
    --rw [map_add]
    /- rw [← lLfsum_apply]
    congr


    sorry
    · simp [polarized_multiComponent]

      sorry -/
  map_smul' r x := by
    simp only [differential, ground_apply, RingHom.id_apply]/-map_pair_def -/
    rw [← map_smul]
    congr
    rw [← lLfsum_apply]
    sorry
    sorry
}

/- Soit /'€ ^(M, N).
Considérons la loi polynôme sur le couple (M, N) égale à (D/*) (m, rc),
où m est la loi linéaire définie par l'injection identique de M dans Mi
et x la loi constante définie par l'application constante de M sur l'élé-
ment ^€Ms. Cette loi polynôme se notera (D^/*) (m) et s'appellera la
dérivée partielle de f par rapport à Isolément x de M. On la notera aussi ,—•-/

def partial_derivative (x : M) : M →ₚₗ[R] N := by
  set m : M → (ULift.{u, 0} (Fin 2) → M) := fun y ↦
    (fun (i : (ULift.{u} (Fin 2))) ↦ match i with | 0 => y | 1 => 0)
  set cx : M → (ULift.{u, 0} (Fin 2) → M) := fun y ↦
    (fun (i : (ULift.{u} (Fin 2))) ↦ match i with | 0 => 0 | 1 => x)
  have := (differential f 1).toFun'

  sorry

end PolynomialLaw
