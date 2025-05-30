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
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.proj i)).toFun
  isCompat' φ := by
    ext x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Function.comp_apply]
    sorry

lemma proj_apply (i : ι) (m : ι → M) : proj R M i m = m i := by simp [proj, ground_apply]

variable (ι) in
/-- `sum_proj R M ι` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] M` defined as the sum of all the
coordinate laws from  `(Π (_ : ι), M)`to `M`. -/
def sum_proj : (Π (_ : ι), M) →ₚₗ[R] M := lfsum (fun i ↦ proj R M i)

variable (ι) {R M}

/-- Given a polynomial law `f : M →ₚₗ[R] N` and a finite type `ι`, the `ι`-polarized of `f`
is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] N` obtained by composing `f` and `sum_proj R M ι`.
This is denoted by `Π_p` in Roby63 (where `p` corresponds to the size of `ι`). -/
def polarized : (Π (_ : ι), M) →ₚₗ[R] N := f.comp (sum_proj ι R M)

lemma polarized_apply [Fintype ι] {m : ι → M} : polarized ι f m = f (∑ (i : ι), m i):= by
  simp only [polarized, ground_apply]
  --congr
  sorry
  /- simp only [comp, sum_proj, Function.comp_apply]
  rw [lfsum_eq (locFinsupp_of_fintype _),
    Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (fun i _ => rfl),
    TensorProduct.tmul_sum]
  rfl -/

variable {f p}

lemma isHomogeneousOfDegree_polarized (hf : IsHomogeneousOfDegree p f) :
    IsHomogeneousOfDegree p (polarized ι f) := by
  rw [isHomogeneousOfDegree_of_coeff_iff] at hf ⊢
  intro n m d hd
  specialize hf n
  simp only [polarized, coeff_eq, EmbeddingLike.map_eq_zero_iff]
  sorry

-- Roby63, example in pg 234
lemma coeff_component_eq_zero_of_ne {n : ℕ} (m : (Fin n) → ι → M) (d : (Fin n) →₀ ℕ)
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

def foo (n p : ℕ) : (ULift (Fin 2)) → ℕ := (fun i ↦ match i with | 0 => p | 1 => n)

/- def foo (n p : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _) -/

variable {R M}

/-- The multihomogeneous component of multidegree `n : ι →₀ ℕ` of `f.polarized ι`.
  This is denoted by `Π^{n_1, ..., n_p}f` in Roby63. -/
def polarized_multiComponent [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (f : PolynomialLaw R M N) :
    PolynomialLaw R (Π (_ : ι), M) N := PolynomialLaw.multiComponent n (f.polarized ι)

-- Ideally I would like to write M × M
def differential : (Π (_ : ULift (Fin 2)), M) →ₚₗ[R] N :=
  PolynomialLaw.lfsum (fun (p : ℕ) ↦ polarized_multiComponent (foo n p) f)

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
  sorry

end PolynomialLaw
