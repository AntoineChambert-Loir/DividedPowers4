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

def map_pair (n p : ℕ) : (ULift.{u} (Fin 2)) →₀ ℕ :=
  (Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _))

lemma map_pair_def (n p : ℕ) : map_pair n p =
  (Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _)) := rfl

variable {R M}

-- I am not sure whether it is useful to add this.
/-- The multihomogeneous component of multidegree `n : ι →₀ ℕ` of `f.polarized ι`.
  This is denoted by `Π^{n_1, ..., n_p}f` in Roby63. -/
abbrev polarized_multiComponent [Fintype ι] [DecidableEq ι] (n : ι →₀ ℕ)
    (f : PolynomialLaw R M N) :
    PolynomialLaw R (Π (_ : ι), M) N := PolynomialLaw.multiComponent n (f.polarized ι)

open TensorProduct

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

end PolynomialLaw
