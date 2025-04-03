/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.ForMathlib.RingTheory.TensorProduct.Polynomial
import DividedPowers.PolynomialLaw.Coeff
import Mathlib.RingTheory.TensorProduct.Basic

universe u

/- # Homogeneous components of a polynomial map

Let `R` be a commutative ring, let `M` and `N` be `R`-modules, and let `f : M →ₚ[R] N` be a
polynomial map.

--## Main Definitions/Lemmas

* `f.IsHomogeneousOfDegree p` says that `f` is homogeneous of degree `p`, that is, for all
  commutative `R`-algebras `S : Type u` and  all `s : S`,
  `f.toFun' S (s • m) = s ^ p (f.toFun' S m)` for all `m : S ⊗[R] M`. The property extends to all
  `R`-algebras for `f.toFun`.

* `f` is homogeneous of degree `p` if and only if for all `m : ι → M`, and all `d : ι →₀ ℕ`,
  `f.coeff m d` vanishes unless the sum of `d` equals `p`.

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

Let `S` be an `R`-algebra
and let `j : S →ₐ[S] S[X]` be the canonical algebra map.

For `m : S ⊗[R] M`, we consider the element `X • (j m) : S[X] ⊗[R] M`
and its image `f.toFun' S[X] (X • (j m)) : S[X] ⊗[R] N`.
The components of `f` are defined so that
`f.toFun' S[X] (X • (j m)) = ∑ X ^ p • (j ((f.component p).toFun' S m))`.

If one consider the morphism of evaluation at 1, `ε : S[X] →ₐ[R] S`,
we have `ε ∘ j = @id S`, and the compatibility properties of `f` implies that
`f.toFun' S[X] m = ∑ (f.component p).toFun' S m`.

-/
namespace Polynomial

variable {R : Type*} [CommSemiring R] {S : Type _} [CommSemiring S] [Algebra R S]
  {S' : Type _} [CommSemiring S'] [Algebra R S']

lemma C_eq_algebraMap' (r : R) : C (algebraMap R S r) = algebraMap R S[X] r := rfl

/-- baseChange φ aplies φ on the coefficients of a polynomial in S[X] -/
noncomputable def baseChange (φ : S →ₐ[R] S') : S[X] →ₐ[R] S'[X] where
  toRingHom := eval₂RingHom (C.comp φ) X
  commutes' := fun r ↦ by simp [← C_eq_algebraMap']

lemma coeff_baseChange_apply (φ : S →ₐ[R] S') (f : S[X]) (p : ℕ) :
    coeff (baseChange φ f) p = φ (coeff f p) := by
  rw [baseChange, AlgHom.coe_mk, coe_eval₂RingHom]
  induction f using Polynomial.induction_on with
  | h_C r =>
    simp only [eval₂_C, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, coeff_C,
      apply_ite φ, map_zero]
  | h_add f g hf hg => simp only [eval₂_add, coeff_add, hf, hg, map_add]
  | h_monomial n r _ =>
    simp only [eval₂_mul, eval₂_C, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      eval₂_X_pow, coeff_C_mul, _root_.map_mul, coeff_X_pow, apply_ite φ, _root_.map_one, map_zero]

lemma lcoeff_comp_baseChange_eq (φ : S →ₐ[R] S') (p : ℕ) :
    LinearMap.comp (AlgHom.toLinearMap φ) ((lcoeff S p).restrictScalars R) =
      LinearMap.comp ((lcoeff S' p).restrictScalars R) (baseChange φ).toLinearMap := by
  ext f
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, lcoeff_apply,
    AlgHom.toLinearMap_apply, coeff_baseChange_apply]

lemma baseChange_monomial (φ : S →ₐ[R] S') (n : ℕ) (a : S) :
    (baseChange φ) ((Polynomial.monomial n) a) = (Polynomial.monomial n) (φ a) := by
  simp only [baseChange, AlgHom.coe_mk, coe_eval₂RingHom, eval₂_monomial, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, C_mul_X_pow_eq_monomial]

end Polynomial

namespace TensorProduct

open scoped TensorProduct

open LinearMap Finsupp

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

lemma exists_Finsupp (S : Type*) [CommSemiring S] [Algebra R S] (μ : S ⊗[R] M) :
    ∃ (m : S →₀ M), μ = m.sum (fun s x => s ⊗ₜ[R] x) := by
  classical
  induction μ using TensorProduct.induction_on with
  | zero => use 0; rw [sum_zero_index]
  | tmul s m => use single s m; simp only [tmul_zero, sum_single_index]
  | add x y hx hy =>
    obtain ⟨sx, rfl⟩ := hx
    obtain ⟨sy, rfl⟩ := hy
    use sx + sy
    rw [sum_add_index (fun _ ↦ by simp) (fun _ _ _ _ ↦ by rw [TensorProduct.tmul_add])]

theorem exists_Fin (S : Type*) [CommRing S] [Algebra R S] (sm : S ⊗[R] M) :
    ∃ (n : ℕ) (s : Fin n → S) (m : Fin n → M),
      sm = Finset.univ.sum (fun i ↦ (s i) ⊗ₜ[R] (m i)) := by
  obtain ⟨m, rfl⟩ := TensorProduct.exists_Finsupp S sm
  let e : m.support ≃ Fin (m.support.card) := Finset.equivFin _
  use m.support.card, fun i ↦ e.symm i, fun i ↦ m (e.symm i)
  rw [sum, ← Finset.sum_attach]
  apply Finset.sum_equiv e
  simp only [Finset.mem_attach, Finset.mem_univ, implies_true]
  intros; simp only [Equiv.symm_apply_apply]

lemma smul_rTensor {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {S : Type*} [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T) (s : S) (m : S ⊗[R] M) :
    φ s • (φ.toLinearMap.rTensor M m) = φ.toLinearMap.rTensor M (s • m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul s' m =>
    simp only [rTensor_tmul, AlgHom.toLinearMap_apply, smul_tmul', smul_eq_mul, _root_.map_mul]
  | add m m' hm hm' => simp only [map_add, smul_add, hm, hm']

variable {R : Type*} [CommSemiring R]
  {S : Type*} [Semiring S] [Algebra R S]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  {P : Type*} [AddCommMonoid P] [Module R P]
  {Q : Type*} [AddCommMonoid Q] [Module R Q]

/-- If `f` is `S`-linear, then `TensorProduct.map (f.restrictScalars R) g` is `S`-linear -/
lemma map_isLinearMap_of_left (f : M →ₗ[S] N) (g : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (f.restrictScalars R) g) where
  map_add  x y := by rw [map_add]
  map_smul c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul x y => simp only [smul_tmul', map_tmul, coe_restrictScalars, map_smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

lemma rTensor_smul' (f : M →ₗ[S] N) (s : S) (t : M ⊗[R] P) :
    rTensor P (f.restrictScalars R) (s • t) = s • (rTensor P (f.restrictScalars R) t) := by
  have : rTensor P (f.restrictScalars R) = (IsLinearMap.mk' _
    (TensorProduct.map_isLinearMap_of_left f LinearMap.id)).restrictScalars R := rfl
  rw [this, coe_restrictScalars, map_smul, IsLinearMap.mk'_apply]

end TensorProduct

open LinearMap TensorProduct
namespace PolynomialLaw
section Homogeneous

open Finsupp MvPolynomial

variable {R : Type u} {M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A polynomial map `f : M →ₚ[R] N` is homogeneous of degree `p`
  if the function `f.toFun' S` is homogeneous of degree `p` for all `S` -/
def IsHomogeneousOfDegree (p : ℕ) (f : PolynomialLaw R M N) : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (r : S) (m : S ⊗[R] M),
    f.toFun' S (r • m) = r ^ p • f.toFun' S m

theorem IsHomogeneousOfDegree_add (p : ℕ) {f g : PolynomialLaw R M N}
    (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree p) :
    (f + g).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsHomogeneousOfDegree_smul (p : ℕ) (r : R) {f : PolynomialLaw R M N}
    (hf : f.IsHomogeneousOfDegree p) : (r • f).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm r (s ^ p) (toFun' f S m)

/-- The submodule of Homogeneous Polynomial maps -/
def grade (p : ℕ) : Submodule R (PolynomialLaw R M N) where
  carrier            := IsHomogeneousOfDegree p
  add_mem' hf hg     := IsHomogeneousOfDegree_add p hf hg
  smul_mem' r f hf   := IsHomogeneousOfDegree_smul p r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_grade (f : PolynomialLaw R M N) (p : ℕ) :
    f ∈ grade p ↔ IsHomogeneousOfDegree p f := by rfl

/-- If `f` is homogeneous of degree `p`,
  then all `f.toFun S` are homogeneous of degree `p`. -/
lemma isHomogeneousOfDegree_toFun {p : ℕ} {f : PolynomialLaw R M N} (hf : IsHomogeneousOfDegree p f)
    (S : Type*) [CommRing S] [Algebra R S] (r : S) (m : S ⊗[R] M) :
    f.toFun S (r • m) = r ^ p • f.toFun S m := by
  choose n ψ  m' r' hm' hr' using PolynomialLaw.exists_lift' m r
  simp only [← hm', ← hr', ← isCompat_apply, toFun_eq_toFun', TensorProduct.smul_rTensor]
  rw [hf, ← TensorProduct.smul_rTensor, map_pow]

/-- If `f` is homogeneous of degree `p`, then `f.ground` is too.  -/
lemma isHomogeneousOfDegree_ground {p : ℕ} {f : PolynomialLaw R M N}
    (hf : IsHomogeneousOfDegree p f) (r : R) (m : M) :
    f.ground (r • m) = r ^ p • f.ground m := by
  simp only [ground, Function.comp_apply, map_smul, TensorProduct.lid_symm_apply, hf R r]

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish
  outside of degree `p` -/
lemma isHomogeneousOfDegree_coeff {f : PolynomialLaw R M N} {p : ℕ} (hf : IsHomogeneousOfDegree p f)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (m : ι → M) (d : ι →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≠ p) : PolynomialLaw.coeff m f d = 0 := by
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
  let μ : MvPolynomial (Option ι) R ⊗[R] M := Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m i)
  have hf' := isHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (X none) μ
  simp only [μ, Finset.smul_sum, TensorProduct.smul_tmul', image_eq_coeff_sum, Finsupp.smul_sum,
    TensorProduct.smul_tmul'] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [map_finsupp_sum, LinearMap.map_smul, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hφ
  rw [Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
    AddHom.coe_mk, lid_tmul, φ] at hφ
  rw [he, coeff_monomial, if_pos, _root_.one_smul, he, coeff_monomial, if_neg, _root_.zero_smul]
    at hφ
  exact hφ
  · intro hd'
    apply hd
    convert (DFunLike.ext_iff.mp hd'.symm) none <;> exact (he_none _ _)
  · simp only [Finset.mem_univ, forall_true_left, implies_true,
      Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  all_goals
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
      AddHom.coe_mk, lid_tmul, φ]
    rw [he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i

/-- A polynomial map `f` is homogeneous of degree `p` iff all of
  its coefficients `PolynomialLaw.coeff m f` vanish outside of degree `p`,
  for all `m : Fin n → M`. -/
theorem isHomogeneousOfDegree_of_coeff_iff (f : PolynomialLaw R M N) (p : ℕ) :
    IsHomogeneousOfDegree p f ↔ ∀ (n : ℕ) (m : Fin n → M) (d : Fin n →₀ ℕ)
      (_ : d.sum (fun _ n => n) ≠ p), PolynomialLaw.coeff m f d = 0 := by
  refine ⟨fun hf _ m d hd => isHomogeneousOfDegree_coeff hf m d hd, fun H S _ _ r μ => ?_⟩
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
  simp only [Finset.smul_sum, TensorProduct.smul_tmul']
  rw [← toFun_eq_toFun', image_eq_coeff_sum, image_eq_coeff_sum, Finsupp.smul_sum]
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

theorem IsHomogeneousOfDegree.comp {P : Type*} [AddCommGroup P] [Module R P]
    {f : M →ₚ[R] N} {g : N →ₚ[R] P} {p q : ℕ}
    (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsHomogeneousOfDegree (p * q) := by
  intro S _ _ r m
  simp [comp_toFun', hf S, hg S, ← pow_mul]

end Homogeneous

section ConstantMap

variable {R : Type u} [CommRing R] {M N : Type _} [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

open MvPolynomial

noncomputable def ofConstant (n : N) : PolynomialLaw R M N where
  toFun' S _ _ _:= TensorProduct.tmul R 1 n
  isCompat' φ   := by ext; simp

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantHom : N →ₗ[R] (grade 0 : Submodule R (PolynomialLaw R M N)) := {
  toFun := fun n ↦ {
    val := ofConstant n
    property := by
      rw [grade, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
      intro S _ _ r sm
      rw [pow_zero, _root_.one_smul]
      rfl }
  map_add'  := fun x y ↦ by
    simp only [ofConstant, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    ext
    simp only [add_def_apply, TensorProduct.tmul_add]
  map_smul' := fun r x ↦ by
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq, ofConstant,
      TensorProduct.tmul_smul]
    rfl }

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantEquiv :
    N ≃ₗ[R] (grade 0 : Submodule R (PolynomialLaw R M N)) := {
  ofConstantHom with
  invFun    := fun f ↦ f.val.ground 0
  left_inv  := fun x ↦ by
    simp only [ground, ofConstantHom, ofConstant, AddHom.toFun_eq_coe, AddHom.coe_mk,
      Function.comp_apply, lid_tmul, _root_.one_smul]
  right_inv := fun x ↦ by
    obtain ⟨f, hf⟩ := x
    simp only [mem_grade, isHomogeneousOfDegree_toFun] at hf
    rw [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Subtype.ext_iff, Subtype.coe_mk]
    simp only [ofConstantHom, ground, Function.comp_apply, map_zero, coe_mk, AddHom.coe_mk]
    ext S _ _ m
    conv_rhs =>
      rw [← _root_.one_smul (M := S) (f.toFun' S m), ← pow_zero 0, ← hf S _ m, _root_.zero_smul]
    simp only [ofConstant, includeRight_lid, isCompat_apply', map_zero] }

end ConstantMap

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
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M) {d : ι →₀ ℕ}
    (hd : Finsupp.sum d (fun _ n => n) ≠ 1) : (coeff m f) d = 0 :=
  isHomogeneousOfDegree_coeff hf m d hd

theorem isHomogeneousOfDegreeOne_coeff_support_le {f : PolynomialLaw R M N}
    (hf : IsHomogeneousOfDegree 1 f) {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → M) :
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
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : Finset.sum Finset.univ (fun (j : ι) => (Pi.single i (1 : R) j) ⊗ₜ[R] m j) =
      1 ⊗ₜ[R] m i := by
    rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_tmul])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same]
  simp only [← this, image_eq_coeff_sum, map_finsupp_sum, TensorProduct.lid_tmul]
  rw [Finsupp.sum_of_support_subset _ (isHomogeneousOfDegreeOne_coeff_support_le hf m),
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
    forall_exists_index, implies_true, forall_const]


noncomputable def ofLinearMap (v : M →ₗ[R] N) : PolynomialLaw R M N where
  toFun' S _ _ := v.baseChange S
  isCompat' φ  := by
    ext
    simp only [← LinearMap.comp_apply, baseChange_eq_ltensor, Function.comp_apply,
      rTensor_comp_lTensor, lTensor_comp_rTensor]

lemma ofLinearMap_mem_grade_one (v : M →ₗ[R] N) :
    IsHomogeneousOfDegree 1 (ofLinearMap v) :=
  fun S _ _ r m => by simp only [ofLinearMap, LinearMapClass.map_smul, pow_one]

theorem IsHomogeneousOfDegree.comp_ofLinearMap
    {P : Type*} [AddCommGroup P] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₚ[R] P} {q : ℕ}
    (hg : g.IsHomogeneousOfDegree q) :
    (g.comp (PolynomialLaw.ofLinearMap f)).IsHomogeneousOfDegree q := by
  simpa using IsHomogeneousOfDegree.comp (ofLinearMap_mem_grade_one f) hg

theorem IsHomogeneousOfDegree.ofLinearMap_comp
    {P : Type*} [AddCommGroup P] [Module R P]
    {f : M →ₚ[R] N} {g : N →ₗ[R] P} {p : ℕ}
    (hf : f.IsHomogeneousOfDegree p) :
    ((PolynomialLaw.ofLinearMap g).comp f).IsHomogeneousOfDegree p := by
  simpa using IsHomogeneousOfDegree.comp hf (ofLinearMap_mem_grade_one g)

theorem ofLinearMap_toFun' (u : M →ₗ[R] N)
    (S : Type u) [CommRing S] [Algebra R S] :
    (ofLinearMap u).toFun' S = LinearMap.baseChange S u := rfl

theorem ofLinearMap_toFun (u : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S] :
    (ofLinearMap u).toFun S = u.baseChange S := by
  ext sm
  obtain ⟨n, φ, p, rfl⟩ := exists_lift sm
  simp only [← isCompat_apply, toFun_eq_toFun', ofLinearMap_toFun', baseChange_eq_ltensor,
    ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

open MvPolynomial

theorem ofLinearMap_coeff_single (u : M →ₗ[R] N) (ι : Type*) [DecidableEq ι] [Fintype ι]
    (m : ι → M) (i : ι) : ((coeff m) (ofLinearMap u)) (Finsupp.single i 1) = u (m i) := by
  rw [coeff, generize, coe_comp, LinearEquiv.coe_coe, coe_mk, AddHom.coe_mk, Function.comp_apply]
  simp only [ofLinearMap_toFun, map_sum, LinearMap.baseChange_tmul]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single i _ (fun hi => by
    simp only [mem_univ, not_true_eq_false] at hi), scalarRTensor_apply_tmul_apply,
      coeff_X, _root_.one_smul]
  · intro b _ hb
    have hb' : ¬ Finsupp.single b 1 = Finsupp.single i 1 := by
      rwa [Finsupp.single_left_inj]; norm_num
    rw [scalarRTensor_apply_tmul_apply, coeff_X', if_neg hb', _root_.zero_smul]

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
    exact Or.inl ⟨ha, by simpa [ha, add_right_eq_self] using h⟩

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
    rw [image_eq_coeff_sum, Finsupp.sum_of_support_subset _
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
      forall_exists_index, implies_true, forall_const] }

end Linear

section Quadratic

end Quadratic

section Components

open Polynomial

/- Here we define the homogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

variable {R : Type u} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₚ[R] N) (p : ℕ)

theorem Polynomial.baseChange_comp_monomial_eq
    {S : Type*} [CommRing S] [Algebra R S]
    {S' : Type*} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
    (p : ℕ) :
    (Polynomial.baseChange φ).toLinearMap ∘ₗ
      ((monomial p).restrictScalars R) =
        ((monomial p).restrictScalars R) ∘ₗ φ.toLinearMap := by
  ext
  simp only [coe_comp, coe_restrictScalars, Function.comp_apply,
    AlgHom.toLinearMap_apply, baseChange_monomial]

/-- The homogeneous components of a `PolynomialLaw` -/
@[simps] noncomputable def component (p : ℕ) (f : PolynomialLaw R M N) :
    PolynomialLaw R M N where
  toFun' S _ _ := fun m ↦ rTensor R N S
    (f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M m))  p
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    dsimp
    simp only [LinearEquiv.rTensor'_apply, Function.comp_apply, rTensor_apply, ← rTensor_comp_apply]
    rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply', ← rTensor_comp_apply]
    rw [Polynomial.baseChange_comp_monomial_eq]

theorem component.toFun'_apply (p : ℕ) (f : PolynomialLaw R M N)
  (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
  (f.component p).toFun' S m = rTensor R N S (f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M m))  p := rfl

theorem component_toFun_apply (p : ℕ) (f : PolynomialLaw R M N)
    (S : Type*) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (f.component p).toFun S m =
      Polynomial.rTensor R N S (f.toFun S[X] (((monomial 1).restrictScalars R).rTensor M m)) p := by
  obtain ⟨n, ψ, q, rfl⟩ :=  exists_lift m
  rw [← PolynomialLaw.isCompat_apply]
  rw [toFun_eq_toFun'_apply, component.toFun'_apply]
  rw [← LinearMap.rTensor_comp_apply]
  rw [← Polynomial.baseChange_comp_monomial_eq]
  rw [LinearMap.rTensor_comp_apply]
  rw [← PolynomialLaw.isCompat_apply]
  simp only [LinearEquiv.rTensor'_apply, Function.comp_apply, rTensor_apply, ← rTensor_comp_apply]
  rw [lcoeff_comp_baseChange_eq, toFun_eq_toFun'_apply]

/-
-- Faire une preuve directe  qui court-circuite `lcoeff_comp_baseChange_eq`?
/-- The homogeneous components of a `PolynomialLaw` -/
noncomputable example (p : ℕ) (f : PolynomialLaw R M N) :
  PolynomialLaw R M N where
  toFun' S _ _ := fun m ↦ rTensor R N S
    (f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M m)) p
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    simp only [LinearEquiv.rTensor'_apply, Function.comp_apply]
    simp only [← LinearMap.rTensor_comp_apply]
    have : (((monomial 1).restrictScalars R) ∘ₗ φ.toLinearMap) = ((baseChange φ).toLinearMap.comp ((monomial 1).restrictScalars R)) := by
      sorry
    rw [this, LinearMap.rTensor_comp_apply, ← f.isCompat_apply']
    set sn := f.toFun' S[X] (((monomial (R := S) 1).restrictScalars R).rTensor M sm)
    simp only [rTensor_apply]
    simp only [← LinearMap.comp_apply]
    simp only [← LinearMap.rTensor_comp]
    sorry
-/

/-- `f.PolynomialLaw.component p` is homogeneous of degree p -/
lemma componentIsHomogeneous (p : ℕ) (f : PolynomialLaw R M N) :
    IsHomogeneousOfDegree p (f.component p) := by
  intro S _ _ s sm
  dsimp [component]
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
    | h_add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | h_monomial n a =>
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
      apply congr_arg
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
      mk_apply, smul_tmul', smul_eq_mul]

theorem component_add (p : ℕ) (f g : PolynomialLaw R M N) :
    (f + g).component p = f.component p + g.component p := by
  ext S _ _ sm
  simp only [component, add_def_apply, map_add, Finsupp.coe_add, Pi.add_apply]

theorem component_smul (r : R) (f : PolynomialLaw R M N) :
    (r • f).component p = r • f.component p := by
  ext S _ _ sm
  simp only [component, smul_def_apply, rTensor_apply, LinearMapClass.map_smul]

theorem support_component' (f : M →ₚ[R] N)
    {S : Type u} [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    Function.support (fun i => ((fun p => component p f) i).toFun' S m) =
    (rTensor R N S ((f.toFun' S[X] ((rTensor M ((monomial 1).restrictScalars R)) m)))).support := by
  ext n
  simp only [component, Finsupp.fun_support_eq, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]

theorem support_component (f : M →ₚ[R] N) {S : Type*} [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    Function.support (fun i => ((fun p => component p f) i).toFun S m) =
    (rTensor R N S ((f.toFun S[X] ((rTensor M ((monomial 1).restrictScalars R)) m)))).support := by
  ext i
  rw [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_iff_not,
    component_toFun_apply]

theorem LocFinsupp_component (f : PolynomialLaw R M N) :
    LocFinsupp (fun p ↦ f.component p) := fun S _ _ m ↦ by
  simp only [support_component', Finset.finite_toSet]

theorem LocFinsupp_component_eq (f : M →ₚ[R] N)
    {S : Type u} [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (Finsupp.ofSupportFinite (fun i => (component i f).toFun' S m)
      (LocFinsupp_component f S m)) =
    rTensor R N S ((f.toFun' S[X] ((rTensor M ((monomial 1).restrictScalars R)) m))) := by
  ext n
  simp only [component, Finsupp.ofSupportFinite_coe]

theorem _root_.Polynomial.rTensor'_sum
    {S : Type*} [CommSemiring S] [Algebra R S] (φ : ℕ → S) (sXn : S[X] ⊗[R] N) :
    (rTensor R N S sXn).sum (fun p sn ↦ (φ p) • sn) =
      (Polynomial.lsum (fun n ↦ (LinearMap.lsmul S S (φ n)).restrictScalars R)).rTensor N sXn := by
  induction sXn using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.sum_zero_index]
  | tmul p n =>
    induction p using Polynomial.induction_on with
    | h_C s =>
      rw [Finsupp.sum_eq_single 0, rTensor_apply, rTensor_tmul, rTensor_tmul]
      simp only [coe_restrictScalars, lcoeff_apply, coeff_C_zero, Polynomial.lsum_apply,
        lsmul_apply, smul_eq_mul, mul_zero, sum_C_index]
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      · intro b _ hb
        simp only [rTensor_apply, rTensor_tmul, coe_restrictScalars, lcoeff_apply]
        rw [Polynomial.coeff_C, if_neg hb, zero_tmul, smul_zero]
      · exact fun _ => by rw [smul_zero]
    | h_add p q hp hq =>
      simp only [add_tmul, LinearEquiv.map_add]
      rw [Finsupp.sum_add_index, hp, hq, LinearMap.map_add]
      · intro x _; apply smul_zero
      · intro x _; apply smul_add
    | h_monomial p s _ =>
      rw [Finsupp.sum_eq_single (p + 1), rTensor_apply, rTensor_tmul]
      · simp only [coe_restrictScalars, lcoeff_apply, coeff_C_mul, coeff_X_pow,
          ↓reduceIte, mul_one, rTensor_tmul, Polynomial.lsum_apply,
          lsmul_apply, smul_eq_mul]
        rw [C_mul_X_pow_eq_monomial, sum_monomial_index, smul_tmul', smul_eq_mul]
        rw [mul_zero]
      · intro b  _ hb
        simp only [rTensor_apply, rTensor_tmul, coe_restrictScalars, lcoeff_apply, coeff_C_mul,
          coeff_X_pow, mul_ite, mul_one, mul_zero, if_neg hb, zero_tmul, smul_zero]
      · exact fun _ ↦ smul_zero _
  | add p q hp hq =>
    simp only [add_tmul, LinearEquiv.map_add]
    rw [Finsupp.sum_add_index, hp, hq, LinearMap.map_add]
    · intro x _; exact smul_zero _
    · intro x _; exact smul_add _


/-- A polynomial map is the locally finite sum of its homogeneous components.
(PolynomialLaw lies in between the direct sum and the product of its graded submodules,
hence there is no graded module structure.) -/
theorem recompose_component (f : PolynomialLaw R M N) :
    PolynomialLaw.lfsum (fun p ↦ f.component p) = f := by
  ext S _ _ sm
  rw [lfsum_eq (LocFinsupp_component f), LocFinsupp_component_eq]
  have hsm : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor M
    (((monomial 1).restrictScalars R).rTensor M sm) := by
    rw [← LinearMap.rTensor_comp_apply, LinearMap.rTensor, eq_comm]
    convert DFunLike.congr_fun TensorProduct.map_id sm
    ext s
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.coe_restrictScalars', aeval_monomial, Algebra.id.map_eq_id, RingHom.id_apply, pow_one,
      mul_one, id_coe, id_eq]
  conv_rhs => rw [hsm, ← f.isCompat_apply']
  generalize f.toFun' S[X] (((monomial 1).restrictScalars R).rTensor M sm) = sn
  convert rTensor'_sum (R := R) (fun _ ↦ 1) sn
  simp only [_root_.one_smul]
  ext p
  simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', coe_aeval_eq_eval,
    Polynomial.lsum_apply, coe_restrictScalars, lsmul_apply, smul_eq_mul, one_mul, eval_eq_sum]
  apply congr_arg₂ _ rfl
  simp only [one_pow, mul_one]

end Components

end PolynomialLaw

--#lint
