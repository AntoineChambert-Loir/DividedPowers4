import DividedPowers.ForMathlib.RingTheory.SubmoduleMem
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import DividedPowers.PolynomialLaw.Basic2

import Mathlib.RingTheory.TensorProduct.Basic

universe u

variable (R : Type u) [CommSemiring R]

/- # Prerequisites. -/

section Prerequisites

section Finset

open Equiv Finsupp Function Set

@[to_additive]
theorem Finset.prod_congr_equiv {α β M : Type*} [CommMonoid M] {f : α → M} {s : Finset α}
    (e : α ≃ β) : s.prod f = (s.map e).prod (f ∘ e.symm)  := by
  simp [comp_apply, prod_map, coe_toEmbedding, symm_apply_apply]

@[to_additive]
theorem Finset.prod_congr_equiv' {α β M : Type*} [CommMonoid M] {f : β → M} {s : Finset α}
    (e : α ≃ β) : s.prod (f ∘ e) = (s.map e).prod f := by
  simp [comp_apply, prod_map, coe_toEmbedding]

theorem Finsupp.ofSupportFinite_support {ι α : Type*} [Zero α] {f : ι → α} (hf : f.support.Finite) :
    (ofSupportFinite f hf).support = hf.toFinset := by
  ext; simp [ofSupportFinite_coe, mem_support_iff, Finite.mem_toFinset, mem_support]

end Finset

namespace LinearForm

open Algebra Algebra.TensorProduct Function LinearMap TensorProduct

variable (S S' M : Type*) [CommSemiring S] [Algebra R S] [CommSemiring S'] [Algebra R S']
  (φ : S →ₐ[R] S') [AddCommMonoid M] [Module R M]

noncomputable def baseChange (f : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (Algebra.TensorProduct.rid R S S).toLinearMap.comp (f.baseChange S)

theorem baseChange_apply_tmul (f : M →ₗ[R] R) (r : S) (m : M) :
    baseChange R S M f (r ⊗ₜ[R] m) = r * ((f m) • (1 : S)) := by
  simp [baseChange, coe_comp, Function.comp_apply, baseChange_tmul, AlgEquiv.toLinearMap_apply,
    rid_tmul, Algebra.mul_smul_comm, mul_one]

theorem baseChange_compat_apply (f : M →ₗ[R] R) (m : S ⊗[R] M) :
    φ (baseChange R S M f m) = (baseChange R S' M f) ((rTensor M φ.toLinearMap) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul => simp [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
      AlgEquiv.toLinearMap_apply, rid_tmul, map_smul, rTensor_tmul, AlgHom.toLinearMap_apply]
  | add x y hx hy => simp [map_add, hx, hy]

end LinearForm

variable {R}

namespace MvPolynomial

variable {σ M N ι : Type*} [DecidableEq σ] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

open LinearMap TensorProduct

theorem rTensor_lcoeff (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    (LinearMap.rTensor N (lcoeff R k)) sn = 1 ⊗ₜ[R] (scalarRTensor sn) k  := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    simp only [rTensor_tmul, scalarRTensor_apply_tmul, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single k (fun b _ hb ↦ by rw [Finsupp.single_eq_of_ne hb])
      (fun _ ↦ by rw [_root_.zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]),
      Finsupp.single_eq_same, lcoeff_apply, ← smul_tmul, smul_eq_mul, mul_one]
    congr
  | add x y hx hy => simp [LinearMap.map_add, LinearEquiv.map_add, hx, hy,
      Finsupp.add_apply, tmul_add]

theorem scalarRTensor_apply (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    scalarRTensor sn k = TensorProduct.lid R N ((LinearMap.rTensor N (lcoeff R k)) sn) := by
  rw [← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply, rTensor_lcoeff]

end MvPolynomial

open TensorProduct
namespace Submodule

theorem span_tensorProduct_eq_top_of_span_eq_top {σ M S : Type*} [AddCommMonoid M] [Module R M]
    [Semiring S] [Algebra R S] (e : σ → M) (hm : span R (Set.range e) = ⊤) :
    (span S (Set.range fun s ↦ (1 : S) ⊗ₜ[R] e s) : Submodule S (S ⊗[R] M)) = ⊤ := by
  rw [eq_top_iff]
  intro m h
  induction m using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul r m =>
      let f : M →ₗ[R] S ⊗[R] M :=
        { toFun m       := (1 : S) ⊗ₜ[R] m
          map_add' x y  := by simp [tmul_add]
          map_smul' a x := by simp [tmul_smul] }
      suffices r ⊗ₜ[R] m = r • (1 : S) ⊗ₜ[R] m by
        have heq : (Set.range fun s ↦ 1 ⊗ₜ[R] e s) = ⇑f '' Set.range e := by
          conv_rhs => rw [← Set.image_univ, Set.image_image, Set.image_univ]
          simp [f]
        exact this ▸ smul_mem _ r (span_le_restrictScalars R _ _
          (heq ▸ apply_mem_span_image_of_mem_span f (hm ▸ mem_top)))
      rw [smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => exact Submodule.add_mem _ (hx mem_top) (hy mem_top)

end Submodule

end Prerequisites

/- # Polynomial laws. -/

namespace PolynomialLaw

variable {R}

/- **MI** : The file now works assuming the weaker hypotheses `CommSemiring R`, `CommSemiring S`,
  `AddCommMonoid M`, `AddCommMonoid N`. -/

open Finset MvPolynomial TensorProduct

/- ## LocFinsupp. -/
noncomputable section LocFinsupp

open Finsupp Function

variable {M N ι : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] (r : R) {f g : ι → M →ₚₗ[R] N}

variable (f) in
/-- A family `f : ι → M →ₚₗ[R] N` of polynomial maps has locally finite support
  if, for all `S`, `fun i ↦ (f i).toFun' S` has finite support` -/
def LocFinsupp := ∀ (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M),
    (fun i ↦ (f i).toFun' S m).support.Finite

theorem locFinsupp_add (hf : LocFinsupp f) (hg : LocFinsupp g) : LocFinsupp (f + g) :=
  fun S _ _ m ↦ (Set.finite_union.mpr ⟨hf S m, hg S m⟩).subset (support_add _ _)

theorem locFinsupp_zero : LocFinsupp (0 : ι → M →ₚₗ[R] N) := fun S _ _ _ ↦ by
  simp [zero_def, Function.support_zero, Set.finite_empty]

theorem locFinsupp_smul (hf : LocFinsupp f) : LocFinsupp (r • f) :=
  fun S _ _ m ↦ (hf S m).subset (Function.support_smul_subset_right _ _)

variable (f)

lemma locFinsupp_of_fintype [Fintype ι] : LocFinsupp f := fun _ _ _ _ ↦ Set.toFinite _

variable (R M N)
/-- The submodule of families of polynomial maps which have locally finite support  -/
def Submodule.locFinsupp (ι : Type*) : Submodule R (ι → M →ₚₗ[R] N) where
  carrier   := LocFinsupp
  add_mem'  := locFinsupp_add
  zero_mem' := locFinsupp_zero
  smul_mem' := locFinsupp_smul

variable {R M N}

open Classical in
/-- The sum of of a family polynomial maps (0 if not locally finite). -/
noncomputable def lfsum : M →ₚₗ[R] N :=
  if hf : LocFinsupp f then {
    toFun'    := fun S _ _ m ↦ (ofSupportFinite _ (hf S m)).sum fun _ m ↦ m
    isCompat' := fun {S _ _ S' _ _} φ ↦ by
      ext m
      simp only [Function.comp_apply, map_finsuppSum]
      rw [sum]
      suffices hSm : _ ⊆ (hf S m).toFinset by
        rw [sum_of_support_subset _ hSm _ (fun i _ ↦ rfl)]
        exact sum_congr rfl (fun i _ ↦ by simp [ofSupportFinite_coe, isCompat_apply'])
      intro i
      simp only [ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply']
      intro hi
      rw [hi, map_zero] }
  else 0

variable {f}

theorem lfsum_eq_of_locFinsupp (hf : LocFinsupp f) (S : Type u) [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] M) : (lfsum f).toFun' S m = (ofSupportFinite _ (hf S m)).sum fun _ m ↦ m := by
  rw [lfsum, dif_pos hf]

/-- The sum of a locally finite family of polynomial maps, as a linear map -/
noncomputable def lfsumHom :
    Submodule.locFinsupp R M N ι →ₗ[R] M →ₚₗ[R] N where
  toFun fhf := PolynomialLaw.lfsum fhf.val
  map_add'  := fun ⟨f, hf⟩ ⟨g, hg⟩ ↦ by
    classical
    ext S _ _ m
    rw [AddSubmonoid.mk_add_mk, add_def, Pi.add_apply, lfsum_eq_of_locFinsupp hf,
      lfsum_eq_of_locFinsupp hg, lfsum_eq_of_locFinsupp (locFinsupp_add hf hg)]
    simp only [Pi.add_apply, add_def_apply]
    rw [sum_of_support_subset (s := (hf S m).toFinset ∪ (hg S m).toFinset) _ _ _ (fun _ _ ↦ rfl),
      sum_of_support_subset _ subset_union_left _ (fun _ _ ↦ rfl),
      sum_of_support_subset _ subset_union_right _ (fun _ _ ↦ rfl), ← sum_add_distrib]
    · exact sum_congr rfl (fun _ _ ↦ rfl)
    · intro x
      simp only [ofSupportFinite_support, Set.Finite.mem_toFinset,
        Function.mem_support, ne_eq, mem_union, ← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' := fun a ⟨f,hf⟩ ↦ by
    ext S _ _ m
    simp only [SetLike.val_smul, smul_def, RingHom.id_apply, Pi.smul_apply,
      lfsum_eq_of_locFinsupp hf, lfsum_eq_of_locFinsupp (locFinsupp_smul a hf)]
    rw [sum_of_support_subset _ _ _ (fun i _ ↦ rfl)]
    · rw [Finsupp.smul_sum, sum]
      exact sum_congr rfl fun i _ ↦ rfl
    · intro i
      simp only [ofSupportFinite_coe, Finsupp.mem_support_iff, ne_eq, not_imp_not]
      intro hi
      rw [hi, smul_zero]

lemma lfsumHom_apply' {f : ↥(Submodule.locFinsupp R M N ι)} : lfsumHom f = lfsum f.val := rfl

lemma lfsumHom_apply (hf : LocFinsupp f) : lfsumHom ⟨f, hf⟩ = lfsum f := rfl

end LocFinsupp

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {M N ι : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section Fintype

open LinearMap

variable [Fintype ι]

section generize

/-- Given `m : ι → M`, `generize m` is the `R`-linear map sending `f : M →ₚₗ[R] N` to the
term of `MvPolynomial ι R ⊗[R] N` obtained by applying `f.toFun (MvPolynomial ι R)` to the
sum `∑ i, X i ⊗ₜ[R] m i`. -/
noncomputable def generize (m : ι → M) :
    (M →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i)
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

/-- **MI** : do we need these two lemmas? I don't think we are using them. -/
theorem generize_comp_equiv {κ : Type*} [Fintype κ] {e : ι ≃ κ} {m : κ → M} {f : M →ₚₗ[R] N} :
    generize m f =
      (aeval (fun i ↦ X (e i))).toLinearMap.rTensor N (generize (fun x ↦ m (e x)) f) := by
  let hf := f.isCompat_apply (aeval (fun i ↦ X (e i)) : MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (∑ i, X i ⊗ₜ[R] (m (e i)))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf
  simp only [generize, coe_mk, AddHom.coe_mk, hf]
  apply congr_arg
  simp [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

theorem generize_comp_equiv' {κ : Type*} [Fintype κ] {e : ι ≃ κ} {m : κ → M}
    {f : M →ₚₗ[R] N} : (generize (fun x ↦ m (e x)) f) =
      (aeval (fun i ↦ X (e.symm i))).toLinearMap.rTensor N (generize m f) := by
  let hf' := f.isCompat_apply (aeval (fun i ↦ X (e.symm i)) :
    MvPolynomial κ R →ₐ[R] MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i)
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf'
  simp only [generize, coe_mk, AddHom.coe_mk, hf']
  apply congr_arg
  simp [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

end generize

section coeff

variable [DecidableEq ι] (m : ι → M) (k : ι →₀ ℕ) (f : M →ₚₗ[R] N)

/-- The coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def coeff : (M →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (generize m)

theorem generize_eq : generize m f = (coeff m f).sum (fun k n ↦ (monomial k 1) ⊗ₜ n)  := by
  dsimp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize h : scalarRTensor (generize m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h, LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d (fun _ _ hb ↦ by simp [if_neg hb,
    scalarRTensor_apply_tmul_apply]) (by simp), scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul]

theorem coeff_eq :
  coeff m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i))) := by
  rw [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _

/- **MI**: these two lemmas seemed unused as well. -/
theorem coeff_comp_equiv {κ : Type*} [DecidableEq κ] [Fintype κ] (e : ι ≃ κ) (m : κ → M) :
    coeff m f (k.equivMapDomain e) = coeff (m.comp e) f (k) := by
  simp only [coeff, coe_comp, LinearEquiv.coe_coe, MvPolynomial.scalarRTensor_apply, Function.comp]
  let hf := f.isCompat_apply (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
    MvPolynomial ι R →ₐ[R] MvPolynomial κ R) (∑ i, X i ⊗ₜ[R] (m (e i)))
  suffices toFun f (MvPolynomial κ R) (∑ x, MvPolynomial.X (e x) ⊗ₜ[R] m (e x)) = generize m f by
    simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X, this] at hf
    rw [← hf]
    generalize h : generize (fun x ↦ m (e x)) f = g
    simp only [generize, coe_mk, AddHom.coe_mk] at h
    rw [h, EmbeddingLike.apply_eq_iff_eq, ← LinearMap.rTensor_comp_apply, ← h]
    congr
    ext p
    simp only [coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
      _root_.map_one, Finsupp.prod_pow, _root_.one_mul, MvPolynomial.lcoeff_apply]
    suffices ∏ x, MvPolynomial.X (e x) ^ p x =
        MvPolynomial.monomial (Finsupp.equivMapDomain e p) (1 : R) by
      simp only [this, MvPolynomial.coeff_monomial]
      by_cases h : p = k
      . rw [if_pos h, if_pos (by rw [h])]
      . rw [if_neg h, if_neg]
        intro h'; apply h
        ext i
        simpa [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using
          (DFunLike.ext_iff.mp h') (e i)
    . simp [monomial_eq, _root_.map_one, Finsupp.prod_pow, one_mul, prod_congr_equiv e,
        map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]
  . rw [generize, coe_mk, AddHom.coe_mk]
    apply congr_arg
    simp [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

theorem coeff_comp_equiv' {κ : Type*} [DecidableEq κ] [Fintype κ] (e : ι ≃ κ) (m : κ → M)
    (k : κ →₀ ℕ) : coeff m f k = coeff (m ∘ e) f (k.equivMapDomain e.symm) := by
  rw [coeff_comp_equiv]
  congr
  ext k
  simp [Function.comp_apply, Equiv.apply_symm_apply]

theorem toFun_sum_tmul_eq_coeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) :
    f.toFun S (∑ i, r i ⊗ₜ[R] m i) = (coeff m f).sum (fun k n ↦ (∏ i, r i ^ k i) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval r)) (∑ i, X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at this
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul]

end coeff

end Fintype

open Function

/-- Variant of `toFun_sum_tmul_eq_coeff_sum` over a Finset -/
theorem toFun_sum_tmul_eq_coeff_finset_sum [DecidableEq ι] (m : ι → M) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) (s : Finset ι) :
    f.toFun S (∑ i ∈ s, r i ⊗ₜ[R] m i) = (coeff (fun i : s ↦ m i) f).sum
      (fun k n ↦ (∏ i ∈ s, r i ^ ((Function.extend (fun x ↦ x.val) k (const ι 0)) i)) ⊗ₜ[R] n) := by
  convert toFun_sum_tmul_eq_coeff_sum (fun (i : s) ↦ m i) f S fun (i : s) ↦ r i
  · rw [univ_eq_attach, ← sum_attach]
  · rw [univ_eq_attach, ← prod_attach]
    exact prod_congr rfl (fun _ _ ↦ congr_arg₂ _ rfl (Subtype.coe_injective.extend_apply _ _ _))

-- Useful ?
/-- Variant of `toFun_sum_tmul_eq_coeff_sum` with a `Finsupp`-/
theorem toFun_sum_tmul_eq_coeff_finsupp_sum [DecidableEq ι] (m : ι → M) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι →₀ S) :
    f.toFun S (r.sum fun i a ↦ a ⊗ₜ[R] m i) = (coeff (fun i : r.support ↦ m i) f).sum
      (fun k n ↦ (∏ i ∈ r.support,
        (r i ^ ((Function.extend (fun x ↦ x.val) k (const ι 0)) i))) ⊗ₜ[R] n) := by
  rw [Finsupp.sum, toFun_sum_tmul_eq_coeff_finset_sum]

section Fintype

variable [Fintype ι]

section Decidable_Fintype

variable [DecidableEq ι] (f : M →ₚₗ[R] N) (m : ι → M) (r : ι → R) (r₁ r₂ : R) (m₁ m₂ : M)

theorem ground_apply_sum_smul :
    ground f (∑ i, (r i) • (m i)) = (coeff m f).sum (fun k n ↦ (∏ i,  r i ^ k i) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_sum, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ ↦ by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])

theorem ground_apply_smul :
    ground f (r₁ • m₁) = (coeff (const Unit m₁) f).sum (fun k n ↦ r₁ ^ (k 0) • n) := by
  suffices r₁ • m₁ = ∑ i, (const Unit r₁) i • (const Unit m₁ i) by
    rw [this, ground_apply_sum_smul]
    exact sum_congr rfl (fun i _ ↦ by simp)
  simp

theorem ground_apply_add_smul : ground f (r₁ • m₁ + r₂ • m₂) =
      (coeff (R := R) (![m₁, m₂]) f).sum fun k n ↦ (∏ i, (![r₁, r₂]) i ^ (k i)) • n := by
  suffices r₁ • m₁ + r₂ • m₂ = ∑ i, (![r₁, r₂]) i • (![m₁, m₂]) i  by
    rw [this, ground_apply_sum_smul]
  simp [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]

variable {S : Type*} [CommSemiring S] [Algebra R S]

theorem coeff_injective {m : ι → M} (hm : Submodule.span R (Set.range m) = ⊤) :
    Function.Injective (coeff m : (M →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N) := fun f g h ↦ by
  ext S _ _ p
  suffices hp : p ∈ Submodule.span S (Set.range fun s ↦ 1 ⊗ₜ[R] m s) by
    simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
    obtain ⟨r, rfl⟩ := hp
    rw [Finsupp.sum_of_support_subset _ (subset_univ _) _ (fun  i _ ↦ by
      rw [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul])]
    simp [smul_eq_mul, mul_one, ← toFun_eq_toFun'_apply, toFun_sum_tmul_eq_coeff_sum, h]
  simp [Submodule.span_tensorProduct_eq_top_of_span_eq_top m hm]

theorem coeff_inj {m : ι → M} (hm : Submodule.span R (Set.range m) = ⊤)
    {f g : M →ₚₗ[R] N} : coeff m f = coeff m g ↔ f = g := (coeff_injective hm).eq_iff

end Decidable_Fintype

end Fintype

end Coefficients

end PolynomialLaw


namespace Finsupp

open Finset MvPolynomial PolynomialLaw TensorProduct

variable {R} {M N ι : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (S : Type*) [CommSemiring S] [Algebra R S]

/- When M is free, we can go in the other direction and construct,
  from a basis `b` of `M` and `N`-valued polynomials, a polynomial law. -/
variable (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) (m : S ⊗[R] M)

section Fintype

variable [Fintype ι]

-- BP
/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ`, `Finsupp.polynomialLaw b h : M →ₚₗ[R] N` is
the polynomial map whose coefficients at `b` are given by `h`. -/
noncomputable def polynomialLaw : M →ₚₗ[R] N where
  toFun' S _ _ x := h.sum fun k n ↦ (∏ i, (LinearForm.baseChange R S _ (b.coord i)) x ^ k i) ⊗ₜ[R] n
  isCompat' φ   := by
    ext m
    rw [Function.comp_apply, sum, _root_.map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    apply congr_arg₂ _ _ rfl
    rw [map_prod φ]
    apply Finset.prod_congr rfl (fun _ _ ↦ ?_)
    rw [map_pow]
    exact congr_arg₂ _ (by rw [LinearForm.baseChange_compat_apply]) rfl

theorem polynomialLaw_toFun_apply : (polynomialLaw b h).toFun S m =
    h.sum fun k n ↦ (∏ i, (LinearForm.baseChange R S _ (b.coord i)) m ^ k i) ⊗ₜ[R] n := by
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  simp only [← isCompat_apply, toFun_eq_toFun', polynomialLaw, map_finsuppSum]
  apply sum_congr
  intro k _
  rw [LinearMap.rTensor_tmul]
  congr
  simp only [AlgHom.toLinearMap_apply, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro i _
  apply congr_arg₂ _ _ rfl
  rw [LinearForm.baseChange_compat_apply]

open LinearMap

theorem generize_polynomialLaw_eq_sum :
    ((generize ⇑b) (polynomialLaw b h)) = sum h (fun k n ↦ (monomial k 1) ⊗ₜ[R] n) := by
  classical
  set m := ∑ i, (X i : MvPolynomial ι R) ⊗ₜ[R] b i with hm
  rw [generize, LinearMap.coe_mk, AddHom.coe_mk, polynomialLaw_toFun_apply]
  have : ∀ i, (LinearForm.baseChange R (MvPolynomial ι R) M (Basis.coord b i)) m = X i := fun i ↦ by
    rw [hm, map_sum, Finset.sum_eq_single i, LinearForm.baseChange_apply_tmul, Basis.coord_apply,
      Basis.repr_self, single_eq_same, _root_.one_smul, mul_one]
    · intro j _ hj
      rw [LinearForm.baseChange_apply_tmul, Basis.coord_apply, Basis.repr_self,
        Algebra.mul_smul_comm, mul_one, single_smul, one_smul, single_eq_of_ne hj]
    · simp
  simp only [← hm, this]
  apply sum_congr (fun k _ ↦ ?_)
  congr
  rw [← MvPolynomial.prod_X_pow_eq_monomial, ← prod_mul_prod_compl k.support]
  convert mul_one _
  apply prod_eq_one
  intro i hi
  rw [mem_compl, mem_support_iff, ne_eq, not_not] at hi
  rw [hi, pow_zero]

/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ,
  `Finsupp.polynomialLaw b h : M →ₚₗ[R] N` is the polynomial map
  whose coefficients at `b` are given by `h` -/
theorem coeff_polynomialLaw [DecidableEq ι] :
    coeff (DFunLike.coe b) (polynomialLaw b h) = h := by
  simp only [PolynomialLaw.coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  ext d
  rw [scalarRTensor_apply, eq_comm, ← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply,
    generize_polynomialLaw_eq_sum, map_finsuppSum, sum_eq_single d
    (fun b _ hb ↦ by rw [rTensor_tmul, lcoeff_apply, coeff_monomial, if_neg hb, zero_tmul])
    (fun _ ↦ by rw [tmul_zero, map_zero]), rTensor_tmul, lcoeff_apply, coeff_monomial, if_pos rfl]

theorem polynomialLaw_of_coeff [DecidableEq ι] (f : M →ₚₗ[R] N) :
    polynomialLaw b (coeff (DFunLike.coe b) f) = f :=
  (coeff_inj (eq_top_iff.mpr (fun m _ ↦ Submodule.span_mono
    (Set.image_subset_range _ _) (Basis.mem_span_repr_support b m)))).mp (coeff_polynomialLaw _ _)

noncomputable def polynomialLawEquivCoeff : ((ι →₀ ℕ) →₀ N) ≃ₗ[R] (M →ₚₗ[R] N) where
  toFun h      := polynomialLaw b h
  map_add' h k := by
    classical
    ext S _ _ m
    simp only [← toFun_eq_toFun', add_toFun, polynomialLaw_toFun_apply, Pi.add_apply]
    rw [sum_of_support_subset h (h.support.subset_union_left), sum_of_support_subset k
      (h.support.subset_union_right), sum_of_support_subset (h + k) support_add]
    simp_rw [coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [sum_add_distrib]
    all_goals intro i _hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    ext S _ _ m
    simp only [← toFun_eq_toFun', RingHom.id_apply, smul_toFun, Pi.smul_apply,
      polynomialLaw_toFun_apply]
    rw [sum_of_support_subset (a • h) support_smul _ (fun k _ ↦ by rw [TensorProduct.tmul_zero]),
      sum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [coe_smul, Pi.smul_apply, tmul_smul])
  invFun f    := by classical exact coeff (DFunLike.coe b) f
  left_inv h  := by dsimp; rw [coeff_polynomialLaw]
  right_inv f := by classical dsimp; rw [polynomialLaw_of_coeff b]

end Fintype

end Finsupp
