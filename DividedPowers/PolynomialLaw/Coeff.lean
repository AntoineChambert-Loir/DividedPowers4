import DividedPowers.ForMathlib.RingTheory.SubmoduleMem
import DividedPowers.ForMathlib.RingTheory.TensorProduct.MvPolynomial
import DividedPowers.PolynomialLaw.Basic2
import Mathlib.LinearAlgebra.Basis.Basic

universe u v w uM uN uι

section Finset

open Equiv Finsupp Function Set

@[to_additive]
theorem Finset.prod_congr_equiv {α β M : Type*} [CommMonoid M] {f : α → M} {s : Finset α}
    (e : α ≃ β) : s.prod f = (s.map e).prod (f ∘ e.symm)  := by
  simp only [comp_apply, prod_map, coe_toEmbedding, symm_apply_apply]

-- Useful ?
@[to_additive]
theorem Finset.prod_congr_equiv' {α β M : Type*} [CommMonoid M] {f : β → M} {s : Finset α}
    (e : α ≃ β) : s.prod (f ∘ e) = (s.map e).prod f := by
  simp only [comp_apply, prod_map, coe_toEmbedding]

theorem Finsupp.ofSupportFinite_support {ι α : Type*} [Zero α] {f : ι → α} (hf : f.support.Finite) :
    (ofSupportFinite f hf).support = hf.toFinset := by
  ext
  simp only [ofSupportFinite_coe, mem_support_iff, Finite.mem_toFinset, mem_support]

end Finset

section Algebra

open Algebra Algebra.TensorProduct Function LinearMap

open scoped TensorProduct

variable (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]

/-- The natural `R`-algebra map from `S ⊗[R] R` to `S`.-/
noncomputable def Algebra.TensorProduct.rid' : S ⊗[R] R →ₐ[S] S := TensorProduct.rid R S S

@[simp]
theorem Algebra.TensorProduct.rid'_tmul (r : R) (s : S) : (rid' R S) (s ⊗ₜ[R] r) = r • s := rfl

variable (M : Type*) [AddCommMonoid M] [Module R M]

namespace LinearForm

noncomputable def baseChange (f : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (rid' R S).toLinearMap.comp (f.baseChange S)

theorem baseChange_apply_tmul (f : M →ₗ[R] R) (r : S) (m : M) :
    baseChange R S M f (r ⊗ₜ[R] m) = r * ((f m) • (1 : S)) := by
  simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul, AlgHom.toLinearMap_apply,
    rid'_tmul, mul_smul_comm, _root_.mul_one]

variable (S' : Type*) [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S')

theorem baseChange_compat_apply (f : M →ₗ[R] R) (m : S ⊗[R] M) :
    φ (baseChange R S M f m) = (baseChange R S' M f) ((rTensor M φ.toLinearMap) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul => simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
      AlgHom.toLinearMap_apply, rid'_tmul, map_smul, rTensor_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end LinearForm

end Algebra
namespace PolynomialLaw

open Finset MvPolynomial TensorProduct

noncomputable section LocFinsupp

open Finsupp Function

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/- **MI** : Now the file works with `[CommSemiring R]` and `[CommSemiring S]`. -/

/-- A family `f : ι → M →ₚₗ[R] N` of polynomial maps has locally finite support
  if, for all `S`, `fun i ↦ (f i).toFun' S` has finite support` -/
def LocFinsupp {ι : Type*} (f : ι → PolynomialLaw R M N) :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M),
    (fun i => (f i).toFun' S m).support.Finite

theorem LocFinsupp_add {ι : Type*} {f g : ι → M →ₚₗ[R] N} (hf : LocFinsupp f) (hg : LocFinsupp g) :
    LocFinsupp (f + g) := fun S _ _ m ↦
  Set.Finite.subset (Set.finite_union.mpr ⟨hf S m, hg S m⟩) (support_add _ _)

theorem LocFinsupp_zero {ι : Type*} : LocFinsupp (0 : ι → M →ₚₗ[R] N) := fun S _ _ _ ↦ by
  simp only [Pi.zero_apply, zero_def, Function.support_zero, Set.finite_empty]

theorem LocFinsupp_smul {ι : Type*} (r : R) {f : ι → M →ₚₗ[R] N} (hf : LocFinsupp f) :
    LocFinsupp (r • f) := fun S _ _ m ↦
  Set.Finite.subset (hf S m) (Function.support_smul_subset_right _ _)

-- We should probably use finite instead
lemma locFinsupp_of_fintype {ι : Type*} [Fintype ι] (f : ι → M →ₚₗ[R] N) : LocFinsupp f := by
  simp only [LocFinsupp]; intros; exact Set.toFinite _

variable (R M N)
/-- The submodule of families of polynomial maps which have locally finite support  -/
def Submodule.locFinsupp (ι : Type*) : Submodule R (ι → PolynomialLaw R M N) where
  carrier   := LocFinsupp
  add_mem'  := LocFinsupp_add
  zero_mem' := LocFinsupp_zero
  smul_mem' := LocFinsupp_smul

variable {R M N}

open Classical in
/-- The sum of of a family polynomial maps (0 if not locally finite) -/
noncomputable def lfsum {ι : Type*} (f : ι → PolynomialLaw R M N) : PolynomialLaw R M N :=
  if hf : LocFinsupp f then {
    toFun'    := fun S _ _ m ↦ (ofSupportFinite _ (hf S m)).sum fun _ m => m
    isCompat' := fun {S _ _ S' _ _} φ ↦ by
      ext m
      simp only [Function.comp_apply, map_finsuppSum]
      rw [sum]
      suffices hSm : _ ⊆ (hf S m).toFinset by
        rw [sum_of_support_subset _ hSm _ (fun i _ ↦ rfl)]
        apply sum_congr rfl (fun i _ ↦ by
          simp only [ofSupportFinite_coe, _root_.map_sum, isCompat_apply'])
      intro i
      simp only [ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply']
      intro hi
      rw [hi, map_zero] }
  else 0

theorem lfsum_eq {ι : Type*} {f : ι → PolynomialLaw R M N} (hf : LocFinsupp f) (S : Type _)
    [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (lfsum f).toFun' S m = (ofSupportFinite _ (hf S m)).sum fun _ m => m := by
  rw [lfsum, dif_pos hf]

/-- The sum of a locally finite family of polynomial maps, as a linear map -/
noncomputable def lLfsum {ι : Type*} [DecidableEq ι] :
    Submodule.locFinsupp R M N ι →ₗ[R] PolynomialLaw R M N where
  toFun fhf := PolynomialLaw.lfsum fhf.val
  map_add'  := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext S _ _ m
    rw [AddSubmonoid.mk_add_mk, add_def, Pi.add_apply, lfsum_eq hf, lfsum_eq hg,
      lfsum_eq (LocFinsupp_add hf hg)]
    simp only [Pi.add_apply, add_def_apply]
    rw [sum_of_support_subset (s := (hf S m).toFinset ∪ (hg S m).toFinset),
      sum_of_support_subset _ subset_union_left,
      sum_of_support_subset _ subset_union_right, ← sum_add_distrib]
    apply sum_congr rfl
    all_goals try intro i _hi; rfl
    · intro x
      simp only [ofSupportFinite_support, Set.Finite.mem_toFinset,
        Function.mem_support, ne_eq, mem_union, ← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' := fun a ⟨f,hf⟩ ↦ by
    ext S _ _ m
    dsimp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, AddSubmonoid.mk_add_mk, add_def,
      add_def_apply, id_eq, Pi.add_apply, ne_eq, eq_mpr_eq_cast, cast_eq, AddHom.toFun_eq_coe,
      AddHom.coe_mk, SetLike.val_smul, smul_def, RingHom.id_apply, Pi.smul_apply]
    rw [lfsum_eq hf, lfsum_eq (LocFinsupp_smul a hf)]
    simp only [Pi.smul_apply, smul_def_apply]
    rw [sum_of_support_subset _ _ _ (fun i _ => rfl)]
    · rw [Finsupp.smul_sum, sum]
      exact sum_congr rfl fun i _ => rfl
    · intro i
      simp only [ofSupportFinite_coe, SetLike.val_smul, Pi.smul_apply, smul_def,
        Finsupp.mem_support_iff, ne_eq, not_imp_not, PolynomialLaw.smul_def]
      intro hi
      rw [hi, smul_zero]

lemma lLfsum_apply' {ι : Type*} [DecidableEq ι] {f : ↥(Submodule.locFinsupp R M N ι)} :
    lLfsum f = lfsum f.val := rfl

lemma lLfsum_apply {ι : Type*} [DecidableEq ι] {f : ι → PolynomialLaw R M N}
  (hf : LocFinsupp f) : lLfsum ⟨f, hf⟩ = lfsum f := rfl

end LocFinsupp

section Coefficients

variable {R : Type u} [CommSemiring R] {M : Type uM} [AddCommGroup M] [Module R M]
  {N : Type uN} [AddCommGroup N] [Module R N]

--variable {ι : Type uι} /- [DecidableEq ι]   -/
variable {ι : Type*}
section Fintype

variable [Fintype ι]

noncomputable def generize (m : ι → M) :
    PolynomialLaw R M N →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (univ.sum fun i => X i ⊗ₜ[R] m i)
  map_add' p q  := by simp only [add_toFun_apply]
  map_smul' r p := by simp only [RingHom.id_apply, smul_toFun, Pi.smul_apply]

open LinearMap

theorem generize_comp_equiv {κ : Type*} [Fintype κ] {e : ι ≃ κ} {m : κ → M}
    {f : PolynomialLaw R M N} : generize m f =
      (aeval (fun i ↦ X (e i))).toLinearMap.rTensor N (generize (fun x ↦ m (e x)) f) := by
  let hf := f.isCompat_apply (aeval (fun i ↦ X (e i)) : MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (univ.sum (fun i ↦ X i ⊗ₜ[R] (m (e i))))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf
  simp only [generize, coe_mk, AddHom.coe_mk, comp_apply, hf]
  apply congr_arg
  simp only [sum_congr_equiv e, map_univ_equiv]
  exact sum_congr rfl (fun k _ => by rw [Function.comp_apply, Equiv.apply_symm_apply])

theorem generize_comp_equiv' {κ : Type*} [Fintype κ] {e : ι ≃ κ} {m : κ → M}
    {f : PolynomialLaw R M N} : (generize (fun x ↦ m (e x)) f) =
      (aeval (fun i ↦ X (e.symm i))).toLinearMap.rTensor N (generize m f) := by
  let hf' := f.isCompat_apply (aeval (fun i ↦ X (e.symm i)) :
    MvPolynomial κ R →ₐ[R] MvPolynomial ι R) (univ.sum (fun i ↦ X i ⊗ₜ[R] (m i)))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf'
  simp only [generize, coe_mk, AddHom.coe_mk, hf']
  apply congr_arg
  simp only [sum_congr_equiv e, map_univ_equiv]
  exact sum_congr rfl (fun k _ => by rw [Function.comp_apply, Equiv.apply_symm_apply])

/-
theorem generize_comp_embed (f : PolynomialLaw R M N)
    {ι : Type u} {κ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι][DecidableEq κ]
    (e : ι ↪ κ) (m : κ → M) :
  (rTensor N
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i))).toLinearMap)
      (generize A N (fun i ↦ m (e i)) f) =
   rTensor N (MvPolynomial.aeval (R := A)
    (fun k ↦ if k ∈ Finset.univ.map e then MvPolynomial.X k else (0 : MvPolynomial κ A))).toLinearMap
      (generize A N m f) := by
  let hf := f.isCompat_apply
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
        MvPolynomial ι A →ₐ[A] MvPolynomial κ A)
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[A] (m (e i))))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf
  simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [Function.comp_apply, hf]

  let hf' := f.isCompat_apply (MvPolynomial.aeval (R := A)
    (fun k ↦ if k ∈ Finset.univ.map e then MvPolynomial.X k else (0 : MvPolynomial κ A)))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf'
  rw [hf', _root_.map_sum]
  simp only [Set.mem_range, rTensor_tmul, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X]
  apply congr_arg
  rw [← Finset.sum_map (Finset.univ : Finset ι) e
    (fun k ↦ (MvPolynomial.X k : MvPolynomial κ A) ⊗ₜ[A] m k)]
  simp_rw [TensorProduct.ite_tmul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  . ext k
    simp only [Finset.mem_map, Finset.mem_univ, true_and, forall_true_left,
      Finset.univ_filter_exists, Finset.mem_image]
-/

/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff [DecidableEq ι] (m : ι → M) : PolynomialLaw R M N →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (generize m)

theorem generize_eq [DecidableEq ι] (m : ι → M) (f : PolynomialLaw R M N)  :
    generize m f = (coeff m f).sum (fun k n => (monomial k 1) ⊗ₜ n)  := by
  dsimp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize h : scalarRTensor (generize m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h, LinearEquiv.symm_apply_eq, map_finsuppSum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d, scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul]
  · intro b _ hb
    rw [scalarRTensor_apply_tmul_apply, coeff_monomial, if_neg hb, _root_.zero_smul]
  · simp only [tmul_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, implies_true]

theorem _root_.MvPolynomial.rTensor_lcoeff {σ : Type*} [DecidableEq σ]
    (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    (LinearMap.rTensor N (lcoeff R k)) sn = 1 ⊗ₜ[R] (scalarRTensor sn) k  := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    simp only [rTensor_tmul, scalarRTensor_apply_tmul, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single k (fun b _ hb => by rw [Finsupp.single_eq_of_ne hb])
      (fun _ => by rw [_root_.zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]),
      Finsupp.single_eq_same, lcoeff_apply, ← smul_tmul, smul_eq_mul, mul_one]
    congr
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy,
      Finsupp.add_apply, tmul_add]

theorem _root_.MvPolynomial.scalarRTensor_apply {σ : Type*} [DecidableEq σ]
    (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    scalarRTensor sn k = TensorProduct.lid R N ((LinearMap.rTensor N (lcoeff R k)) sn) := by
  rw [← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply, rTensor_lcoeff]

theorem coeff_eq [DecidableEq ι] (m : ι → M) (k : ι →₀ ℕ) (f : PolynomialLaw R M N) :
  coeff m f k = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R k))
      (f.toFun (MvPolynomial ι R) (univ.sum fun i : ι => MvPolynomial.X i ⊗ₜ[R] m i))) := by
  rw [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ]
  exact scalarRTensor_apply _ _


-- Unsolved goals (?)
theorem coeff_comp_equiv [DecidableEq ι] {κ : Type*} [DecidableEq κ]
    [Fintype κ] (e : ι ≃ κ) (m : κ → M) (k : ι →₀ ℕ) (f : PolynomialLaw R M N) :
    coeff m f (k.equivMapDomain e) = coeff (m.comp e) f (k) := by
  simp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    MvPolynomial.scalarRTensor_apply, Function.comp]
  let hf := f.isCompat_apply (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
    MvPolynomial ι R →ₐ[R] MvPolynomial κ R) (univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[R] (m (e i))))
  suffices toFun f (MvPolynomial κ R)
    (Finset.sum univ (fun x ↦ MvPolynomial.X (e x) ⊗ₜ[R] m (e x))) = generize m f by
    simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_X, this] at hf
    rw [← hf]
    generalize h : generize (fun x ↦ m (e x)) f = g
    simp only [generize, coe_mk, AddHom.coe_mk] at h
    rw [h, EmbeddingLike.apply_eq_iff_eq, ← LinearMap.rTensor_comp_apply, ← h]
    congr
    ext p
    simp only [coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial,
      _root_.map_one, Finsupp.prod_pow, _root_.one_mul, MvPolynomial.lcoeff_apply]
    suffices Finset.prod univ (fun x ↦ MvPolynomial.X (e x) ^ p x) =
        MvPolynomial.monomial (Finsupp.equivMapDomain e p) (1 : R) by
      simp only [this, MvPolynomial.coeff_monomial]
      by_cases h : p = k
      . rw [if_pos h, if_pos (by rw [h])]
      . rw [if_neg h, if_neg]
        intro h'; apply h
        simp only [DFunLike.ext_iff] at h'
        ext i
        simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using h' (e i)
    . simp only [monomial_eq, _root_.map_one, Finsupp.prod_pow, Finsupp.equivMapDomain_apply,
        _root_.one_mul, prod_congr_equiv e, map_univ_equiv, Function.comp_apply,
         Equiv.apply_symm_apply]
  . rw [generize, coe_mk, AddHom.coe_mk]
    apply congr_arg
    simp only [sum_congr_equiv e, map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

theorem coeff_comp_equiv' [DecidableEq ι] {κ : Type*} [DecidableEq κ] [Fintype κ] (e : ι ≃ κ)
    (m : κ → M) (k : κ →₀ ℕ) (f : PolynomialLaw R M N) :
    coeff m f k = coeff (m ∘ e) f (k.equivMapDomain e.symm) := by
  rw [coeff_comp_equiv]
  congr
  ext k
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem image_eq_coeff_sum [DecidableEq ι] (m : ι → M) (f : PolynomialLaw R M N) (S : Type*)
    [CommSemiring S] [Algebra R S] (r : ι → S) : f.toFun S (univ.sum fun i => r i ⊗ₜ[R] m i) =
      (coeff m f).sum (fun k n => (univ.prod fun i => r i ^ k i) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval r))
    (univ.sum fun i => MvPolynomial.X i ⊗ₜ[R] m i)
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

end Fintype

open Function

/-- Variant of `image_eq_coeff_sum` over a Finset -/
theorem image_eq_coeff_finset_sum [DecidableEq ι] (m : ι → M) (f : PolynomialLaw R M N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S) (s : Finset ι) :
    f.toFun S (s.sum fun i => r i ⊗ₜ[R] m i) = (coeff (fun i : s => m i) f).sum
      (fun k n => (s.prod fun i =>
        r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i)) ⊗ₜ[R] n) := by
  let m' : s → M := fun i => m i
  let r' : s → S := fun i => r i
  convert image_eq_coeff_sum m' f S r'
  · simp only [univ_eq_attach, Finsupp.coe_mk]
    rw [← sum_attach]
  · simp only [univ_eq_attach, Finsupp.coe_mk]
    rw [← prod_attach]
    apply prod_congr rfl
    intro x _
    simp only [const_zero, exists_apply_eq_apply, not_true]
    apply congr_arg₂ _ rfl
    rw [Subtype.coe_injective.extend_apply]

-- Useful ?
/-- Variant of `image_eq_coeff_sum'` with a `Finsupp`-/
theorem image_eq_coeff_sum' [DecidableEq ι] (m : ι → M) (f : PolynomialLaw R M N)
    (S : Type*) [CommSemiring S] [Algebra R S] (r : ι →₀ S) :
    f.toFun S (r.sum fun i a => a ⊗ₜ[R] m i) = (coeff (fun i : r.support => m i) f).sum
      (fun k n => (r.support.prod
        (fun i => r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i)) ⊗ₜ[R] n)) := by
  rw [Finsupp.sum, image_eq_coeff_finset_sum]

section Fintype

variable [Fintype ι]

section Decidable_Fintype

variable [DecidableEq ι]

theorem ground_image_eq_coeff_sum (m : ι → M) (f : PolynomialLaw R M N) (r : ι → R) :
    ground f (univ.sum fun i => (r i) • (m i)) =
      (coeff m f).sum (fun k n => (univ.prod fun i => r i ^ k i) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_sum, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', image_eq_coeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ => by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])

theorem ground_image_eq_coeff_sum_one (m : M) (f : PolynomialLaw R M N) (r : R) :
    ground f (r • m) = (coeff (const Unit m) f).sum (fun k n => r ^ (k 0) • n) := by
  suffices r • m = univ.sum fun i ↦ (const Unit r) i • (const Unit m i) by
    rw [this, ground_image_eq_coeff_sum]
    exact sum_congr rfl (fun i _ => by simp only [univ_unique, const_apply, prod_singleton])
  simp only [univ_unique, const_apply, sum_const, card_singleton, _root_.one_smul]

theorem ground_image_eq_coeff_sum_two (r₁ r₂ : R) (m₁ m₂ : M) (f : PolynomialLaw R M N) :
    ground f (r₁ • m₁ + r₂ • m₂) =
      (coeff (R := R) (![m₁, m₂]) f).sum fun k n =>
        (univ.prod (fun i => (![r₁, r₂]) i ^ (k i)) • n) := by
  suffices r₁ • m₁ + r₂ • m₂ = univ.sum fun i ↦ (![r₁, r₂]) i • (![m₁, m₂]) i  by
    rw [this, ground_image_eq_coeff_sum]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

variable {S : Type v} [CommSemiring S] [Algebra R S]

theorem span_tensorProduct_eq_top_of_span_eq_top (σ : Type*) (e : σ → M)
    (hm : Submodule.span R (Set.range e) = ⊤) :
    (Submodule.span S (Set.range fun s => (1 : S) ⊗ₜ[R] e s) : Submodule S (S ⊗[R] M)) = ⊤ := by
  rw [_root_.eq_top_iff]
  intro m h
  induction m using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul r m =>
      let f : M →ₗ[R] S ⊗[R] M :=
        { toFun     := fun m => (1 : S) ⊗ₜ[R] m
          map_add'  := fun x y => by simp only [TensorProduct.tmul_add]
          map_smul' := fun a x => by simp only [TensorProduct.tmul_smul, RingHom.id_apply] }
      suffices r ⊗ₜ[R] m = r • (1 : S) ⊗ₜ[R] m by
        rw [this]
        apply Submodule.smul_mem _ r _
        apply Submodule.span_le_restrictScalars R
        convert Submodule.apply_mem_span_image_of_mem_span (s := Set.range e) f _
        . conv_rhs => rw [← Set.image_univ, Set.image_image, Set.image_univ]
          rfl
        . rw [hm]; exact Submodule.mem_top
      rw [TensorProduct.smul_tmul']; simp only [Algebra.id.smul_eq_mul, _root_.mul_one]
  | add x y hx hy => exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)

end Decidable_Fintype

theorem coeff_injective [DecidableEq ι] (m : ι → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (f g : PolynomialLaw R M N) (h : coeff m f = coeff m g) : f = g := by
  ext S _ _ p
  suffices hp : p ∈ Submodule.span S (Set.range fun s => 1 ⊗ₜ[R] m s) by
    simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
    obtain ⟨r, rfl⟩ := hp
    rw [Finsupp.sum_of_support_subset _ (subset_univ _) _ (fun  i _ => by
      rw [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul])]
    simp [smul_eq_mul, mul_one, ← toFun_eq_toFun'_apply,image_eq_coeff_sum, h]
  rw [PolynomialLaw.span_tensorProduct_eq_top_of_span_eq_top ι m hm]
  exact Submodule.mem_top

/- When M is free, we can go in the other direction and construct,
  from a basis `b` of `M` and `N`-valued polynomials, a polynomial map -/
variable (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N)

namespace Finsupp

-- BP
noncomputable def polynomialMap_toFun (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] M) :
    S ⊗[R] N :=
  h.sum fun k n => (univ.prod fun i => (LinearForm.baseChange R S _ (b.coord i)) x ^ k i) ⊗ₜ[R] n

-- I think this is not used?
/- noncomputable def polynomialMap_toFun' (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] M) :
    S ⊗[R] N :=
  h.sum fun k n => (k.prod fun i m => (LinearForm.baseChange R S _ (b.coord i)) x ^ m) ⊗ₜ[R] n -/

-- BP
theorem polynomialMap_isCompat {S : Type*} [CommSemiring S] [Algebra R S] {S' : Type*}
    [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ (Finsupp.polynomialMap_toFun b h S) =
      Finsupp.polynomialMap_toFun b h S' ∘ (φ.toLinearMap.rTensor M) := by
  ext m
  rw [Function.comp_apply, polynomialMap_toFun, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  rw [map_prod φ]
  apply prod_congr rfl
  intro i _
  rw [map_pow]
  apply congr_arg₂ _ _ rfl
  rw [LinearForm.baseChange_compat_apply]

-- BP
/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ,
  `Finsupp.polynomialMap b h : M →ₚₗ[R] N` is the polynomial map
  whose coefficients at `b` are given by `h` -/
noncomputable def polynomialMap (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
    PolynomialLaw R M N where
  toFun' S _ _:= polynomialMap_toFun b h S
  isCompat' φ   := polynomialMap_isCompat b h φ

variable (S : Type*) [CommSemiring S] [Algebra R S]

theorem polynomialMap_toFun_apply (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) (m : S ⊗[R] M) :
    (Finsupp.polynomialMap b h).toFun S m = h.sum fun k n =>
      (univ.prod (fun i => (LinearForm.baseChange R S _ (b.coord i)) m ^ k i)) ⊗ₜ[R] n := by
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  simp only [← isCompat_apply, toFun_eq_toFun', polynomialMap, polynomialMap_toFun, map_finsuppSum]
  apply Finsupp.sum_congr
  intro k _
  rw [LinearMap.rTensor_tmul]
  congr
  simp only [AlgHom.toLinearMap_apply, map_prod, map_pow]
  apply prod_congr rfl
  intro i _
  apply congr_arg₂ _ _ rfl
  rw [LinearForm.baseChange_compat_apply]

end Finsupp

open LinearMap

theorem generize_finsupp_eq [DecidableEq ι] (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
    ((generize ⇑b) (Finsupp.polynomialMap b h)) =
      Finsupp.sum h (fun k n ↦ (monomial k 1) ⊗ₜ[R] n) := by
  set m := Finset.sum univ (fun i => (X i : MvPolynomial ι R) ⊗ₜ[R] b i) with hm
  rw [generize, coe_mk, AddHom.coe_mk, Finsupp.polynomialMap_toFun_apply]
  have : ∀ i, (LinearForm.baseChange R (MvPolynomial ι R) M (Basis.coord b i)) m = X i := fun i ↦ by
    rw [hm, map_sum, sum_eq_single i, LinearForm.baseChange_apply_tmul, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_eq_same, _root_.one_smul, mul_one]
    · intro j _ hj
      rw [LinearForm.baseChange_apply_tmul, Basis.coord_apply,
        Basis.repr_self, Algebra.mul_smul_comm, mul_one, Finsupp.single_smul,
        _root_.one_smul, Finsupp.single_eq_of_ne hj]
    · simp only [mem_univ, not_true_eq_false, false_implies]
  simp only [← hm, this]
  apply Finsupp.sum_congr
  intro k _
  congr
  rw [← MvPolynomial.prod_X_pow_eq_monomial, ← prod_mul_prod_compl k.support]
  convert mul_one _
  apply prod_eq_one
  intro i hi
  rw [mem_compl, Finsupp.mem_support_iff, ne_eq, not_not] at hi
  rw [hi, pow_zero]

/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ,
  `Finsupp.polynomialMap b h : M →ₚₗ[R] N` is the polynomial map
  whose coefficients at `b` are given by `h` -/
theorem coeff_of_finsupp_polynomialMap [DecidableEq ι]
    (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
    coeff (DFunLike.coe b) (Finsupp.polynomialMap b h) = h := by
  simp only [coeff, coe_mk, AddHom.coe_mk, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  ext d
  rw [scalarRTensor_apply, eq_comm, ← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply,
    generize_finsupp_eq, map_finsuppSum, Finsupp.sum_eq_single d
    (fun b _ hb => by rw [rTensor_tmul, lcoeff_apply, coeff_monomial, if_neg hb, zero_tmul])
    (fun _ => by rw [tmul_zero, map_zero]), rTensor_tmul, lcoeff_apply, coeff_monomial, if_pos rfl]

theorem finsupp_polynomialMap_of_coeff [DecidableEq ι] (b : Basis ι R M) (f : PolynomialLaw R M N) :
    Finsupp.polynomialMap b (coeff (DFunLike.coe b) f) = f := by
  apply coeff_injective (DFunLike.coe b)
  · rw [_root_.eq_top_iff]
    intro m _
    apply Submodule.span_mono _ (Basis.mem_span_repr_support b m)
    apply Set.image_subset_range
  · rw [coeff_of_finsupp_polynomialMap]

example [DecidableEq ι] (b : Basis ι R M) (i j : ι) : (b.coord i) (b j) = ite (j = i) 1 0 := by
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

noncomputable def coeffPolynomialLawEquiv [DecidableEq ι] (b : Basis ι R M) :
    ((ι →₀ ℕ) →₀ N) ≃ₗ[R] PolynomialLaw R M N where
  toFun h      := Finsupp.polynomialMap b h
  map_add' h k := by
    ext S _ _ m
    simp only [← toFun_eq_toFun', add_toFun, Finsupp.polynomialMap_toFun_apply, Pi.add_apply]
    rw [Finsupp.sum_of_support_subset h (h.support.subset_union_left),
      Finsupp.sum_of_support_subset k (h.support.subset_union_right),
      Finsupp.sum_of_support_subset (h + k) Finsupp.support_add]
    simp_rw [Finsupp.coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [sum_add_distrib]
    all_goals intro i _hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    ext S _ _ m
    simp only [← toFun_eq_toFun', RingHom.id_apply, smul_toFun, Pi.smul_apply,
      Finsupp.polynomialMap_toFun_apply]
    rw [Finsupp.sum_of_support_subset (a • h) Finsupp.support_smul _
      (fun k _ => by rw [TensorProduct.tmul_zero]), Finsupp.sum, smul_sum]
    exact sum_congr rfl (fun k _ => by rw [Finsupp.coe_smul, Pi.smul_apply, tmul_smul])
  invFun f    := coeff (DFunLike.coe b) f
  left_inv h  := by dsimp; rw [coeff_of_finsupp_polynomialMap]
  right_inv f := by dsimp; rw [finsupp_polynomialMap_of_coeff b]

end Fintype

end Coefficients

--#lint
