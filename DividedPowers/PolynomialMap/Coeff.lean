import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

import DividedPowers.PolynomialMap.Basic
-- import Mathlib.Data.MvPolynomial.Basic
-- import Mathlib.LinearAlgebra.Multilinear.Basic

open TensorProduct Algebra Function MvPolynomial LinearMap Algebra.TensorProduct

universe u v w uM uN uι

section Finset

@[to_additive]
theorem Finset.prod_congr_equiv {α β M : Type*} [CommMonoid M]
  {f : α → M} {s : Finset α}
  (e : α ≃ β) : s.prod f = (s.map e).prod (f ∘ e.symm)  := by
  simp only [Function.comp_apply, Finset.prod_map, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply]

-- Useful ?
@[to_additive]
theorem Finset.prod_congr_equiv' {α β M : Type _} [CommMonoid M]
  {f : β → M} {s : Finset α}
  (e : α ≃ β) : s.prod (f ∘ e) = (s.map e).prod f := by
  simp only [Function.comp_apply, prod_map, Equiv.coe_toEmbedding]

theorem Finsupp.ofSupportFinite_support {ι α : Type*} [Zero α]
    (f : ι → α) (hf : f.support.Finite) :
  (Finsupp.ofSupportFinite f hf).support = hf.toFinset := by
  ext
  simp only [Finsupp.ofSupportFinite_coe, Finsupp.mem_support_iff,
    Set.Finite.mem_toFinset, Function.mem_support]

end Finset

section Algebra

open Algebra Function LinearMap

open scoped TensorProduct

variable (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]

-- The natural `R`-algebra map from `S ⊗[R] R` to `S`.
noncomputable def Algebra.TensorProduct.rid' : S ⊗[R] R →ₐ[S] S := Algebra.TensorProduct.rid R S S

@[simp]
theorem Algebra.TensorProduct.rid'_tmul (r : R) (s : S) : (rid' R S) (s ⊗ₜ[R] r) = r • s := rfl

variable (M : Type*) [AddCommMonoid M] [Module R M]

open Algebra.TensorProduct LinearMap

namespace LinearForm

noncomputable def baseChange (f : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (rid' R S).toLinearMap.comp (LinearMap.baseChange S f)
#align linear_form.base_change LinearForm.baseChange

theorem baseChange_apply_tmul (f : M →ₗ[R] R) (r : S) (m : M) :
  baseChange R S M f (r ⊗ₜ[R] m) = r * ((f m) • (1 : S)) := by
  simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
    AlgHom.toLinearMap_apply, rid'_tmul, Algebra.mul_smul_comm, _root_.mul_one]
#align linear_form.base_change_apply_tmul LinearForm.baseChange_apply_tmul

variable (S' : Type*) [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S')

theorem baseChange_compat_apply (f : M →ₗ[R] R) (m : S ⊗[R] M) :
  φ (baseChange R S M f m) =
    (baseChange R S' M f) ((rTensor M φ.toLinearMap) m) := by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · simp only [map_zero]
  · simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
      AlgHom.toLinearMap_apply, rid'_tmul, map_smul, rTensor_tmul]
  · simp only [map_add, hx, hy]

end LinearForm

section MvPolynomial

variable {R : Type*} [CommSemiring R]
def MvPolynomial.lcoeff (k : ι →₀ ℕ) : MvPolynomial ι R →ₗ[R] R where
  toFun     := coeff k
  map_add'  := coeff_add k
  map_smul' := coeff_smul k

theorem MvPolynomial.lcoeff_apply (k : ι →₀ ℕ) (f : MvPolynomial ι R) :
    lcoeff k f = coeff k f := rfl

end MvPolynomial

end Algebra

namespace PolynomialMap

noncomputable section LocFinsupp

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- A family `f : ι → M →ₚ[R] N` of polynomial maps has locally finite support
  if, for all `S`, `fun i ↦ (f i).toFun' S` has finite support` -/
def LocFinsupp {ι : Type*} (f : ι → PolynomialMap R M N) :=
    ∀ (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M),
      (Function.support fun i => (f i).toFun' S m).Finite
#align polynomial_map.locfinsupp PolynomialMap.LocFinsupp

theorem LocFinsupp_add {ι : Type*} {f g : ι → M →ₚ[R] N}
    (hf : LocFinsupp f) (hg : LocFinsupp g) :
    LocFinsupp (f + g) := fun S _ _ m ↦
  Set.Finite.subset (Set.finite_union.mpr ⟨hf S m, hg S m⟩)
      (Function.support_add _ _)

theorem LocFinsupp_zero {ι : Type*} :
    LocFinsupp (0 : ι → M →ₚ[R] N) := fun S _ _ _ ↦ by
  simp only [Pi.zero_apply, zero_def, Function.support_zero, Set.finite_empty]

theorem LocFinsupp_smul {ι : Type*} (r : R) {f : ι → M →ₚ[R] N}
    (hf : LocFinsupp f) : LocFinsupp (r • f) := fun S _ _ m ↦
  Set.Finite.subset (hf S m) (Function.support_smul_subset_right _ _)

variable (R M N)
/-- The submodule of families of polynomial maps which have locally finite support  -/
def Submodule.locFinsupp (ι : Type*) : Submodule R (ι → PolynomialMap R M N) where
  carrier := LocFinsupp
  add_mem' := LocFinsupp_add
  zero_mem' := LocFinsupp_zero
  smul_mem' := LocFinsupp_smul

variable {R M N}

open Classical in
/-- The sum of of a family polynomial maps (0 if not locally finite) -/
noncomputable def lfsum {ι : Type*} (f : ι → PolynomialMap R M N) :
    PolynomialMap R M N :=
  if hf : LocFinsupp f then {
  toFun' := fun S _ _ m ↦ (Finsupp.ofSupportFinite _ (hf S m)).sum fun _ m => m
  isCompat' := fun {S _ _ S' _ _} φ ↦ by
    ext m
    simp only [Function.comp_apply, map_finsupp_sum]
    rw [Finsupp.sum]
    suffices _ ⊆ (hf S m).toFinset by
      rw [Finsupp.sum_of_support_subset _ this]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.ofSupportFinite_coe, _root_.map_sum, isCompat_apply']
      · intro i _; rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply']
      intro hi
      rw [hi, map_zero] }
  else 0

theorem lfsum_eq {ι : Type*} {f : ι → PolynomialMap R M N}
    (hf : LocFinsupp f)
    (S : Type _) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
  (lfsum f).toFun' S m =
    (Finsupp.ofSupportFinite _ (hf S m)).sum fun _ m => m := by
  rw [lfsum, dif_pos hf]

/-- The sum of a locally finite family of polynomial maps, as a linear map -/
noncomputable def lLfsum {ι : Type _} [DecidableEq ι] :
    Submodule.locFinsupp R M N ι →ₗ[R] PolynomialMap R M N where
  toFun fhf := PolynomialMap.lfsum fhf.val
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext S _ _ m
    dsimp only [AddSubmonoid.mk_add_mk, add_def, Pi.add_apply]
    rw [lfsum_eq hf, lfsum_eq hg, lfsum_eq (LocFinsupp_add hf hg)]
    simp only [Pi.add_apply, add_def_apply]
    rw [@Finsupp.sum_of_support_subset _ _ _ _ _ _ ((hf S m).toFinset ∪ (hg S m).toFinset),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_left _ _),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_right _ _), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    all_goals try intro i hi; rfl
    · intro x
      simp only [Finsupp.ofSupportFinite_support, Set.Finite.mem_toFinset,
        Function.mem_support, Ne.def, Finset.mem_union]
      rw [← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' := fun a ⟨f,hf⟩ ↦ by
    ext S _ _ m
    dsimp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, AddSubmonoid.mk_add_mk, add_def,
      add_def_apply, id_eq, Pi.add_apply, ne_eq, eq_mpr_eq_cast, cast_eq, AddHom.toFun_eq_coe,
      AddHom.coe_mk, SetLike.val_smul, smul_def, RingHom.id_apply, Pi.smul_apply]
    rw [lfsum_eq hf, lfsum_eq (LocFinsupp_smul a hf)]
    simp only [Pi.smul_apply, smul_def_apply]
    rw [Finsupp.sum_of_support_subset]
    · rw [Finsupp.smul_sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, SetLike.val_smul, Pi.smul_apply, smul_def, Finsupp.mem_support_iff, ne_eq, not_imp_not, PolynomialMap.smul_def]
      intro hi
      rw [hi, smul_zero]
    · intro i _ ; rfl

end LocFinsupp


section Coefficients

variable {R : Type u} [CommRing R]
  {M : Type uM} [AddCommGroup M]  [Module R M]
  {N : Type uN} [AddCommGroup N][Module R N]

variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

noncomputable def generize (m : ι → M) :
  PolynomialMap R M N →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun := fun f ↦ f.toFun (MvPolynomial ι R)
    (Finset.univ.sum fun i => X i ⊗ₜ[R] m i)
  map_add' := fun p q ↦ by
    simp only [add_toFun_apply]
  map_smul' := fun r p ↦ by
    simp only [RingHom.id_apply, smul_toFun, Pi.smul_apply]

theorem generize_comp_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (m : κ → M) (f : PolynomialMap R M N) :
    generize m f = (aeval (fun i ↦ X (e i))).toLinearMap.rTensor N
      (generize (fun x ↦ m (e x)) f) := by
  let hf := f.isCompat_apply
    (aeval (fun i ↦ X (e i)) : MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (Finset.univ.sum (fun i ↦ X i ⊗ₜ[R] (m (e i))))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf
  simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [comp_apply, hf]
  apply congr_arg
  simp only [Finset.sum_congr_equiv e, Finset.map_univ_equiv]
  apply Finset.sum_congr rfl
  intro k _ ; simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem generize_comp_equiv' {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (m : κ → M)  (f : PolynomialMap R M N):
    (generize (fun x ↦ m (e x)) f) =
      (aeval (fun i ↦ X (e.symm i))).toLinearMap.rTensor N
      (generize m f) := by
  let hf' := f.isCompat_apply
    (aeval (fun i ↦ X (e.symm i)) : MvPolynomial κ R →ₐ[R] MvPolynomial ι R)
    (Finset.univ.sum (fun i ↦ X i ⊗ₜ[R] (m i)))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, aeval_X] at hf'
  simp only [generize, coe_mk, AddHom.coe_mk]
  rw [hf']
  apply congr_arg
  simp only [Finset.sum_congr_equiv e, Finset.map_univ_equiv]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

/-
theorem generize_comp_embed (f : PolynomialMap R M N)
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
noncomputable def coeff (m : ι → M) :
    PolynomialMap R M N →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (generize m)

#align polynomial_map.coeff PolynomialMap.coeff

theorem generize_eq (m : ι → M) (f : PolynomialMap R M N)  :
  generize m f = (coeff m f).sum
    (fun k n => (monomial k 1) ⊗ₜ n)  := by
  simp only [coeff]
  dsimp
  generalize h : scalarRTensor (generize m f) = p
  rw [eq_comm, ← LinearEquiv.symm_apply_eq] at h
  rw [← h]
  rw [LinearEquiv.symm_apply_eq, map_finsupp_sum]
  ext d
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single d, scalarRTensor_apply_tmul_apply,
    coeff_monomial, if_pos rfl, _root_.one_smul]
  · intro b _ hb
    rw [scalarRTensor_apply_tmul_apply, coeff_monomial, if_neg hb, _root_.zero_smul]
  · simp

theorem _root_.MvPolynomial.rTensor_lcoeff {σ : Type*} [DecidableEq σ]
    (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    (LinearMap.rTensor N (lcoeff k)) sn = 1 ⊗ₜ[R] (scalarRTensor sn) k  := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    simp only [rTensor_tmul, scalarRTensor_apply_tmul, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single k, Finsupp.single_eq_same, lcoeff_apply,
      ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    congr
    intro b _ hb; rw [Finsupp.single_eq_of_ne hb]
    intro _; simp
  | add x y hx hy =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy,
      Finsupp.add_apply, tmul_add]

theorem _root_.MvPolynomial.scalarRTensor_apply {σ : Type*} [DecidableEq σ]
    (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    scalarRTensor sn k = TensorProduct.lid R N ((LinearMap.rTensor N (lcoeff k)) sn) := by
  rw [← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply, rTensor_lcoeff]

theorem coeff_eq (m : ι → M) (k : ι →₀ ℕ) (f : PolynomialMap R M N) :
  coeff m f k =
    (TensorProduct.lid R N)
      ((LinearMap.rTensor N (MvPolynomial.lcoeff k))
        (f.toFun (MvPolynomial ι R) (Finset.univ.sum
          fun i : ι => MvPolynomial.X i ⊗ₜ[R] m i))) := by
  simp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  exact scalarRTensor_apply _ _
 #align polynomial_map.coeff_eq PolynomialMap.coeff_eq

theorem coeff_comp_equiv {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (e : ι ≃ κ) (m : κ → M) (k : ι →₀ ℕ) (f : PolynomialMap R M N) :
  coeff m f (k.equivMapDomain e) = coeff (m.comp e) f (k) := by
  simp only [coeff]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  simp only [MvPolynomial.scalarRTensor_apply]
  rw [Function.comp]

  let hf := f.isCompat_apply
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
        MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[R] (m (e i))))
  simp only [map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf
  suffices toFun f (MvPolynomial κ R)
    (Finset.sum Finset.univ (fun x ↦ MvPolynomial.X (e x) ⊗ₜ[R] m (e x))) =
      generize m f by
    rw [this] at hf
    rw [← hf]
    generalize h : generize (fun x ↦ m (e x)) f = g
    simp only [generize, coe_mk, AddHom.coe_mk] at h
    rw [h]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    rw [← LinearMap.rTensor_comp_apply]
    congr
    ext p
    simp only [coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    simp only [MvPolynomial.aeval_monomial, _root_.map_one, Finsupp.prod_pow,
      _root_.one_mul, MvPolynomial.lcoeff_apply]
    suffices Finset.prod Finset.univ (fun x ↦ MvPolynomial.X (e x) ^ p x) =
        MvPolynomial.monomial (Finsupp.equivMapDomain e p) (1 : R) by
      simp only [this, MvPolynomial.coeff_monomial]
      by_cases h : p = k
      . rw [if_pos h, if_pos]
        rw [h]
      . rw [if_neg h, if_neg]
        intro h'; apply h
        simp only [DFunLike.ext_iff] at h'
        ext i
        specialize h' (e i)
        simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using h'
    . simp only [MvPolynomial.monomial_eq, _root_.map_one, Finsupp.prod_pow,
        Finsupp.equivMapDomain_apply, _root_.one_mul]
      rw [Finset.prod_congr_equiv e]
      simp only [Finset.map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]
  . rw [generize, coe_mk, AddHom.coe_mk]
    apply congr_arg
    rw [Finset.sum_congr_equiv e]
    simp only [Finset.map_univ_equiv, Function.comp_apply, Equiv.apply_symm_apply]

theorem coeff_comp_equiv' {κ : Type*} [DecidableEq κ] [Fintype κ]
    (e : ι ≃ κ) (m : κ → M) (k : κ →₀ ℕ) (f : PolynomialMap R M N) :
    coeff m f k = coeff (m ∘ e) f (k.equivMapDomain e.symm) := by
  rw [coeff_comp_equiv]
  congr
  ext k
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem image_eq_coeff_sum
    (m : ι → M)
    (f : PolynomialMap R M N)
    (S : Type*) [CommRing S] [Algebra R S] (r : ι → S) :
  f.toFun S (Finset.univ.sum fun i => r i ⊗ₜ[R] m i) =
    (coeff m f).sum
      (fun k n => (Finset.univ.prod fun i => r i ^ k i) ⊗ₜ[R] n) := by
  have that := congr_fun (f.isCompat (MvPolynomial.aeval r))
    (Finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at that
  rw [← that]
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [h]
  simp only [Finsupp.sum, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [MvPolynomial.aeval_monomial]
#align polynomial_map.image_eq_coeff_sum PolynomialMap.image_eq_coeff_sum

/-- Variant of `image_eq_coeff_sum` over a Finset -/
theorem image_eq_coeff_finset_sum {ι : Type*} [DecidableEq ι]
    (m : ι → M)
    (f : PolynomialMap R M N)
    (S : Type*) [CommRing S] [Algebra R S]
    (r : ι → S) (s : Finset ι):
  f.toFun S (s.sum fun i => r i ⊗ₜ[R] m i) =
    (coeff (fun i : s => m i) f).sum
      (fun k n => (s.prod fun i =>
        r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i)) ⊗ₜ[R] n) := by
  let m' : s → M := fun i => m i
  let r' : s → S := fun i => r i
  convert image_eq_coeff_sum m' f S r'
  · simp only [Finset.univ_eq_attach, Finsupp.coe_mk]
    rw [← Finset.sum_attach]
  · simp only [Finset.univ_eq_attach, Finsupp.coe_mk]
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro x _
    simp only [const_zero, exists_apply_eq_apply, not_true]
    apply congr_arg₂ _ rfl
    rw [Subtype.coe_injective.extend_apply]

-- Useful ?
/-- Variant of `image_eq_coeff_sum'` with a `Finsupp`-/
theorem image_eq_coeff_sum' {ι : Type*} [DecidableEq ι] (m : ι → M)
    (f : PolynomialMap R M N)
    (S : Type*) [CommRing S] [Algebra R S] (r : ι →₀ S) :
    f.toFun S (r.sum fun i a => a ⊗ₜ[R] m i) =
      (coeff (fun i : r.support => m i) f).sum
        (fun k n =>
          (r.support.prod
            (fun i => r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i) )
           ⊗ₜ[R] n)) := by
  rw [Finsupp.sum]
  rw [image_eq_coeff_finset_sum]
#align polynomial_map.image_eq_coeff_sum' PolynomialMap.image_eq_coeff_sum'

theorem ground_image_eq_coeff_sum
    (m : ι → M)
    (f : PolynomialMap R M N)
    (r : ι → R) :
  ground f (Finset.univ.sum fun i => (r i) • (m i)) =
    (coeff m f).sum
      (fun k n => (Finset.univ.prod fun i => r i ^ k i) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  simp only [TensorProduct.lid_symm_apply]
  rw [isCompat_apply_ground]
  simp only [← TensorProduct.lid_symm_apply]
  simp only [map_sum, TensorProduct.lid_symm_apply,
    ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [image_eq_coeff_sum]
  simp only [← TensorProduct.lid_symm_apply]
  simp only [map_finsupp_sum, map_finsupp_sum, TensorProduct.lid_symm_apply]
  apply Finsupp.sum_congr
  intro d _
  rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]

theorem ground_image_eq_coeff_sum_one (m : M) (f : PolynomialMap R M N) (r : R) :
  ground f (r • m) =
    (coeff (const Unit m) f).sum (fun k n => r ^ (k 0) • n) := by
  suffices r • m = Finset.univ.sum
    fun i ↦ (const Unit r) i • (const Unit m i) by
    rw [this, ground_image_eq_coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.univ_unique, const_apply, Finset.prod_singleton]
    rfl
  simp only [Finset.univ_unique, const_apply, Finset.sum_const, Finset.card_singleton, _root_.one_smul]

theorem ground_image_eq_coeff_sum_two
    (r₁ r₂ : R) (m₁ m₂ : M) (f : PolynomialMap R M N) :
    ground f (r₁ • m₁ + r₂ • m₂) =
      (coeff (![m₁, m₂]) f).sum fun k n =>
        (Finset.univ.prod (fun i => (![r₁, r₂]) i ^ (k i)) • n) := by
  suffices r₁ • m₁ + r₂ • m₂ = Finset.univ.sum
    fun i ↦ (![r₁, r₂]) i • (![m₁, m₂]) i  by
    rw [this, ground_image_eq_coeff_sum]
  simp

variable {S : Type v} [CommRing S] [Algebra R S]

theorem span_tensorProduct_eq_top_of_span_eq_top
    (σ : Type _) (e : σ → M)
    (hm : Submodule.span R (Set.range e) = ⊤) :
    (Submodule.span S (Set.range fun s => (1 : S) ⊗ₜ[R] e s) :
  Submodule S (S ⊗[R] M)) = ⊤ := by
  rw [_root_.eq_top_iff]
  intro m h
  induction' m using TensorProduct.induction_on with r m x y hx hy
  exact zero_mem _
  · let f : M →ₗ[R] S ⊗[R] M :=
      { toFun := fun m => (1 : S) ⊗ₜ[R] m
        map_add' := fun x y => by simp only [TensorProduct.tmul_add]
        map_smul' := fun a x => by simp only [TensorProduct.tmul_smul, RingHom.id_apply] }
    suffices r ⊗ₜ[R] m = r • (1 : S) ⊗ₜ[R] m by
      rw [this]
      refine' Submodule.smul_mem _ r _
      apply Submodule.span_le_restrictScalars R
      convert Submodule.apply_mem_span_image_of_mem_span
        (s := Set.range e) f _
      . conv_rhs => rw [← Set.image_univ, Set.image_image, Set.image_univ]
      . rw [hm]; exact Submodule.mem_top
    rw [TensorProduct.smul_tmul']; simp only [Algebra.id.smul_eq_mul, _root_.mul_one]
  exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
#align polynomial_map.span_tensor_product_eq_top_of_span_eq_top PolynomialMap.span_tensorProduct_eq_top_of_span_eq_top

theorem coeff_injective [DecidableEq ι] (m : ι → M)
    (hm : Submodule.span R (Set.range m) = ⊤)
    (f g : PolynomialMap R M N) (h : coeff m f = coeff m g) :
  f = g := by
  ext S _ _ p
  suffices hp : p ∈ Submodule.span S (Set.range fun s => 1 ⊗ₜ[R] m s) by
    simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
    obtain ⟨r, rfl⟩ := hp
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)]
    simp only [← toFun_eq_toFun'_apply]
    rw [image_eq_coeff_sum m f]
    simp only [image_eq_coeff_sum, h]
    . intro i _
      simp only [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul]
  rw [PolynomialMap.span_tensorProduct_eq_top_of_span_eq_top ι m hm]
  exact Submodule.mem_top
#align polynomial_map.coeff_injective PolynomialMap.coeff_injective

/- When M is free, we can go in the other direction and construct,
  from a basis `b` of `M` and `N`-valued polynomials, a polynomial map -/

variable (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N)

noncomputable def Finsupp.polynomialMap_toFun
  (S : Type*) [CommRing S] [Algebra R S] (x : S ⊗[R] M) : S ⊗[R] N :=
  h.sum fun k n =>
    (Finset.univ.prod fun i =>
      (LinearForm.baseChange R S _ (b.coord i)) x ^ k i) ⊗ₜ[R] n

noncomputable def Finsupp.polynomialMap_toFun'
  (S : Type*) [CommRing S] [Algebra R S] (x : S ⊗[R] M) : S ⊗[R] N :=
  h.sum fun k n =>
    (k.prod fun i m =>
      (LinearForm.baseChange R S _ (b.coord i)) x ^ m) ⊗ₜ[R] n


theorem Finsupp.polynomialMap_isCompat
    {S : Type*} [CommRing S] [Algebra R S]
    {S' : Type*} [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ (Finsupp.polynomialMap_toFun b h S) =
      Finsupp.polynomialMap_toFun b h S' ∘ (φ.toLinearMap.rTensor M) := by
  ext m
  dsimp
  simp only [polynomialMap_toFun, Finsupp.sum]
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  rw [map_prod φ]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]
  apply congr_arg₂ _ _ rfl
  rw [LinearForm.baseChange_compat_apply]

/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ,
  `Finsupp.polynomialMap b h : M →ₚ[R] N` is the polynomial map
  whose coefficients at `b` are given by `h` -/
noncomputable def Finsupp.polynomialMap (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
    PolynomialMap R M N where
  toFun' S _ _ x := polynomialMap_toFun b h S x
  isCompat' φ := polynomialMap_isCompat b h φ
#align polynomial_map.finsupp.polynomial_map PolynomialMap.Finsupp.polynomialMap

theorem Finsupp.polynomialMap_toFun_apply (b : Basis ι R M)
    (h : (ι →₀ ℕ) →₀ N) (m : S ⊗[R] M) :
  (Finsupp.polynomialMap b h).toFun S m =
    h.sum fun k n =>
      (Finset.univ.prod
        (fun i => (LinearForm.baseChange R S _ (b.coord i)) m ^ k i)) ⊗ₜ[R] n := by
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialMap.exists_lift m
  rw [← isCompat_apply, toFun_eq_toFun']
  simp only [polynomialMap, polynomialMap_toFun]
  simp only [map_finsupp_sum]
  apply Finsupp.sum_congr
  intro k _
  simp only [LinearMap.rTensor_tmul]
  congr
  simp only [AlgHom.toLinearMap_apply, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro i _
  apply congr_arg₂ _ _ rfl
  simp only [LinearForm.baseChange_compat_apply]
#align polynomial_map.finsupp.polynomial_map_to_fun_apply PolynomialMap.Finsupp.polynomialMap_toFun_apply

theorem generize_finsupp_eq [DecidableEq ι] (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
    ((generize ⇑b) (Finsupp.polynomialMap b h)) =
      Finsupp.sum h (fun k n ↦ (monomial k 1) ⊗ₜ[R] n) := by
  simp [generize]
  set m := Finset.sum Finset.univ (fun i => (X i : MvPolynomial ι R) ⊗ₜ[R] b i) with hm
  simp [Finsupp.polynomialMap_toFun_apply]
  have : ∀ i,
  (LinearForm.baseChange R (MvPolynomial ι R) M (Basis.coord b i)) m
    = X i := fun i ↦ by
    rw [hm, map_sum, Finset.sum_eq_single i]
    simp only [LinearForm.baseChange_apply_tmul, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same, _root_.one_smul, mul_one]
    · intro j _ hj
      simp only [LinearForm.baseChange_apply_tmul, Basis.coord_apply,
        Basis.repr_self, Algebra.mul_smul_comm, mul_one, Finsupp.single_smul,
        _root_.one_smul, Finsupp.single_eq_of_ne hj]
      · simp
    · intro hi; exfalso; exact hi (Finset.mem_univ _)
  simp [this]
  apply Finsupp.sum_congr
  intro k _
  congr
  rw [← MvPolynomial.prod_X_pow_eq_monomial, ← Finset.prod_mul_prod_compl k.support]
  convert mul_one _
  apply Finset.prod_eq_one
  intro i hi
  simp only [Finset.mem_compl, Finsupp.mem_support_iff, ne_eq, not_not] at hi
  rw [hi, pow_zero]


/-- Given `b : Basis ι R M` and `h : (ι →₀ ℕ) →₀ ℕ,
  `Finsupp.polynomialMap b h : M →ₚ[R] N` is the polynomial map
  whose coefficients at `b` are given by `h` -/
theorem coeff_of_finsupp_polynomialMap [DecidableEq ι]
    (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
    coeff (DFunLike.coe b) (Finsupp.polynomialMap b h) = h := by
  simp only [coeff, coe_mk, AddHom.coe_mk]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  ext d
  rw [scalarRTensor_apply]
  rw [eq_comm, ← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply]
  rw [generize_finsupp_eq, map_finsupp_sum, Finsupp.sum_eq_single d]
  simp only [rTensor_tmul, lcoeff_apply, coeff_monomial, if_pos]
  intro b _ hb
  simp only [rTensor_tmul, lcoeff_apply, coeff_monomial, if_neg hb, zero_tmul]
  intro _; simp

theorem finsupp_polynomialMap_of_coeff [DecidableEq ι]
    (b : Basis ι R M) (f : PolynomialMap R M N) :
  Finsupp.polynomialMap b (coeff (DFunLike.coe b) f) = f := by
  apply coeff_injective (DFunLike.coe b)
  · rw [_root_.eq_top_iff]; intro m _
    apply Submodule.span_mono _ (Basis.mem_span_repr_support b m)
    apply Set.image_subset_range
  rw [coeff_of_finsupp_polynomialMap]
#align polynomial_map.finsup_polynomial_map_of_coeff PolynomialMap.finsupp_polynomialMap_of_coeff

example [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
  (b.coord i) (b j) = ite (j = i) 1 0 := by
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

noncomputable def coeffPolynomialMapEquiv [DecidableEq ι]
    (b : Basis ι R M) :
    ((ι →₀ ℕ) →₀ N) ≃ₗ[R] PolynomialMap R M N where
  toFun h := Finsupp.polynomialMap b h
  map_add' h k := by
--    classical
    ext S _ _ m
    simp only [← toFun_eq_toFun', add_toFun]
    simp only [Finsupp.polynomialMap_toFun_apply, Pi.add_apply]
    rw [Finsupp.sum_of_support_subset h (h.support.subset_union_left k.support)]
    rw [Finsupp.sum_of_support_subset k (h.support.subset_union_right k.support)]
    rw [Finsupp.sum_of_support_subset (h + k) Finsupp.support_add]
    simp_rw [Finsupp.coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [Finset.sum_add_distrib]
    all_goals intro i hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    ext S _ _ m
    -- rw [ext_iff]; ext R _ _ m; skip
    simp only [← toFun_eq_toFun']
    simp only [RingHom.id_apply, smul_toFun, Pi.smul_apply]
    simp [Finsupp.polynomialMap_toFun_apply]
    rw [Finsupp.sum_of_support_subset (a • h) Finsupp.support_smul]
    simp only [Finsupp.sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Finsupp.coe_smul, Pi.smul_apply, TensorProduct.tmul_smul]
    intro k _; rw [TensorProduct.tmul_zero]
  invFun f := coeff (DFunLike.coe b) f
  left_inv h := by dsimp; rw [coeff_of_finsupp_polynomialMap]
  right_inv f := by dsimp; rw [finsupp_polynomialMap_of_coeff b]
#align polynomial_map.coeff_polynomial_map_equiv PolynomialMap.coeffPolynomialMapEquiv

end Coefficients
