/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.PolynomialMap.Coeff
import Mathlib.RingTheory.TensorProduct


universe u

section Lemmas

open scoped TensorProduct

variable {R : Type*} [CommSemiring R]
  variable {M : Type*} [AddCommMonoid M] [Module R M]

lemma _root_.TensorProduct.exists_Finsupp
    (S : Type*) [CommSemiring S] [Algebra R S] (μ : S ⊗[R] M) :
    ∃ (m : S →₀ M), μ = m.sum (fun s x => s ⊗ₜ[R] x) := by
  classical
  induction μ using TensorProduct.induction_on with
  | zero => use 0; simp
  | tmul s m => use Finsupp.single s m; simp
  | add x y hx hy =>
    obtain ⟨sx, rfl⟩ := hx
    obtain ⟨sy, rfl⟩ := hy
    use sx + sy
    rw [Finsupp.sum_add_index]
    exact fun _ ↦ by simp
    exact fun _ _ _ _ ↦ by rw [TensorProduct.tmul_add]

theorem TensorProduct.exists_Fin
    (S : Type*) [CommRing S] [Algebra R S] (sm : S ⊗[R] M) :
    ∃ (n : ℕ) (s : Fin n → S) (m : Fin n → M),
      sm = Finset.univ.sum (fun i ↦ (s i) ⊗ₜ[R] (m i)) := by
  have := TensorProduct.exists_Finsupp S sm
  obtain ⟨m, rfl⟩ := this
  let e : m.support ≃ Fin (m.support.card) := Finset.equivFin _
  use m.support.card
  use fun i ↦ e.symm i
  use fun i ↦ m (e.symm i)
  rw [Finsupp.sum, ← Finset.sum_attach]
  apply Finset.sum_equiv e <;> simp

end Lemmas

section Homogeneous

namespace PolynomialMap

open scoped TensorProduct
open MvPolynomial

variable {R : Type u} {M N : Type*}
  [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
/- For the moment, need CommRing and AddCommGroup
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] -/

/-- A polynomial map is homogeneous if all its toFun are homogeneous -/
def IsHomogeneousOfDegree
    (p : ℕ) (f : PolynomialMap R M N) : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (r : S) (m : S ⊗[R] M),
    f.toFun' S (r • m) = r ^ p • f.toFun' S m
#align polynomial_map.is_homogeneous_of_degree PolynomialMap.IsHomogeneousOfDegree

theorem IsHomogeneousOfDegree_add (p : ℕ) {f g : PolynomialMap R M N}
    (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree p) :
    (f + g).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsHomogeneousOfDegree_smul (p : ℕ) (r : R) {f : PolynomialMap R M N}
    (hf : f.IsHomogeneousOfDegree p) : (r • f).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm r (s ^ p) (toFun' f S m)

/-- The submodule of Homogeneous Polynomial maps -/
def grade (p : ℕ) : Submodule R (PolynomialMap R M N) where
  carrier   := IsHomogeneousOfDegree p
  add_mem' hf hg := IsHomogeneousOfDegree_add p hf hg
  smul_mem' r f hf := IsHomogeneousOfDegree_smul p r hf
  zero_mem' := by
    intro S _ _ r _
    simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_grade (f : PolynomialMap R M N) (p : ℕ) :
    f ∈ grade p ↔ IsHomogeneousOfDegree p f := by
  rfl

section coeff
-- WHILE WE HAVE COMMRING/GROUP ASSUMPTIONS ON R, S…

lemma _root_.TensorProduct.smul_rTensor {M : Type*} [AddCommMonoid M] [Module R M]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {T : Type*} [CommSemiring T] [Algebra R T]
    (φ : S →ₐ[R] T) (s : S) (m : S ⊗[R] M) :
    φ s • (φ.toLinearMap.rTensor M m) = φ.toLinearMap.rTensor M (s • m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s' m =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add m m' hm hm' => simp [hm, hm']

lemma isHomogeneousOfDegree_toFun {p : ℕ} {f : PolynomialMap R M N}
    (hf : IsHomogeneousOfDegree p f)
    (S : Type*) [CommRing S] [Algebra R S] (r : S) (m : S ⊗[R] M) :
      f.toFun S (r • m) = r ^ p • f.toFun S m := by
  choose n ψ  m' r' hm' hr' using PolynomialMap.exists_lift' m r
  simp only [← hm', ← hr', ← isCompat_apply, toFun_eq_toFun', TensorProduct.smul_rTensor]
  rw [hf, ← TensorProduct.smul_rTensor, map_pow]

lemma isHomogeneousOfDegree_ground {p : ℕ} {f : PolynomialMap R M N}
    (hf : IsHomogeneousOfDegree p f)
    (r : R) (m : M) : f.ground (r • m) = r ^ p • f.ground m := by
  simp only [ground]
  simp only [Function.comp_apply, map_smul, TensorProduct.lid_symm_apply]
  rw [hf R r, map_smul]

lemma isHomogeneousOfDegree_coeff {f : PolynomialMap R M N} {p : ℕ}
    (hf : IsHomogeneousOfDegree p f)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (m : ι → M)
    (d : ι →₀ ℕ) (hd : d.sum (fun _ n => n) ≠ p) :
    PolynomialMap.coeff m f d = 0 := by
  classical
  let e (b : ι →₀ ℕ) (k : ℕ) : Option ι →₀ ℕ :=
    Finsupp.update (Finsupp.mapDomainEmbedding (Function.Embedding.some) b) none k
  have he : ∀ b k,  (X none ^ k * (Finset.prod Finset.univ
    fun x => X (some x) ^ b x) : MvPolynomial (Option ι) R) =
      MvPolynomial.monomial (e b k) 1 := fun b k ↦ by
    rw [MvPolynomial.monomial_eq]
    simp only [Finsupp.prod_pow, Fintype.prod_option, map_one, one_mul]
    simp [e]
    apply congr_arg₂ _ rfl
    apply Finset.prod_congr rfl
    · intro h _
      rw [Finsupp.mapDomain_apply (Option.some_injective ι)]
  have he_some : ∀ b k i, e b k (some i) = b i :=
    fun b k i ↦ by
      simp [e, Finsupp.update, Function.update, Finsupp.mapDomain_apply (Option.some_injective ι)]
  have he_none : ∀ b k, e b k none = k := fun b k ↦ by
    simp [e, Finsupp.update, Function.update, dif_pos]
 /-  On écrit l'homogénéité : f (∑ T ⬝ X_i m_i) = T ^ p ⬝ f(∑ X_i m_i)
   ∑ coeff f e (T X) ^ e = T ^ p ⬝ ∑ coeff f e X ^ e
   Identification : (coeff f e) T^|e| X^ e = coeff f e T ^ p X ^ e
   On en déduit coeff f e = 0 si |e| ≠ p .    -/
  let μ : MvPolynomial (Option ι) R ⊗[R] M := Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m i)
  have hf' := isHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (X none) μ
  simp only [μ, Finset.smul_sum, TensorProduct.smul_tmul'] at hf'
  simp only [image_eq_coeff_sum] at hf'
  simp only [Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp (LinearMap.rTensor N (MvPolynomial.lcoeff (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [map_finsupp_sum, LinearMap.map_smul] at hφ
  simp [TensorProduct.smul_tmul'] at hφ
  simp [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hφ
  rw [Finsupp.sum_eq_single d] at hφ
  rw [Finsupp.sum_eq_single d] at hφ
  simp [φ, lcoeff] at hφ
  rw [he, MvPolynomial.coeff_monomial, if_pos, one_smul] at hφ
  rw [he, MvPolynomial.coeff_monomial, if_neg, zero_smul] at hφ
  exact hφ
  · rw [eq_comm]
    intro hd'
    apply hd
    rw [DFunLike.ext_iff] at hd'
    convert hd' none <;> exact (he_none _ _).symm
  · simp [Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  · intro b _ hb'
    simp [φ, lcoeff]
    rw [he, MvPolynomial.coeff_monomial, if_neg, zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b p i, h]
    exact he_some d _ i
  · simp
  · intro b _ hb'
    simp [φ, lcoeff]
    rw [he, MvPolynomial.coeff_monomial, if_neg, zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i
  · simp

theorem coeff_comp_equiv' {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (e : ι ≃ κ) (m : κ → M) (k : κ →₀ ℕ) (f : PolynomialMap R M N) :
    coeff m f k = coeff (m ∘ e) f (k.equivMapDomain e.symm) := by
  rw [coeff_comp_equiv]
  congr
  ext k
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

lemma isHomogeneousOfDegree_of_coeff_iff (f : PolynomialMap R M N) (p : ℕ) :
    IsHomogeneousOfDegree p f ↔
    ∀ (n : ℕ) (m : Fin n → M) (d : Fin n →₀ ℕ) (_ : d.sum (fun _ n => n) ≠ p),
      PolynomialMap.coeff m f d = 0 := by
  constructor
  · intro hf n m d hd
    exact isHomogeneousOfDegree_coeff hf m d hd
  · intro H S _ _ r μ
    obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
    simp only [Finset.smul_sum, TensorProduct.smul_tmul']
    simp only [← toFun_eq_toFun']
    rw [image_eq_coeff_sum, image_eq_coeff_sum]
    rw [Finsupp.smul_sum]
    apply Finsupp.sum_congr
    rintro d hd
    simp only [Finsupp.mem_support_iff] at hd
    rw [TensorProduct.smul_tmul']
    apply congr_arg₂ _ _ rfl
    simp only [smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
    apply congr_arg₂ _ _ rfl
    rw [Finset.prod_pow_eq_pow_sum]
    apply congr_arg₂ _ rfl
    specialize H n m d
    rw [not_imp_comm, Finsupp.sum_of_support_subset _ (Finset.subset_univ _)] at H
    apply H
    exact hd
    exact fun _ _ ↦ rfl

/-  let κ := ULift.{v} (Fin n)
  let e : Fin n ≃ ULift.{v} (Fin n) :=
    Equiv.ofBijective  (ULift.up) (by
    constructor
    · intro a b h
      rw [← ULift.down_up a, ← ULift.down_up b, h]
    · intro a
      use a.down)
  rw [coeff_comp_equiv' e.symm, Equiv.symm_symm]
  apply H
  simp only [Finsupp.sum_equivMapDomain, ne_eq]
  convert hd'
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)]
  congr
  exact fun _ _ ↦ rfl -/

/-
lemma isHomogeneousOfDegree_of_coeff' (f : PolynomialMap R M N) (p : ℕ)
    (H : ∀ {ι : Type v} [DecidableEq ι] [Fintype ι] (m : ι → M)
      (d : ι →₀ ℕ) (_ : d.sum (fun _ n => n) ≠ p),
      PolynomialMap.coeff m f d = 0) :
    IsHomogeneousOfDegree p f := by
  classical
· intro S _ _ r μ
  --obtain ⟨m, rfl⟩ := TensorProduct.exists_Finsupp S μ
  obtain ⟨(ι : Type v), _, s, m, rfl⟩ := TensorProduct.exists_Fintype S μ
  simp only [Finsupp.smul_sum, TensorProduct.smul_tmul']
  rw [Finsupp.sum, Finsupp.sum]
  simp only [← toFun_eq_toFun']
  rw [image_eq_coeff_finset_sum, image_eq_coeff_finset_sum]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  rintro d hd
  simp only [Finsupp.mem_support_iff] at hd
  simp only [Function.const_zero]
  rw [TensorProduct.smul_tmul']
  apply congr_arg₂ _ _ rfl
  simp only [smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  apply congr_arg₂ _ _ rfl
  rw [Finset.prod_pow_eq_pow_sum]
  apply congr_arg₂ _ rfl
  by_contra hd'
  apply hd
  let κ := ULift.{v} (Fin (m.support.card))
  let e : { x // x ∈ m.support} ≃ ULift.{v} (Fin (m.support.card)) :=
    Equiv.ofBijective  (ULift.up ∘ m.support.equivFin) (by
    rw [Equiv.bijective_comp]
    constructor
    · intro a b h
      rw [← ULift.down_up a, ← ULift.down_up b, h]
    · intro a
      use a.down)
  rw [coeff_comp_equiv' e.symm, Equiv.symm_symm]
  apply H
  simp only [Finsupp.sum_equivMapDomain, ne_eq]
  intro hd
  apply hd'
  suffices m.support = Finset.map (Function.Embedding.subtype fun x => x ∈ m.support) Finset.univ by
    simp_rw [this]
    rw [Finset.sum_subtype_map_embedding (f := fun x => d x)]
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)] at hd
    exact hd
    · exact fun _ _ ↦ rfl
    · intro x _
      rw [Subtype.val_injective.extend_apply]
  · ext x
    simp only [Finsupp.mem_support_iff, ne_eq, Finset.univ_eq_attach, Finset.mem_map,
      Finset.mem_attach, Function.Embedding.coe_subtype, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
-/

end coeff

end PolynomialMap

end Homogeneous

section ConstantMap

namespace PolynomialMap

variable {R : Type u} [CommRing R]
  {M N : Type _} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open TensorProduct LinearMap MvPolynomial

noncomputable def ofConstant (n : N) : PolynomialMap R M N where
  toFun' S _ _ _:= TensorProduct.tmul R 1 n
  isCompat' φ := by ext; simp
#align polynomial_map.of_constant PolynomialMap.ofConstant

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantHom : N →ₗ[R] (grade 0 : Submodule R (PolynomialMap R M N)) := {
  toFun := fun n ↦ {
    val := ofConstant n
    property := by
      simp only [grade, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
      intro S _ _ r sm
      simp only [pow_zero, one_smul]
      rfl }
  map_add'  := fun x y ↦ by
    simp only [AddSubmonoid.mk_add_mk, Subtype.mk.injEq, ofConstant]
    ext
    simp only [add_def_apply, TensorProduct.tmul_add]
  map_smul' := fun r x ↦ by
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq, ofConstant,
      TensorProduct.tmul_smul]
    rfl }

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantEquiv :
    N ≃ₗ[R] (grade 0 : Submodule R (PolynomialMap R M N)) := {
  ofConstantHom with
  invFun    := fun f ↦ f.val.ground 0
  left_inv  := fun x ↦ by
    simp [ofConstantHom, ground, ofConstant]
  right_inv := fun x ↦ by
    obtain ⟨f, hf⟩ := x
    simp only [mem_grade, isHomogeneousOfDegree_toFun] at hf
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [Subtype.ext_iff]
    rw [Subtype.coe_mk]
    simp [ofConstantHom, ground]
    ext S _ _ m
    conv_rhs =>
      rw [← one_smul (M := S) (f.toFun' S m), ← pow_zero 0, ← hf S _ m]
      rw [zero_smul]
    have := f.isCompat_apply (algebraMap' R S) 0
    simp only [map_zero] at this
    simp [← this, ofConstant, TensorProduct.includeRight_lid, isCompat_apply'] }

end PolynomialMap

end ConstantMap

section Linear

namespace PolynomialMap

open LinearMap
open scoped TensorProduct

variable {R : Type u} [CommRing R]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

noncomputable def ofLinearMap (v : M →ₗ[R] N) : PolynomialMap R M N where
  toFun' S _ _ := v.baseChange S
  isCompat' φ := by
    ext
    simp only [← LinearMap.comp_apply, LinearMap.baseChange_eq_ltensor, Function.comp_apply, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
#align polynomial_map.of_linear_map PolynomialMap.ofLinearMap

lemma ofLinearMap_mem_grade_one (v : M →ₗ[R] N) :
    IsHomogeneousOfDegree 1 (ofLinearMap v) := by
  intro S _ _ r m
  simp [ofLinearMap]

theorem ofLinearMap_toFun' (u : M →ₗ[R] N)
    (S : Type u) [CommRing S] [Algebra R S] :
  (ofLinearMap u).toFun' S = LinearMap.baseChange S u := rfl
#align polynomial_map.of_linear_map_to_fun PolynomialMap.ofLinearMap_toFun'

theorem ofLinearMap_toFun (u : M →ₗ[R] N)
    (S : Type*) [CommRing S] [Algebra R S] :
    (ofLinearMap u).toFun S = u.baseChange S := sorry

theorem ofLinearMap_coeff (u : M →ₗ[R] N)
    (ι : Type*) [DecidableEq ι] [Fintype ι] (m : ι → M) (i : ι) :
    ((coeff m) (ofLinearMap u)) (Finsupp.single i 1) = u (m i) := by
  simp only [coeff]
  sorry

noncomputable def ofLinearMapHom :
    (M →ₗ[R] N) →ₗ[R] (grade 1 : Submodule R (PolynomialMap R M N)) where
  toFun := fun u ↦ ⟨ofLinearMap u, ofLinearMap_mem_grade_one u⟩
  map_add' u v := by
    ext S _ _ m
    simp only [AddSubmonoid.coe_add, add_def_apply]
    simp only [ofLinearMap_toFun', LinearMap.baseChange_add, LinearMap.add_apply]
  map_smul' a v := by
    ext S _ _ m
    simp only [smul_def, ofLinearMap_toFun', LinearMap.baseChange_smul]
    rfl
#align polynomial_map.of_linear_map_hom PolynomialMap.ofLinearMapHom

theorem ofLinearMapHom_apply (v : M →ₗ[R] N) :
  ofLinearMapHom v = ofLinearMap v := rfl
#align polynomial_map.of_linear_map_hom_apply PolynomialMap.ofLinearMapHom_apply

open MvPolynomial
section coeff

variable {R : Type u} [CommRing R]
  {M N : Type _} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

private lemma zero_pow_add_zero_pow (a b : ℕ) (h : a + b = 1) :
  0 ^ a + 0 ^ b = (1 : R) := by
  suffices (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) by
    cases this with
    | inl h => rw [h.1, h.2, pow_one, pow_zero, zero_add]
    | inr h => rw [h.1, h.2, pow_one, pow_zero, add_zero]
  by_cases ha : a = 0
  · right
    exact ⟨ha, by simpa [ha, zero_add] using h⟩
  · left
    suffices ha : a = 1 by
      exact ⟨ha, by simpa [ha, add_right_eq_self] using h⟩
    apply le_antisymm
    · rw [← h]
      exact Nat.le_add_right a b
    exact Nat.pos_of_ne_zero ha

noncomputable def toLinearMap (f : (grade 1 : Submodule R (PolynomialMap R M N))) :
    M →ₗ[R] N := {
  toFun := ground (f : PolynomialMap R M N)
  map_add' := fun m n => by
    obtain ⟨f, hf⟩ := f; dsimp only
    rw [mem_grade, isHomogeneousOfDegree_of_coeff_iff] at hf
    have h := fun (r s : R) ↦ ground_image_eq_coeff_sum_two r s m n f
    have h11 := h 1 1; simp only [one_smul] at h11
    have h10 := h 1 0; simp only [one_smul, zero_smul, add_zero] at h10
    have h01 := h 0 1; simp only [one_smul, zero_smul, zero_add] at h01
    rw [h01, h10, h11]
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro x hx
    rw [← add_smul]
    apply congr_arg₂ _ _ rfl
    simp
    refine (zero_pow_add_zero_pow _ _ ?_).symm
    suffices Finsupp.sum x (fun _ n => n) = 1 by
      rw [add_comm]
      rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)] at this
      simpa only [Function.comp_apply, Fin.sum_univ_two] using this
      · exact fun _ ↦ by simp
    simp only [Finsupp.mem_support_iff, ne_eq] at hx
    exact not_imp_comm.mp (hf _ _ x) hx

  map_smul' := fun r x => by
    obtain ⟨f, hf⟩ := f; dsimp only [RingHom.id_apply]
    rw [mem_grade] at hf
    rw [isHomogeneousOfDegree_ground hf, pow_one] }

theorem Finsupp.sum_eq_one {α : Type*} [DecidableEq α] (d : α →₀ ℕ) :
    Finsupp.sum d (fun a n ↦ n) = 1 ↔
    ∃ a, Finsupp.single a 1 = d := by
  sorry

theorem ofLinearMap_toFun (u : M →ₗ[R] N)
    (S : Type*) [CommRing S] [Algebra R S] :
    (ofLinearMap u).toFun S = LinearMap.baseChange S u := by
  have hu := ofLinearMap_mem_grade_one u
  ext sm
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S sm
  rw [map_sum]
  rw [image_eq_coeff_sum]
  have : Finsupp.support (coeff m (ofLinearMap u)) ⊆
    Finset.map ⟨(fun d => Finsupp.single d 1), by
      apply Finsupp.single_left_injective
      norm_num⟩ Finset.univ := by
    intro d hd
    simp only [Finsupp.mem_support_iff, ne_eq] at hd
    simp only [isHomogeneousOfDegree_of_coeff_iff] at hu
    specialize hu n m d
    rw [not_imp_comm] at hu
    specialize hu hd
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and]
    simpa only [Finsupp.sum_eq_one] using hu
  rw [Finsupp.sum_of_support_subset _ this]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, LinearMap.baseChange_tmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_eq_single i]
  simp only [Finsupp.single_eq_same, pow_one]
  sorry
  · intro _ _ hj
    rw [Finsupp.single_eq_of_ne hj.symm, pow_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · exact fun _ _ ↦ by simp only [TensorProduct.tmul_zero]


noncomputable def ofLinearMapEquiv :
    (M →ₗ[R] N) ≃ₗ[R] (grade 1 : Submodule R (PolynomialMap R M N)) := {
  ofLinearMapHom with
  invFun := toLinearMap
  left_inv := fun f ↦ by
    ext m
    simp [toLinearMap, ground, ofLinearMapHom, ofLinearMap]
  right_inv := fun f ↦ by
    ext S _ _ sm
    simp [ofLinearMapHom, ofLinearMap, toLinearMap]
    sorry }

end coeff

end PolynomialMap

end Linear
