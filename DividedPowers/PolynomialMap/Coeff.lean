import DividedPowers.PolynomialMap.Basic
import Mathlib.RingTheory.TensorProduct
-- import Mathlib.Data.MvPolynomial.Basic
-- import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorProduct


open TensorProduct Algebra Function LinearMap Algebra.TensorProduct


namespace PolynomialMap

section Coefficients

variable {R : Type u} {M N : Type _} [CommRing R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

variable {ι : Type u} [DecidableEq ι] [Fintype ι]

variable (R N)
noncomputable def generize (m : ι → M) :
  PolynomialMap R M N →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun := fun f ↦ f.toFun (MvPolynomial ι R)
    (Finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[R] m i)
  map_add' := fun p q ↦ by
    simp only [add_def_apply]
  map_smul' := fun r p ↦ by
    simp only [RingHom.id_apply, PolynomialMap.smul_def, Pi.smul_apply]

variable {R N}


theorem generize_comp_equiv
  {ι : Type u} {κ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (e : ι ≃ κ) (m : κ → M) (f : PolynomialMap R M N) :
  generize R N m f = (LinearMap.rTensor N
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i))).toLinearMap)
      (generize R N (fun x ↦ m (e x)) f)
   := by
  let hf := f.isCompat_apply
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
        MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[R] (m (e i))))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf
  simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [Function.comp_apply, hf]
  apply congr_arg
  simp only [Finset.sum_congr_equiv e, Finset.map_univ_equiv]
  apply Finset.sum_congr rfl
  intro k _ ; simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem generize_comp_equiv'
    {ι : Type u} {κ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι][DecidableEq κ]
    (e : ι ≃ κ) (m : κ → M)  (f : PolynomialMap R M N):
  (generize R N (fun x ↦ m (e x)) f) =
    (rTensor N
      (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e.symm i))).toLinearMap)
    (generize R N m f) := by
  let hf' := f.isCompat_apply
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e.symm i)) :
        MvPolynomial κ R →ₐ[R] MvPolynomial ι R)
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[R] (m i)))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at hf'
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
  PolynomialMap R M N →ₗ[R] (ι →₀ ℕ) →₀ N := by
    exact (zooEquiv ι R N).symm.comp (generize R N m)
#align polynomial_map.coeff PolynomialMap.coeff

theorem generize_eq (m : ι → M) (f : PolynomialMap R M N)  :
  generize R N m f = (coeff m f).sum
    (fun k n => (MvPolynomial.monomial k 1) ⊗ₜ n)  := by
  simp only [coeff]
  dsimp
  generalize h : (zooEquiv ι R N).symm (generize R N m f) = p
  rw [LinearEquiv.symm_apply_eq] at h
  rw [h]
  rfl

theorem coeff_eq (m : ι → M) (k : ι →₀ ℕ) (f : PolynomialMap R M N) :
  coeff m f k =
    (TensorProduct.lid R N)
      ((LinearMap.rTensor N (MvPolynomial.lcoeff k))
        (f.toFun (MvPolynomial ι R) (Finset.univ.sum
          fun i : ι => MvPolynomial.X i ⊗ₜ[R] m i))) := by
  simp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  simp only [generize, coe_mk, AddHom.coe_mk]
  rw [zooEquiv_symm_apply]
#align polynomial_map.coeff_eq PolynomialMap.coeff_eq


theorem coeff_comp_equiv {ι : Type u} [DecidableEq ι] [Fintype ι]
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (e : ι ≃ κ) (m : κ → M) (k : ι →₀ ℕ) (f : PolynomialMap R M N) :
  coeff m f (k.equivMapDomain e) = coeff (m.comp e) f (k) := by
  simp only [coeff]

  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  simp only [zooEquiv_symm_apply]
  have : m ∘ e = fun x ↦ m (e x) := rfl
  rw [this]

  let hf := f.isCompat_apply
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) :
        MvPolynomial ι R →ₐ[R] MvPolynomial κ R)
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[R] (m (e i))))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf
  suffices : toFun f (MvPolynomial κ R) (Finset.sum Finset.univ (fun x ↦ MvPolynomial.X (e x) ⊗ₜ[R] m (e x))) =
    generize R N m f
  rw [this] at hf
  rw [← hf]

  generalize h : generize R N (fun x ↦ m (e x)) f = g
  simp only [generize, coe_mk, AddHom.coe_mk] at h
  rw [h]

  simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [← LinearMap.rTensor_comp_apply]
  congr

  ext p
  simp only [coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  simp only [MvPolynomial.aeval_monomial, _root_.map_one, Finsupp.prod_pow, 
    _root_.one_mul, MvPolynomial.lcoeff_apply]
  suffices : Finset.prod Finset.univ (fun x ↦ MvPolynomial.X (e x) ^ p x) = MvPolynomial.monomial (Finsupp.equivMapDomain e p) (1 : R)
  simp only [this, MvPolynomial.coeff_monomial]
  by_cases h : p = k
  . rw [if_pos h, if_pos]
    rw [h]
  . rw [if_neg h, if_neg]
    intro h'; apply h
    simp only [FunLike.ext_iff] at h'
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



theorem image_eq_coeff_sum
    (m : ι → M)
    (f : PolynomialMap R M N)
    (S : Type u) [CommRing S] [Algebra R S] (r : ι → S) :
  f.toFun S (Finset.univ.sum fun i => r i ⊗ₜ[R] m i) =
    (coeff m f).sum
      (fun k n => (Finset.univ.prod fun i => r i ^ k i) ⊗ₜ[R] n) := by
  have that := congr_fun (f.isCompat (MvPolynomial.aeval r))
    (Finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[R] m i)
  simp only [Function.comp_apply, LinearMap.map_sum, LinearMap.rTensor_tmul,
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
theorem image_eq_coeff_finset_sum {ι : Type u} [DecidableEq ι]
    (m : ι → M)
    (f : PolynomialMap R M N)
    (S : Type u) [CommRing S] [Algebra R S]
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
    simp only [Pi.const_zero, exists_apply_eq_apply, not_true]
    apply congr_arg₂ _ rfl
    rw [Subtype.coe_injective.extend_apply]


-- Useful ?
/-- Variant of `image_eq_coeff_sum'` with a `Finsupp`-/
theorem image_eq_coeff_sum' {ι : Type u} [DecidableEq ι] (m : ι → M)
    (f : PolynomialMap R M N)
    (S : Type u) [CommRing S] [Algebra R S] (r : ι →₀ S) :
    f.toFun S (r.sum fun i a => a ⊗ₜ[R] m i) =
      (coeff (fun i : r.support => m i) f).sum
        (fun k n =>
          (r.support.prod
            (fun i => r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i) )
           ⊗ₜ[R] n)) := by
  rw [Finsupp.sum]
  rw [image_eq_coeff_finset_sum]
#align polynomial_map.image_eq_coeff_sum' PolynomialMap.image_eq_coeff_sum'

variable {S : Type _} [CommRing S] [Algebra R S]

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
    suffices : r ⊗ₜ[R] m = r • (1 : S) ⊗ₜ[R] m
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
  suffices hp : p ∈ Submodule.span S (Set.range fun s => 1 ⊗ₜ[R] m s)
  simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
  obtain ⟨r, rfl⟩ := hp
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)]
  rw [image_eq_coeff_sum m f]
  simp only [image_eq_coeff_sum, h]
  . intro i _
    simp only [smul_eq_mul, _root_.mul_one, TensorProduct.zero_tmul]
  . rw [PolynomialMap.span_tensorProduct_eq_top_of_span_eq_top ι m hm]
    exact Submodule.mem_top
#align polynomial_map.coeff_injective PolynomialMap.coeff_injective

noncomputable def Finsupp.polynomialMap (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
  PolynomialMap R M N where
  toFun S _ _ x :=
    h.sum fun k n =>
      (Finset.univ.prod fun i => (LinearForm.baseChange R S _ (b.coord i)) x ^ k i) ⊗ₜ[R] n
  isCompat φ := by
    ext m
    dsimp
    simp only [Finsupp.sum]
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
#align polynomial_map.finsupp.polynomial_map PolynomialMap.Finsupp.polynomialMap

theorem Finsupp.polynomialMap_toFun_apply (b : Basis ι R M)
    (h : (ι →₀ ℕ) →₀ N) (m : S ⊗[R] M) :
  (Finsupp.polynomialMap b h).toFun S m =
    h.sum fun k n =>
      (Finset.univ.prod
        (fun i => (LinearForm.baseChange R S _ (b.coord i)) m ^ k i)) ⊗ₜ[R] n :=
  rfl
#align polynomial_map.finsupp.polynomial_map_to_fun_apply PolynomialMap.Finsupp.polynomialMap_toFun_apply

example (f g : ι → ℕ) (i : ι) : (f + g) i = f i + g i :=
  Pi.add_apply f g i

theorem coeff_of_finsupp_polynomialMap [DecidableEq ι]
    (b : Basis ι R M) (h : (ι →₀ ℕ) →₀ N) :
  coeff (FunLike.coe b) (Finsupp.polynomialMap b h) = h := by
  simp only [coeff, coe_mk, AddHom.coe_mk]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  dsimp [Finsupp.polynomialMap, generize]
  apply congr_arg
  ext k
  apply congr_arg₂ _ _ rfl
  rw [MvPolynomial.monomial_eq]
  simp
  apply congr_arg
  ext i
  congr
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  simp [LinearForm.baseChange]
  intro j _ hij
  simp only [LinearForm.baseChange_apply_tmul]
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [if_neg hij]
  simp only [zero_smul, MulZeroClass.mul_zero]
#align polynomial_map.coeff_of_finsupp_polynomial_map PolynomialMap.coeff_of_finsupp_polynomialMap

theorem finsupp_polynomialMap_of_coeff [DecidableEq ι]
    (b : Basis ι R M) (f : PolynomialMap R M N) :
  Finsupp.polynomialMap b (coeff (FunLike.coe b) f) = f := by
  apply coeff_injective (FunLike.coe b)
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
    simp only [Finsupp.polynomialMap_toFun_apply, add_def, Pi.add_apply]
    rw [Finsupp.sum_of_support_subset h (h.support.subset_union_left k.support)]
    rw [Finsupp.sum_of_support_subset k (h.support.subset_union_right k.support)]
    rw [Finsupp.sum_of_support_subset (h + k) Finsupp.support_add]
    simp_rw [Finsupp.coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [Finset.sum_add_distrib]
    all_goals intro i hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    ext S _ _ m
    -- rw [ext_iff]; ext R _ _ m; skip
    simp only [RingHom.id_apply, smul_def, Pi.smul_apply]
    simp [Finsupp.polynomialMap_toFun_apply]
    rw [Finsupp.sum_of_support_subset (a • h) Finsupp.support_smul]
    simp only [Finsupp.sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Finsupp.coe_smul, Pi.smul_apply, TensorProduct.tmul_smul]
    intro k _; rw [TensorProduct.tmul_zero]
  invFun f := coeff (FunLike.coe b) f
  left_inv h := by dsimp; rw [coeff_of_finsupp_polynomialMap]
  right_inv f := by dsimp; rw [finsupp_polynomialMap_of_coeff b]
#align polynomial_map.coeff_polynomial_map_equiv PolynomialMap.coeffPolynomialMapEquiv

end Coefficients

end PolynomialMap