/- Copyright ACL & MIdFF 2025 -/

--import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

namespace TensorProduct

variable {ι R S T N P M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [CommSemiring S] [Algebra R S]
    [CommSemiring T] [Algebra R T] [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]

lemma prodRight_rTensor_fst_eq_rTensor_prodRight (ψ : N →ₗ[R] P) (m : N ⊗[R] (M₁ × M₂)) :
    ((prodRight R S P M₁ M₂) ((LinearMap.rTensor (M₁ × M₂) ψ) m)).fst =
      LinearMap.rTensor M₁ ψ (prodRight R S N M₁ M₂ m).fst := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add] at hx hy ⊢
    rw [hx, hy]
  | tmul t m => simp

lemma prodRight_rTensor_snd_eq_rTensor_prodRight (ψ : N →ₗ[R] P) (m : N ⊗[R] (M₁ × M₂)) :
    ((prodRight R S P M₁ M₂) ((LinearMap.rTensor (M₁ × M₂) ψ) m)).snd =
      LinearMap.rTensor M₂ ψ (prodRight R S N M₁ M₂ m).snd := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Prod.snd_add] at hx hy ⊢
    rw [hx, hy]
  | tmul t m => simp

variable (R S N)

-- **MI** : I am not sure about whether we want these `coe` lemmas to be `simp`.

--@[simp]
lemma coe_prodRight : ⇑(prodRight R S N M₁ M₂) = (prodRight R R N M₁ M₂) := rfl

--@[simp]
lemma coe_prodRight_symm :
    ⇑(prodRight R S N M₁ M₂).symm = (prodRight R R N M₁ M₂).symm := by
  ext d
  simp [LinearEquiv.symm_apply_eq, coe_prodRight, LinearEquiv.apply_symm_apply]

-- I tried to avoid the next one, but with no success (TODO)
lemma prodRight_rTensor_fst_eq_rTensor_prodRight' (ψ : T →ₐ[R] S) (m : T ⊗[R] (M₁ × M₂)) :
    ((prodRight R S S M₁ M₂) ((LinearMap.rTensor (M₁ × M₂) ψ.toLinearMap) m)).fst =
      LinearMap.rTensor M₁ ψ.toLinearMap (prodRight R T T M₁ M₂ m).fst := by
  simp [prodRight_rTensor_fst_eq_rTensor_prodRight, coe_prodRight]

-- I tried to avoid the next one, but with no success (TODO)
lemma prodRight_rTensor_snd_eq_rTensor_prodRight' (ψ : T →ₐ[R] S) (m : T ⊗[R] (M₁ × M₂)) :
    ((prodRight R S S M₁ M₂) ((LinearMap.rTensor (M₁ × M₂) ψ.toLinearMap) m)).snd =
      LinearMap.rTensor M₂ ψ.toLinearMap (prodRight R T T M₁ M₂ m).snd := by
  simp [prodRight_rTensor_snd_eq_rTensor_prodRight, coe_prodRight]

variable {R S N}

@[simp]
lemma prodRight_symm_zero : ((prodRight R S N M₁ M₂).symm (0, 0)) = 0 := by simp

lemma smul_tmul_fst_eq (r : S × S) (s : S) (m : M₁ × M₂) :
    r.1 • s ⊗ₜ[R] m.1 = ((prodRight R S S M₁ M₂) (r.1 • s ⊗ₜ[R] (m.1, 0))).1 := by simp

lemma smul_tmul_snd_eq (r : S × S) (s : S) (m : M₁ × M₂) :
    r.2 • s ⊗ₜ[R] m.2 = ((prodRight R S S M₁ M₂) (r.2 • s ⊗ₜ[R] (0, m.2))).2 := by simp

-- Might not be needed
theorem smul_prodRight_fst_apply (sm : S ⊗[R] (M₁ × M₂)) (r : S × S) :
    (r.1 • (prodRight R S S M₁ M₂) sm).1 =
      (r.1 • (prodRight R S S M₁ M₂ sm).1, r.2 • (prodRight R S S M₁ M₂ sm).2).1 := by simp

-- Might not be needed
theorem smul_prodRight_snd_apply (sm : S ⊗[R] (M₁ × M₂)) (r : S × S) :
    (r.2 • (prodRight R S S M₁ M₂) sm).2 =
      (r.1 • (prodRight R S S M₁ M₂ sm).1, r.2 • (prodRight R S S M₁ M₂ sm).2).2 := by simp

-- Might not be needed
theorem smul_const_prodRight_apply (sm : S ⊗[R] (M₁ × M₂)) (r : S) :
    r • (prodRight R S S M₁ M₂) sm = (prodRight R S S M₁ M₂) (r • sm) := by simp

variable (R S N M₁ M₂) in
@[irreducible]
def fstRight : N ⊗[R] (M₁ × M₂) →ₗ[S] N ⊗[R] M₁ :=
  (LinearMap.fst _ _ _).comp (prodRight R S N M₁ M₂).toLinearMap

variable (R S N M₁ M₂) in
@[irreducible]
def sndRight : N ⊗[R] (M₁ × M₂) →ₗ[S] N ⊗[R] M₂ :=
  (LinearMap.snd _ _ _).comp (prodRight R S N M₁ M₂).toLinearMap

lemma prodRight_eq_prod_fstRight_sndRight :
    (prodRight R S N M₁ M₂).toLinearMap =
      LinearMap.prod (fstRight R S N M₁ M₂) (sndRight R S N M₁ M₂) := by
  simp only [fstRight, sndRight]
  rfl

lemma prodRight_symm_comp_prod_fstRight_sndRight :
    (prodRight R S N M₁ M₂).symm.toLinearMap.comp
      (LinearMap.prod (fstRight R S N M₁ M₂) (sndRight R S N M₁ M₂)) = LinearMap.id := by
  rw [← prodRight_eq_prod_fstRight_sndRight, LinearEquiv.symm_comp]

lemma prodRight_symm_comp_prod_fstRight_sndRight_apply (x : N ⊗[R] (M₁ × M₂)) :
    (prodRight R S N M₁ M₂).symm (LinearMap.prod (fstRight R S N M₁ M₂) (sndRight R S N M₁ M₂) x) =
      x := by
  erw [← LinearMap.comp_apply, prodRight_symm_comp_prod_fstRight_sndRight, LinearMap.id_apply]

lemma fstRight_prodRight_apply (f : (N ⊗[R] M₁) × (N ⊗[R] M₂))  :
    (fstRight R S N M₁ M₂) ((prodRight R S N M₁ M₂).symm f) = f.fst := by
  simp [fstRight]

lemma sndRight_prodRight_apply (f : (N ⊗[R] M₁) × (N ⊗[R] M₂))  :
    (sndRight R S N M₁ M₂) ((prodRight R S N M₁ M₂).symm f) = f.snd := by
  simp [sndRight]

lemma fstRight_prodRight :
    (fstRight R S N M₁ M₂).comp (prodRight R S N M₁ M₂).symm.toLinearMap = LinearMap.fst _ _ _ :=
  LinearMap.ext_iff.mpr fstRight_prodRight_apply

lemma sndRight_prodRight :
    (sndRight R S N M₁ M₂).comp (prodRight R S N M₁ M₂).symm.toLinearMap = LinearMap.snd _ _ _ :=
  LinearMap.ext_iff.mpr sndRight_prodRight_apply

variable (R S N M₁ M₂) in
@[irreducible]
def inlRight : N ⊗[R] M₁ →ₗ[S] N ⊗[R] (M₁ × M₂) :=
  (prodRight R S N M₁ M₂).symm.toLinearMap.comp (LinearMap.inl S (N ⊗[R] M₁) (N ⊗[R] M₂))

variable (R S N M₁ M₂) in
@[irreducible]
def inrRight : N ⊗[R] M₂ →ₗ[S] N ⊗[R] (M₁ × M₂) :=
  (prodRight R S N M₁ M₂).symm.toLinearMap.comp (LinearMap.inr S (N ⊗[R] M₁) (N ⊗[R] M₂))

lemma inlRight_tmul (n : N) (m : M₁) : inlRight R S N M₁ M₂ (n ⊗ₜ m) = n ⊗ₜ (m, 0) := by
  simp only [inlRight, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inl,
    Function.comp_apply]
  rw [← tmul_zero _ n, prodRight_symm_tmul]

lemma inrRight_tmul (n : N) (m : M₂) : inrRight R S N M₁ M₂ (n ⊗ₜ m) = n ⊗ₜ (0, m) := by
  simp only [inrRight, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    Function.comp_apply]
  rw [← tmul_zero _ n, prodRight_symm_tmul]

lemma fstRight_inlRight_eq (nm : N ⊗[R] M₁) :
    (fstRight R S N M₁ M₂) (inlRight R S N M₁ M₂ nm) = nm := by
  simp [fstRight, inlRight]

lemma fstRight_inrRight_eq (nm : N ⊗[R] M₂) :
    (fstRight R S N M₁ M₂) (inrRight R S N M₁ M₂ nm) = 0 := by
  simp [fstRight, inrRight]

lemma sndRight_inrRight_eq (nm : N ⊗[R] M₂) :
    (sndRight R S N M₁ M₂) (inrRight R S N M₁ M₂ nm) = nm := by
  simp [sndRight, inrRight]

lemma sndRight_inlRight_eq (nm : N ⊗[R] M₁) :
    (sndRight R S N M₁ M₂) (inlRight R S N M₁ M₂ nm) = 0 := by
  simp [sndRight, inlRight]

lemma fstRight_inlRight : (fstRight R S N M₁ M₂).comp (inlRight R S N M₁ M₂) = LinearMap.id :=
  LinearMap.ext_iff.mpr fstRight_inlRight_eq

lemma sndRight_inrRight : (sndRight R S N M₁ M₂).comp (inrRight R S N M₁ M₂) = LinearMap.id :=
  LinearMap.ext_iff.mpr sndRight_inrRight_eq

variable (S) in
lemma prod_right_ext_iff {x y : N ⊗[R] (M₁ × M₂)} :
    x = y ↔ (fstRight R S N M₁ M₂ x = fstRight R S N M₁ M₂ y) ∧
      (sndRight R S N M₁ M₂ x = sndRight R S N M₁ M₂ y) := by
  simp_rw [← (prodRight R R N M₁ M₂).injective.eq_iff, fstRight, sndRight]
  conv_rhs => simp only [LinearMap.coe_comp, LinearMap.coe_fst, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.coe_snd]
  exact Prod.ext_iff

variable (R S N M₁ M₂) in
@[irreducible] def compFstRight : N ⊗[R] (M₁ × M₂) →ₗ[S] N ⊗[R] (M₁ × M₂) :=
  (inlRight R S N M₁ M₂).comp (fstRight R S N M₁ M₂)

variable (R S N M₁ M₂) in
@[irreducible] def compSndRight : N ⊗[R] (M₁ × M₂) →ₗ[S] N ⊗[R] (M₁ × M₂) :=
  (inrRight R S N M₁ M₂).comp (sndRight R S N M₁ M₂)

lemma compFstRight_add_compSndRight (nm : N ⊗[R] (M₁ × M₂)) :
    compFstRight R S N M₁ M₂ nm + compSndRight R S N M₁ M₂ nm = nm := by
  simp [prod_right_ext_iff S, compFstRight, compSndRight, fstRight_inlRight_eq,
    fstRight_inrRight_eq, sndRight_inlRight_eq, sndRight_inrRight_eq]

lemma compFstRight_tmul (n : N) (m : M₁ × M₂) :
    (compFstRight R S N M₁ M₂ (n ⊗ₜ m)) = inlRight R S N M₁ M₂ (n ⊗ₜ m.1) := by
  simp [compFstRight, inlRight, fstRight]

lemma compSndRight_tmul (n : N) (m : M₁ × M₂) :
    (compSndRight R S N M₁ M₂ (n ⊗ₜ m)) = inrRight R S N M₁ M₂ (n ⊗ₜ m.2) := by
  simp [compSndRight, inrRight, sndRight]

lemma compFstRight_prodRight_tmul (n : N × N) (m : M₁ × M₂) :
    (compFstRight R S N M₁ M₂ ((prodRight R S N M₁ M₂).symm (n.1 ⊗ₜ m.1, n.2 ⊗ₜ m.2))) =
      inlRight R S N M₁ M₂ (n.1 ⊗ₜ m.1) := by
  simp [compFstRight, inlRight, fstRight]

lemma compSndRight_prodRight_tmul (n : N × N) (m : M₁ × M₂) :
    (compSndRight R S N M₁ M₂ ((prodRight R S N M₁ M₂).symm (n.1 ⊗ₜ m.1, n.2 ⊗ₜ m.2))) =
      inrRight R S N M₁ M₂ (n.2 ⊗ₜ m.2) := by
  simp [compSndRight, inrRight, sndRight]

lemma compFstRight_inlRight_eq (nm : N ⊗[R] M₁):
    (compFstRight R S N M₁ M₂) (inlRight R S N M₁ M₂ nm) = (inlRight R S N M₁ M₂ nm) := by
  simp [compFstRight, inlRight, fstRight]

lemma compSndRight_inrRight_eq (nm : N ⊗[R] M₂):
    (compSndRight R S N M₁ M₂) (inrRight R S N M₁ M₂ nm) = (inrRight R S N M₁ M₂ nm) := by
  simp [compSndRight, inrRight, sndRight]

lemma compFstRight_inrRight_eq (nm : N ⊗[R] M₂):
    (compFstRight R S N M₁ M₂) (inrRight R S N M₁ M₂ nm) = 0 := by
  simp [compFstRight, inrRight, fstRight]

lemma compSndRight_inlRight_eq (nm : N ⊗[R] M₁):
    (compSndRight R S N M₁ M₂) (inlRight R S N M₁ M₂ nm) = 0 := by
  simp [compSndRight, inlRight, sndRight]

lemma fstRight_compFstRight_eq (nm : N ⊗[R] (M₁ × M₂)) :
    fstRight R S N M₁ M₂ (compFstRight R S N M₁ M₂ nm) = fstRight R S N M₁ M₂ nm := by
  simp [compFstRight, fstRight, inlRight]

lemma fstRight_compSndRight_eq (nm : N ⊗[R] (M₁ × M₂)) :
    fstRight R S N M₁ M₂ (compSndRight R S N M₁ M₂ nm) = 0 := by
  simp [compSndRight, fstRight, inrRight]

lemma sndRight_compSndRight_eq (nm : N ⊗[R] (M₁ × M₂)) :
    sndRight R S N M₁ M₂ (compSndRight R S N M₁ M₂ nm) = sndRight R S N M₁ M₂ nm := by
  simp [compSndRight, sndRight, inrRight]

lemma sndRight_compFstRight_eq (nm : N ⊗[R] (M₁ × M₂)) :
    sndRight R S N M₁ M₂ (compFstRight R S N M₁ M₂ nm) = 0 := by
  simp [compFstRight, sndRight, inlRight]

lemma fstRight_compFstRight_prodRight_tmul (n : N × N) (m : M₁ × M₂) :
    fstRight R S N M₁ M₂ (compFstRight R S N M₁ M₂ ((prodRight R S N M₁ M₂).symm
      (n.1 ⊗ₜ m.1, n.2 ⊗ₜ m.2))) = n.1 ⊗ₜ m.1 := by
  simp [compFstRight, fstRight, inlRight]

lemma fstRight_compSndRight_prodRight_tmul (n : N × N) (m : M₁ × M₂) :
    fstRight R S N M₁ M₂ (compSndRight R S N M₁ M₂ ((prodRight R S N M₁ M₂).symm
      (n.1 ⊗ₜ m.1, n.2 ⊗ₜ m.2))) = 0 := by
  simp [compSndRight, fstRight, inrRight]

lemma sndRight_compSndRight_prodRight_tmul (n : N × N) (m : M₁ × M₂) :
    sndRight R S N M₁ M₂ (compSndRight R S N M₁ M₂ ((prodRight R S N M₁ M₂).symm
      (n.1 ⊗ₜ m.1, n.2 ⊗ₜ m.2))) = n.2 ⊗ₜ m.2 := by
  simp [compSndRight, sndRight, inrRight]

lemma sndRight_compFstRight_prodRight_tmul (n : N × N) (m : M₁ × M₂) :
    sndRight R S N M₁ M₂ (compFstRight R S N M₁ M₂ ((prodRight R S N M₁ M₂).symm
      (n.1 ⊗ₜ m.1, n.2 ⊗ₜ m.2))) = 0 := by
  simp [compFstRight, sndRight, inlRight]

theorem rTensor_inlRight_eq_inlRight_rTensor (ψ : T →ₐ[R] S) (p : T ⊗[R] M₁) :
    (LinearMap.rTensor (M₁ × M₂) ψ.toLinearMap) ((inlRight R R T M₁ M₂) p) =
    (inlRight R R S M₁ M₂) ((LinearMap.rTensor M₁ ψ.toLinearMap) p) := by
  simp only [inlRight, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inl,
    Function.comp_apply]
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq =>
    rw [← Prod.mk_zero_add_mk_zero]
    simp only [map_add, hp, hq]
    simp only [← map_add, Prod.mk_add_mk, add_zero]
  | tmul p m =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    rw [← tmul_zero _ (ψ p), ← tmul_zero _ p]
    simp only [prodRight_symm_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]

theorem rTensor_inrRight_eq_inrRight_rTensor (ψ : T →ₐ[R] S) (p : T ⊗[R] M₂) :
    (LinearMap.rTensor (M₁ × M₂) ψ.toLinearMap) ((inrRight R R T M₁ M₂) p) =
      (inrRight R R S M₁ M₂) ((LinearMap.rTensor M₂ ψ.toLinearMap) p) := by
  simp only [inrRight, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    Function.comp_apply]
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq =>
    rw [← Prod.zero_mk_add_zero_mk]
    simp only [map_add, hp, hq]
    simp only [← map_add, Prod.mk_add_mk, add_zero]
  | tmul p m =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    rw [← tmul_zero _ (ψ p), ← tmul_zero _ p]
    simp only [prodRight_symm_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]

end TensorProduct
