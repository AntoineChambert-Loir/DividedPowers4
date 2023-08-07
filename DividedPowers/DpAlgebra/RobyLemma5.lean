import DividedPowers.DpAlgebra.RobyLemma9
import Mathlib.RingTheory.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace Algebra.TensorProduct

open scoped TensorProduct

local notation:100 M " ⊗[" R "] " N:100 => TensorProduct R M N

variable {A : Type _} [CommRing A] 
  {R S R' S' : Type _} [CommRing R] [CommRing S] [CommRing R'][CommRing S'] 
  [Algebra A R] [Algebra A S] [Algebra A R'] [Algebra A S'] 
  (f : R →ₐ[A] R')
  (g : S →ₐ[A] S')

private def I : Ideal (R ⊗[A] S) :=
  f.toRingHom.ker.map (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S) ⊔
    g.toRingHom.ker.map (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S)

private theorem I_le_ker : 
  I f g ≤ RingHom.ker (Algebra.TensorProduct.map f g) := by
  simp only [I, sup_le_iff, Ideal.map_le_iff_le_comap]
  constructor
  intro x hx
  simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, AlgHom.coe_toRingHom] at hx 
  rw [Ideal.mem_comap, Algebra.TensorProduct.includeLeft_apply, RingHom.mem_ker,
    Algebra.TensorProduct.map_tmul, map_one, hx, TensorProduct.zero_tmul]
  intro y hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, AlgHom.coe_toRingHom] at hy 
  rw [Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, RingHom.mem_ker,
    Algebra.TensorProduct.map_tmul, map_one, hy, TensorProduct.tmul_zero]

variable {f}

private noncomputable def inv_f_fun (hf : Function.Surjective f) :
  R' → (R ⊗[A] S) ⧸ (I f g) := fun r' => 
  Ideal.Quotient.mkₐ A (I f g) 
    (@Algebra.TensorProduct.includeLeft A _ R _ _ S _ _ 
      (hf r').choose)


private theorem hinv_f (hf : Function.Surjective f) :
    ∀ r,
      (inv_f_fun g hf) (f r) = Ideal.Quotient.mkₐ A (I f g) (Algebra.TensorProduct.includeLeft (R := A) (A := R) (B := S) r) :=
  by
  intro r
  simp only [inv_f_fun]
  dsimp
  rw [Ideal.Quotient.eq]
  rw [← TensorProduct.sub_tmul]
  simp only [I]
  apply Ideal.mem_sup_left
  apply Ideal.mem_map_of_mem
  rw [RingHom.mem_ker, map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    (hf (f r)).choose_spec, sub_self]

lemma inv_f_map_add' (hf : Function.Surjective f) : ∀ x' y',
  inv_f_fun g hf (x' + y') = inv_f_fun g hf x' + inv_f_fun g hf y' := by
  intro x' y'
  obtain ⟨x : R, rfl⟩ := hf x' 
  obtain ⟨y : R, rfl⟩ := hf y'
  rw [← f.map_add]
  simp only [hinv_f g hf]
  apply congr_arg
  rw [map_add]

lemma inv_f_map_mul' (hf : Function.Surjective f) : ∀ x' y',
  inv_f_fun g hf (x' * y') = inv_f_fun g hf x' * inv_f_fun g hf y' := by
  intro x' y'
  obtain ⟨x : R, rfl⟩ := hf x' 
  obtain ⟨y : R, rfl⟩ := hf y'
  rw [← f.map_mul]
  simp only [hinv_f g hf]
  apply congr_arg
  rw [map_mul]

lemma inv_f_map_one' (hf : Function.Surjective f) :
  inv_f_fun g hf 1 = 1 := by 
  rw [← f.map_one, hinv_f g hf]
  exact map_one (Ideal.Quotient.mkₐ A (I f g))

lemma inv_f_map_zero' (hf : Function.Surjective f) :
  inv_f_fun g hf 0 = 0 := by 
  rw [← f.map_zero]
  simp only [hinv_f g hf]
  apply congr_arg
  rw [map_zero]

lemma inv_f_commutes' (hf : Function.Surjective f) (a : A) :
  inv_f_fun g hf (algebraMap A R' a) = algebraMap A _ a := by
  rw [← f.commutes a, hinv_f g hf]
  rw [Algebra.TensorProduct.includeLeft.commutes]
  rw [(Ideal.Quotient.mkₐ A (I f g)).commutes]


private noncomputable def inv_f (hf : Function.Surjective f) : 
  R' →ₐ[A] R ⊗[A] S ⧸ (I f g) := {
  toFun := inv_f_fun g hf
  map_one' := inv_f_map_one' g hf
  map_add' := inv_f_map_add' g hf
  map_mul' := inv_f_map_mul' g hf
  map_zero' := inv_f_map_zero' g hf 
  commutes' := inv_f_commutes' g hf }

variable (f)

variable {g}

private noncomputable def inv_g_fun (hg : Function.Surjective g) := fun s =>
  Ideal.Quotient.mkₐ A (I f g) (Algebra.TensorProduct.includeRight (hg s).some)

private theorem hinv_g (hg : Function.Surjective g) :
    ∀ s,
      (invGFun f hg) (g s) = Ideal.Quotient.mkₐ A (i f g) (Algebra.TensorProduct.includeRight s) :=
  by
  intro s
  simp only [inv_g_fun]
  dsimp
  rw [Ideal.Quotient.eq]
  rw [← TensorProduct.tmul_sub]
  simp only [I]
  apply Ideal.mem_sup_right
  apply Ideal.mem_map_of_mem
  rw [RingHom.mem_ker, map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    (hg (g s)).choose_spec, sub_self]

private noncomputable def inv_g (hg : Function.Surjective g) : S' →ₐ[A] R ⊗[A] S ⧸ i f g
    where
  toFun := invGFun f hg
  map_one' := by rw [← g.map_one, hinv_g f hg] <;> exact map_one (Ideal.Quotient.mkₐ A (I f g))
  map_mul' x' y' := by
    obtain ⟨x, rfl⟩ := hg x'; obtain ⟨y, rfl⟩ := hg y'
    rw [← map_mul]
    simp only [hinv_g f hg]
    rw [← map_mul]; apply congr_arg; rw [map_mul]
  map_add' x' y' := by
    obtain ⟨x, rfl⟩ := hg x'; obtain ⟨y, rfl⟩ := hg y'
    rw [← g.map_add]
    simp only [hinv_g f hg]
    rw [← map_add]; apply congr_arg; rw [map_add]
  map_zero' := by rw [← g.map_zero, hinv_g f hg]; apply congr_arg; rw [map_zero]
  commutes' a := by
    rw [← g.commutes a, hinv_g f hg]
    rw [Algebra.TensorProduct.includeRight.commutes]
    rw [(Ideal.Quotient.mkₐ A (I f g)).commutes]

variable {f g}

private theorem hinv_f_tens_g (hf : Function.Surjective f) (hg : Function.Surjective g) (r : R)
    (s : S) : (invF g hf) (f r) * (invG f hg) (g s) = (Ideal.Quotient.mk (i f g)) (r ⊗ₜ[A] s) :=
  by
  simp only [inv_f, inv_g]
  dsimp
  rw [hinv_f g hf]; rw [hinv_g f hg]; rw [← map_mul]
  rw [Ideal.Quotient.mkₐ_eq_mk]
  apply congr_arg
  simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one r, _root_.one_mul s]

/- example (hf : function.surjective f) (hg : function.surjective g)  : 
function.left_inverse (algebra.tensor_product.product_map
  (inv_f f g hf) (inv_g f g hg)) id := sorry
 -/
--set_option profiler true
-- Roby, lemma 5
theorem ker_tens (hf : Function.Surjective f) (hg : Function.Surjective g) :
    RingHom.ker (Algebra.TensorProduct.map f g) =
      f.toRingHom.ker.map (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S) ⊔
        g.toRingHom.ker.map (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S) :=
  by
  rw [← I]
  -- change _ = I f g,
  rw [AlgHom.ker_eq_ideal_iff]
  use I_le_ker f g
  suffices : Function.LeftInverse (Algebra.TensorProduct.productMap (inv_f g hf) (inv_g f hg)) _
  apply Function.LeftInverse.injective this
  --sorry,
  rw [Function.leftInverse_iff_comp, ← AlgHom.coe_comp, ← AlgHom.coe_id A]
  /- have : @id (R ⊗[A] S ⧸ I f g) = alg_hom.id A _, 
    { ext, rw alg_hom.id_apply, refl, },
    rw this,
     -/
  apply congr_arg
  apply Ideal.Quotient.algHom_ext
  apply FunLike.coe_injective
  simp only [AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_comp]
  rw [← Ideal.Quotient.mkₐ_eq_mk A (I f g)]
  simp only [← AlgHom.coe_comp]
  apply congr_arg
  apply Algebra.TensorProduct.ext
  intro r s
  simp only [AlgHom.comp_apply]
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk (I f g) _ _,
    AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.productMap_apply_tmul]
  exact hinv_f_tens_g hf hg r s
#align algebra.tensor_product.ker_tens Algebra.TensorProduct.ker_tens

end Algebra.TensorProduct

