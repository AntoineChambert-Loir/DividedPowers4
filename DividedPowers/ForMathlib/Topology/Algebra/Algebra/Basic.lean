import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!

# Topological algebras

A topological algebra `S` over a commutative topological ring `R` is an `R`-algebra `S`
which is a topological ring and such that the algebra map from `R` to `S` is continuous.

-/

universe u v

open Set Filter TopologicalSpace Function Topology Filter BigOperators

section TopologicalAlgebra

/-- A topological algebra `S` over a commutative topological semiring `R` is an `R`-algebra `S`
  which is a topological semiring and such that the algebra map from `R` to `S` is continuous. -/
class TopologicalAlgebra (R : Type u) (A : Type v) [CommSemiring R] [TopologicalSpace R]
    [TopologicalSemiring R] [Semiring A] [TopologicalSpace A] [TopologicalSemiring A] extends
    Algebra R A where
  continuous_algebraMap : Continuous (algebraMap R A)

variable (R : Type u) (A : Type v) [CommSemiring R] [TopologicalSpace R]
    [TopologicalSemiring R] [Semiring A] [TopologicalSpace A] [TopologicalSemiring A]

/-- If `R` is a discrete topological ring,
  then any topological ring `S` which is an `R`-algebra
  is also a topological `R`-algebra. -/
instance DiscreteTopology.topologicalAlgebra [DiscreteTopology R] [Algebra R A] :
    TopologicalAlgebra R A :=
  { (inferInstance : Algebra R A) with
    continuous_algebraMap := continuous_of_discreteTopology }

namespace Subalgebra

variable [TopologicalAlgebra R A]
/-- An `R`-subalgebra `S` of `A` is a topological algebra (with the subspace topology). -/
instance topologicalAlgebra (S : Subalgebra R A) :
    TopologicalAlgebra R S where
  continuous_algebraMap := by
    rw [inducing_subtype_val.continuous_iff]
    suffices Subtype.val ∘ (algebraMap R S) = algebraMap R A by
      erw [this]
      exact TopologicalAlgebra.continuous_algebraMap
    rfl

end Subalgebra

section Prod

/-- The product topology on the cartesian product of two topological algebras
  makes the product into a topological algebra. -/
instance [TopologicalAlgebra R A] {B : Type*} [Semiring B] [TopologicalSpace B]
    [TopologicalSemiring B] [TopologicalAlgebra R B] : TopologicalAlgebra R (A × B) :=
{ (inferInstance : Algebra R (A × B)) with
  continuous_algebraMap := continuous_prod_mk.mpr
    ⟨TopologicalAlgebra.continuous_algebraMap, TopologicalAlgebra.continuous_algebraMap⟩ }

end Prod

section Pi

/-- The product topology on the cartesian product of two topological algebras
  makes the product into a topological algebra. -/
instance Pi.topologicalAlgebra {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
  [∀ b, Semiring (C b)] [∀ b, TopologicalSemiring (C b)] [∀ b, TopologicalAlgebra R (C b)] :
  TopologicalAlgebra R (Π b , C b) :=
{ toAlgebra := Pi.algebra _ _
  continuous_algebraMap :=
    continuous_pi_iff.mpr fun _ =>  TopologicalAlgebra.continuous_algebraMap }

end Pi

section
/-- Continuous algebra homomorphisms between algebras. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological algebras over the topological
ring `R`. -/
structure ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [TopologicalSpace A]
    [Semiring A] (B : Type*) [TopologicalSpace B] [Semiring B] [Algebra R A] [Algebra R B]
    extends A →ₐ[R] B where
  cont : Continuous toFun := by continuity

/-- `ContinuousAlgHomClass F R A B` asserts `F` is a type of bundled continuous `R`-agebra
  homomorphisms `A → B`. -/
class ContinuousAlgHomClass (F : Type*) (R : outParam (Type*)) [CommSemiring R]
    (A : outParam (Type*)) [TopologicalSpace A] [Semiring A]
    (B : outParam (Type*)) [TopologicalSpace B] [Semiring B] [Algebra R A]
    [Algebra R B] [FunLike F A B]
    extends AlgHomClass F R A B, ContinuousMapClass F A B : Prop
attribute [inherit_doc ContinuousAlgHom] ContinuousAlgHom.cont

@[inherit_doc]
notation:25 A " →A[" R "] " B => ContinuousAlgHom R A B

variable {R : Type*} [CommSemiring R] {A : Type*} [TopologicalSpace A]
    [Semiring A] {B : Type*} [TopologicalSpace B] [Semiring B] [Algebra R A] [Algebra R B]

namespace ContinuousAlgHom

section Semiring

attribute [coe] ContinuousAlgHom.toAlgHom
/-- Coerce continuous linear maps to linear maps. -/
instance AlgHom.coe : Coe (A →A[R] B) (A →ₐ[R] B) := ⟨toAlgHom⟩

theorem coe_injective : Function.Injective ((↑) : (A →A[R] B) → A →ₐ[R] B) := by
  intro f g H
  cases f
  cases g
  congr

instance funLike : FunLike (A →A[R] B) A B where
  coe f := f.toAlgHom
  coe_injective'  _ _ h  := coe_injective (DFunLike.coe_injective h)

instance continuousAlgHomClass :
    ContinuousAlgHomClass (A →A[R] B) R A B where
      map_mul f x y    := map_mul f.toAlgHom x y
      map_one f        := map_one f.toAlgHom
      map_add f        := map_add f.toAlgHom
      map_zero f       := map_zero f.toAlgHom
      commutes f r     := f.toAlgHom.commutes r
      map_continuous f := f.2

theorem coe_mk (f : A →ₐ[R] B) (h) : (mk f h : A →ₐ[R] B) = f := rfl

@[simp]
theorem coe_mk' (f : A →ₐ[R] B) (h) : (mk f h : A → B) = f := rfl

@[continuity]
protected theorem continuous (f : A →A[R] B) : Continuous f := f.2


protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [Ring E₂] [Algebra R E₁] [Algebra R E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (f : E₁ →A[R] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
theorem coe_inj {f g : A →A[R] B} : (f : A →ₐ[R] B) = g ↔ f = g := coe_injective.eq_iff

theorem coeFn_injective : @Function.Injective (A →A[R] B) (A → B) (↑) := DFunLike.coe_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : A →A[R] B) : A → B := h

--TODO: Check if this is needed
/-- See Note [custom simps projection]. -/
def Simps.coe (h : A →A[R] B) : A →ₐ[R] B := h

initialize_simps_projections ContinuousAlgHom (toAlgHom_toFun → apply, toAlgHom → coe)

@[ext]
theorem ext {f g : A →A[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

theorem ext_iff {f g : A →A[R] B} : f = g ↔ ∀ x, f x = g x := DFunLike.ext_iff

/-- Copy of a `ContinuousAlgHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
def copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : A →A[R] B where
  toAlgHom := {
    toRingHom := (f : A →A[R] B).toRingHom.copy f' h
    commutes' := fun r => by
      simp only [AlgHom.toRingHom_eq_coe, h, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_copy, AlgHomClass.commutes f r] }
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
theorem coe_copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' := rfl

theorem copy_eq (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f := DFunLike.ext' h

-- make some straightforward lemmas available to `simp`.
protected theorem map_zero (f : A →A[R] B) : f (0 : A) = 0 := map_zero f

protected theorem map_add (f : A →A[R] B) (x y : A) : f (x + y) = f x + f y := map_add f x y

/- -- @[simp] -- Porting note (#10618): simp can prove this
protected theorem map_smulₛₗ (f : A →A[R] B) (c : R) (x : A) : f (c • x) =  c • f x :=
  (toLinearMap _).map_smulₛₗ _ _
#align continuous_linear_map.map_smulₛₗ ContinuousLinearMap.map_smulₛₗ -/

-- @[simp] -- Porting note (#10618): simp can prove this
protected theorem map_smul [Module R A] (f : A →A[R] B) (c : R) (x : A) :
    f (c • x) = c • f x := (toAlgHom _).map_smul _ _

@[simp]
theorem map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
    [Algebra S B] [SMulHomClass (A →A[S] B) R A B] (f : A →A[S] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul f c x

@[deprecated _root_.map_sum]
protected theorem map_sum {ι : Type*} (f : A →A[R] B) (s : Finset ι) (g : ι → A) :
    f (∑ i in s, g i) = ∑ i in s, f (g i) :=
  map_sum ..

@[simp, norm_cast]
theorem coe_coe (f : A →A[R] B) : ⇑(f : A →ₐ[R] B) = f := rfl

-- TODO: delete?
@[ext]
theorem ext_ring [TopologicalSpace R] {f g : R →A[R] A} : f = g := by
  apply coe_inj.1
  apply Algebra.ext_id

-- TODO: delete?
theorem ext_ring_iff [TopologicalSpace R] {f g : R →A[R] A} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

/-- If two continuous algebra maps are equal on a set `s`, then they are equal on the closure
of the `Submodule.span` of this set. -/
theorem eqOn_closure_span [T2Space B] {s : Set A} {f g : A →A[R] B} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R s : Set A)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
algebra maps equal on `s` are equal. -/
theorem ext_on [T2Space B] {s : Set A} (hs : Dense (Submodule.span R s : Set A))
    {f g : A →A[R] B} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)

/-- Under a continuous algebra map, the image of the `TopologicalClosure` of a submodule is
contained in the `TopologicalClosure` of its image. -/
theorem _root_.Submodule.topologicalClosure_map' [TopologicalSpace R] [ContinuousSMul R A]
    [ContinuousAdd A] [ContinuousSMul R B] [ContinuousAdd B] (f : A →A[R] B) (s : Submodule R A) :
    s.topologicalClosure.map (f : A →ₐ[R] B) ≤ (s.map (f : A →ₐ[R] B)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/-- Under a dense continuous algebra map, a submodule whose `TopologicalClosure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_submodule' [TopologicalSpace R]
    [ContinuousSMul R A] [ContinuousAdd A] [ContinuousSMul R B] [ContinuousAdd B] {f : A →A[R] B}
    (hf' : DenseRange f) {s : Submodule R A} (hs : s.topologicalClosure = ⊤) :
    (s.map (f : A →ₐ[R] B)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

end Semiring

section id

-- Q: Why are R and A implicit here?? #where indicates they are explicit...
/-- The identity map as a continuous algebra homomorphism. -/
def id : A →A[R] A := ⟨AlgHom.id R A, continuous_id⟩

instance one : One (A →A[R] A) := ⟨id⟩

theorem one_def : (1 : A →A[R] A) = id := rfl

theorem id_apply (x : A) : @id R _ A _ _ _ x = x := rfl

@[simp, norm_cast]
theorem coe_id : ((@id R _ A _ _ _) : A →ₐ[R] A) = AlgHom.id R A:= rfl

@[simp, norm_cast]
theorem coe_id' : ⇑(@id R _ A _ _ _ ) = _root_.id := rfl

@[simp, norm_cast]
theorem coe_eq_id {f : A →A[R] A} : (f : A →ₐ[R] A) = AlgHom.id R A ↔ f = id := by
  rw [← coe_id, coe_inj]

@[simp]
theorem one_apply (x : A) : (1 : A →A[R] A) x = x := rfl

end id

variable {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/-- Composition of continuous algebra homomorphisms. -/
def comp (g : B →A[R] C) (f : A →A[R] B) : A →A[R] C :=
  ⟨(g : B →ₐ[R] C).comp (f : A →ₐ[R] B), g.2.comp f.2⟩

@[simp, norm_cast]
theorem coe_comp (h : B →A[R] C) (f : A →A[R] B) :
    (h.comp f : A →ₐ[R] C) = (h : B →ₐ[R] C).comp (f : A →ₐ[R] B) := rfl

@[simp, norm_cast]
theorem coe_comp' (h : B →A[R] C) (f : A →A[R] B) : ⇑(h.comp f) = h ∘ f := rfl

#exit


theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
  rfl
#align continuous_linear_map.comp_apply ContinuousLinearMap.comp_apply

@[simp]
theorem comp_id (f : M₁ →SL[σ₁₂] M₂) : f.comp (id R₁ M₁) = f :=
  ext fun _x => rfl
#align continuous_linear_map.comp_id ContinuousLinearMap.comp_id

@[simp]
theorem id_comp (f : M₁ →SL[σ₁₂] M₂) : (id R₂ M₂).comp f = f :=
  ext fun _x => rfl
#align continuous_linear_map.id_comp ContinuousLinearMap.id_comp

@[simp]
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 := by
  ext
  simp
#align continuous_linear_map.comp_zero ContinuousLinearMap.comp_zero

@[simp]
theorem zero_comp (f : M₁ →SL[σ₁₂] M₂) : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 := by
  ext
  simp
#align continuous_linear_map.zero_comp ContinuousLinearMap.zero_comp

@[simp]
theorem comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f₁ f₂ : M₁ →SL[σ₁₂] M₂) : g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  ext
  simp
#align continuous_linear_map.comp_add ContinuousLinearMap.comp_add

@[simp]
theorem add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  ext
  simp
#align continuous_linear_map.add_comp ContinuousLinearMap.add_comp

theorem comp_assoc {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄}
    {σ₃₄ : R₃ →+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄) (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align continuous_linear_map.comp_assoc ContinuousLinearMap.comp_assoc

instance instMul : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩
#align continuous_linear_map.has_mul ContinuousLinearMap.instMul

theorem mul_def (f g : M₁ →L[R₁] M₁) : f * g = f.comp g :=
  rfl
#align continuous_linear_map.mul_def ContinuousLinearMap.mul_def

@[simp]
theorem coe_mul (f g : M₁ →L[R₁] M₁) : ⇑(f * g) = f ∘ g :=
  rfl
#align continuous_linear_map.coe_mul ContinuousLinearMap.coe_mul

theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) :=
  rfl
#align continuous_linear_map.mul_apply ContinuousLinearMap.mul_apply

instance monoidWithZero : MonoidWithZero (M₁ →L[R₁] M₁) where
  mul_zero f := ext fun _ => map_zero f
  zero_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl
#align continuous_linear_map.monoid_with_zero ContinuousLinearMap.monoidWithZero

theorem coe_pow (f : M₁ →L[R₁] M₁) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

instance instNatCast [ContinuousAdd M₁] : NatCast (M₁ →L[R₁] M₁) where
  natCast n := n • (1 : M₁ →L[R₁] M₁)

instance semiring [ContinuousAdd M₁] : Semiring (M₁ →L[R₁] M₁) where
  __ := ContinuousLinearMap.monoidWithZero
  __ := ContinuousLinearMap.addCommMonoid
  left_distrib f g h := ext fun x => map_add f (g x) (h x)
  right_distrib _ _ _ := ext fun _ => LinearMap.add_apply _ _ _
  toNatCast := instNatCast
  natCast_zero := zero_smul ℕ (1 : M₁ →L[R₁] M₁)
  natCast_succ n := AddMonoid.nsmul_succ n (1 : M₁ →L[R₁] M₁)
#align continuous_linear_map.semiring ContinuousLinearMap.semiring

/-- `ContinuousLinearMap.toLinearMap` as a `RingHom`. -/
@[simps]
def toLinearMapRingHom [ContinuousAdd M₁] : (M₁ →L[R₁] M₁) →+* M₁ →ₗ[R₁] M₁ where
  toFun := toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align continuous_linear_map.to_linear_map_ring_hom ContinuousLinearMap.toLinearMapRingHom
#align continuous_linear_map.to_linear_map_ring_hom_apply ContinuousLinearMap.toLinearMapRingHom_apply

@[simp]
theorem natCast_apply [ContinuousAdd M₁] (n : ℕ) (m : M₁) : (↑n : M₁ →L[R₁] M₁) m = n • m :=
  rfl

@[simp]
theorem ofNat_apply [ContinuousAdd M₁] (n : ℕ) [n.AtLeastTwo] (m : M₁) :
    ((no_index (OfNat.ofNat n) : M₁ →L[R₁] M₁)) m = OfNat.ofNat n • m :=
  rfl

section ApplyAction

variable [ContinuousAdd M₁]

/-- The tautological action by `M₁ →L[R₁] M₁` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyModule : Module (M₁ →L[R₁] M₁) M₁ :=
  Module.compHom _ toLinearMapRingHom
#align continuous_linear_map.apply_module ContinuousLinearMap.applyModule

@[simp]
protected theorem smul_def (f : M₁ →L[R₁] M₁) (a : M₁) : f • a = f a :=
  rfl
#align continuous_linear_map.smul_def ContinuousLinearMap.smul_def

/-- `ContinuousLinearMap.applyModule` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨fun {_ _} => ContinuousLinearMap.ext⟩
#align continuous_linear_map.apply_has_faithful_smul ContinuousLinearMap.applyFaithfulSMul

instance applySMulCommClass : SMulCommClass R₁ (M₁ →L[R₁] M₁) M₁ where
  smul_comm r e m := (e.map_smul r m).symm
#align continuous_linear_map.apply_smul_comm_class ContinuousLinearMap.applySMulCommClass

instance applySMulCommClass' : SMulCommClass (M₁ →L[R₁] M₁) R₁ M₁ where
  smul_comm := ContinuousLinearMap.map_smul
#align continuous_linear_map.apply_smul_comm_class' ContinuousLinearMap.applySMulCommClass'

instance continuousConstSMul_apply : ContinuousConstSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨ContinuousLinearMap.continuous⟩
#align continuous_linear_map.has_continuous_const_smul ContinuousLinearMap.continuousConstSMul_apply

end ApplyAction

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    M₁ →L[R₁] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R₁] M₂).prod f₂, f₁.2.prod_mk f₂.2⟩
#align continuous_linear_map.prod ContinuousLinearMap.prod

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R₁] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl
#align continuous_linear_map.coe_prod ContinuousLinearMap.coe_prod

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) (x : M₁) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl
#align continuous_linear_map.prod_apply ContinuousLinearMap.prod_apply

section

variable (R₁ M₁ M₂)

/-- The left injection into a product is a continuous linear map. -/
def inl [Module R₁ M₂] : M₁ →L[R₁] M₁ × M₂ :=
  (id R₁ M₁).prod 0
#align continuous_linear_map.inl ContinuousLinearMap.inl

/-- The right injection into a product is a continuous linear map. -/
def inr [Module R₁ M₂] : M₂ →L[R₁] M₁ × M₂ :=
  (0 : M₂ →L[R₁] M₁).prod (id R₁ M₂)
#align continuous_linear_map.inr ContinuousLinearMap.inr

end

variable {F : Type*}

@[simp]
theorem inl_apply [Module R₁ M₂] (x : M₁) : inl R₁ M₁ M₂ x = (x, 0) :=
  rfl
#align continuous_linear_map.inl_apply ContinuousLinearMap.inl_apply

@[simp]
theorem inr_apply [Module R₁ M₂] (x : M₂) : inr R₁ M₁ M₂ x = (0, x) :=
  rfl
#align continuous_linear_map.inr_apply ContinuousLinearMap.inr_apply

@[simp, norm_cast]
theorem coe_inl [Module R₁ M₂] : (inl R₁ M₁ M₂ : M₁ →ₗ[R₁] M₁ × M₂) = LinearMap.inl R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_inl ContinuousLinearMap.coe_inl

@[simp, norm_cast]
theorem coe_inr [Module R₁ M₂] : (inr R₁ M₁ M₂ : M₂ →ₗ[R₁] M₁ × M₂) = LinearMap.inr R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_inr ContinuousLinearMap.coe_inr

theorem isClosed_ker [T1Space M₂] [FunLike F M₁ M₂] [ContinuousSemilinearMapClass F σ₁₂ M₁ M₂]
    (f : F) :
    IsClosed (ker f : Set M₁) :=
  continuous_iff_isClosed.1 (map_continuous f) _ isClosed_singleton
#align continuous_linear_map.is_closed_ker ContinuousLinearMap.isClosed_ker

theorem isComplete_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T1Space M₂] [FunLike F M' M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f : F) :
    IsComplete (ker f : Set M') :=
  (isClosed_ker f).isComplete
#align continuous_linear_map.is_complete_ker ContinuousLinearMap.isComplete_ker

instance completeSpace_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂]
    [FunLike F M' M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f : F) : CompleteSpace (ker f) :=
  (isComplete_ker f).completeSpace_coe
#align continuous_linear_map.complete_space_ker ContinuousLinearMap.completeSpace_ker

instance completeSpace_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T2Space M₂]
    [FunLike F M' M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f g : F) : CompleteSpace (LinearMap.eqLocus f g) :=
  IsClosed.completeSpace_coe <| isClosed_eq (map_continuous f) (map_continuous g)

@[simp]
theorem ker_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    ker (f.prod g) = ker f ⊓ ker g :=
  LinearMap.ker_prod (f : M₁ →ₗ[R₁] M₂) (g : M₁ →ₗ[R₁] M₃)
#align continuous_linear_map.ker_prod ContinuousLinearMap.ker_prod

/-- Restrict codomain of a continuous linear map. -/
def codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    M₁ →SL[σ₁₂] p where
  cont := f.continuous.subtype_mk _
  toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h
#align continuous_linear_map.cod_restrict ContinuousLinearMap.codRestrict

@[norm_cast]
theorem coe_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h :=
  rfl
#align continuous_linear_map.coe_cod_restrict ContinuousLinearMap.coe_codRestrict

@[simp]
theorem coe_codRestrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl
#align continuous_linear_map.coe_cod_restrict_apply ContinuousLinearMap.coe_codRestrict_apply

@[simp]
theorem ker_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.codRestrict p h) = ker f :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker_codRestrict p h
#align continuous_linear_map.ker_cod_restrict ContinuousLinearMap.ker_codRestrict

/-- Restrict the codomain of a continuous linear map `f` to `f.range`. -/
@[reducible]
def rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

@[simp]
theorem coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    (f.rangeRestrict : M₁ →ₛₗ[σ₁₂] LinearMap.range f) = (f : M₁ →ₛₗ[σ₁₂] M₂).rangeRestrict :=
  rfl

/-- `Submodule.subtype` as a `ContinuousLinearMap`. -/
def _root_.Submodule.subtypeL (p : Submodule R₁ M₁) : p →L[R₁] M₁ where
  cont := continuous_subtype_val
  toLinearMap := p.subtype
set_option linter.uppercaseLean3 false in
#align submodule.subtypeL Submodule.subtypeL

@[simp, norm_cast]
theorem _root_.Submodule.coe_subtypeL (p : Submodule R₁ M₁) :
    (p.subtypeL : p →ₗ[R₁] M₁) = p.subtype :=
  rfl
set_option linter.uppercaseLean3 false in
#align submodule.coe_subtypeL Submodule.coe_subtypeL

@[simp]
theorem _root_.Submodule.coe_subtypeL' (p : Submodule R₁ M₁) : ⇑p.subtypeL = p.subtype :=
  rfl
set_option linter.uppercaseLean3 false in
#align submodule.coe_subtypeL' Submodule.coe_subtypeL'

@[simp] -- @[norm_cast] -- Porting note: A theorem with this can't have a rhs starting with `↑`.
theorem _root_.Submodule.subtypeL_apply (p : Submodule R₁ M₁) (x : p) : p.subtypeL x = x :=
  rfl
set_option linter.uppercaseLean3 false in
#align submodule.subtypeL_apply Submodule.subtypeL_apply

@[simp]
theorem _root_.Submodule.range_subtypeL (p : Submodule R₁ M₁) : range p.subtypeL = p :=
  Submodule.range_subtype _
set_option linter.uppercaseLean3 false in
#align submodule.range_subtypeL Submodule.range_subtypeL

@[simp]
theorem _root_.Submodule.ker_subtypeL (p : Submodule R₁ M₁) : ker p.subtypeL = ⊥ :=
  Submodule.ker_subtype _
set_option linter.uppercaseLean3 false in
#align submodule.ker_subtypeL Submodule.ker_subtypeL

variable (R₁ M₁ M₂)

/-- `Prod.fst` as a `ContinuousLinearMap`. -/
def fst [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₁ where
  cont := continuous_fst
  toLinearMap := LinearMap.fst R₁ M₁ M₂
#align continuous_linear_map.fst ContinuousLinearMap.fst

/-- `Prod.snd` as a `ContinuousLinearMap`. -/
def snd [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₂ where
  cont := continuous_snd
  toLinearMap := LinearMap.snd R₁ M₁ M₂
#align continuous_linear_map.snd ContinuousLinearMap.snd

variable {R₁ M₁ M₂}

@[simp, norm_cast]
theorem coe_fst [Module R₁ M₂] : ↑(fst R₁ M₁ M₂) = LinearMap.fst R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_fst ContinuousLinearMap.coe_fst

@[simp, norm_cast]
theorem coe_fst' [Module R₁ M₂] : ⇑(fst R₁ M₁ M₂) = Prod.fst :=
  rfl
#align continuous_linear_map.coe_fst' ContinuousLinearMap.coe_fst'

@[simp, norm_cast]
theorem coe_snd [Module R₁ M₂] : ↑(snd R₁ M₁ M₂) = LinearMap.snd R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_snd ContinuousLinearMap.coe_snd

@[simp, norm_cast]
theorem coe_snd' [Module R₁ M₂] : ⇑(snd R₁ M₁ M₂) = Prod.snd :=
  rfl
#align continuous_linear_map.coe_snd' ContinuousLinearMap.coe_snd'

@[simp]
theorem fst_prod_snd [Module R₁ M₂] : (fst R₁ M₁ M₂).prod (snd R₁ M₁ M₂) = id R₁ (M₁ × M₂) :=
  ext fun ⟨_x, _y⟩ => rfl
#align continuous_linear_map.fst_prod_snd ContinuousLinearMap.fst_prod_snd

@[simp]
theorem fst_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (fst R₁ M₂ M₃).comp (f.prod g) = f :=
  ext fun _x => rfl
#align continuous_linear_map.fst_comp_prod ContinuousLinearMap.fst_comp_prod

@[simp]
theorem snd_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (snd R₁ M₂ M₃).comp (f.prod g) = g :=
  ext fun _x => rfl
#align continuous_linear_map.snd_comp_prod ContinuousLinearMap.snd_comp_prod

/-- `Prod.map` of two continuous linear maps. -/
def prodMap [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
    M₁ × M₃ →L[R₁] M₂ × M₄ :=
  (f₁.comp (fst R₁ M₁ M₃)).prod (f₂.comp (snd R₁ M₁ M₃))
#align continuous_linear_map.prod_map ContinuousLinearMap.prodMap

@[simp, norm_cast]
theorem coe_prodMap [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂)
    (f₂ : M₃ →L[R₁] M₄) : ↑(f₁.prodMap f₂) = (f₁ : M₁ →ₗ[R₁] M₂).prodMap (f₂ : M₃ →ₗ[R₁] M₄) :=
  rfl
#align continuous_linear_map.coe_prod_map ContinuousLinearMap.coe_prodMap

@[simp, norm_cast]
theorem coe_prodMap' [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂)
    (f₂ : M₃ →L[R₁] M₄) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl
#align continuous_linear_map.coe_prod_map' ContinuousLinearMap.coe_prodMap'

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : M₁ × M₂ →L[R₁] M₃ :=
  ⟨LinearMap.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩
#align continuous_linear_map.coprod ContinuousLinearMap.coprod

@[norm_cast, simp]
theorem coe_coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : (f₁.coprod f₂ : M₁ × M₂ →ₗ[R₁] M₃) = LinearMap.coprod f₁ f₂ :=
  rfl
#align continuous_linear_map.coe_coprod ContinuousLinearMap.coe_coprod

@[simp]
theorem coprod_apply [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) (x) : f₁.coprod f₂ x = f₁ x.1 + f₂ x.2 :=
  rfl
#align continuous_linear_map.coprod_apply ContinuousLinearMap.coprod_apply

theorem range_coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : range (f₁.coprod f₂) = range f₁ ⊔ range f₂ :=
  LinearMap.range_coprod _ _
#align continuous_linear_map.range_coprod ContinuousLinearMap.range_coprod

theorem comp_fst_add_comp_snd [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f : M₁ →L[R₁] M₃)
    (g : M₂ →L[R₁] M₃) :
    f.comp (ContinuousLinearMap.fst R₁ M₁ M₂) + g.comp (ContinuousLinearMap.snd R₁ M₁ M₂) =
      f.coprod g :=
  rfl
#align continuous_linear_map.comp_fst_add_comp_snd ContinuousLinearMap.comp_fst_add_comp_snd

theorem coprod_inl_inr [ContinuousAdd M₁] [ContinuousAdd M'₁] :
    (ContinuousLinearMap.inl R₁ M₁ M'₁).coprod (ContinuousLinearMap.inr R₁ M₁ M'₁) =
      ContinuousLinearMap.id R₁ (M₁ × M'₁) := by
  apply coe_injective; apply LinearMap.coprod_inl_inr
#align continuous_linear_map.coprod_inl_inr ContinuousLinearMap.coprod_inl_inr

section

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S]
  [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂]

/-- The linear map `fun x => c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `ContinuousLinearMap.smulRightₗ` and `ContinuousLinearMap.smulRightL`. -/
def smulRight (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
  { c.toLinearMap.smulRight f with cont := c.2.smul continuous_const }
#align continuous_linear_map.smul_right ContinuousLinearMap.smulRight

@[simp]
theorem smulRight_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} :
    (smulRight c f : M₁ → M₂) x = c x • f :=
  rfl
#align continuous_linear_map.smul_right_apply ContinuousLinearMap.smulRight_apply

end

variable [Module R₁ M₂] [TopologicalSpace R₁] [ContinuousSMul R₁ M₂]

@[simp]
theorem smulRight_one_one (c : R₁ →L[R₁] M₂) : smulRight (1 : R₁ →L[R₁] R₁) (c 1) = c := by
  ext
  simp [← ContinuousLinearMap.map_smul_of_tower]
#align continuous_linear_map.smul_right_one_one ContinuousLinearMap.smulRight_one_one

@[simp]
theorem smulRight_one_eq_iff {f f' : M₂} :
    smulRight (1 : R₁ →L[R₁] R₁) f = smulRight (1 : R₁ →L[R₁] R₁) f' ↔ f = f' := by
  simp only [ext_ring_iff, smulRight_apply, one_apply, one_smul]
#align continuous_linear_map.smul_right_one_eq_iff ContinuousLinearMap.smulRight_one_eq_iff

theorem smulRight_comp [ContinuousMul R₁] {x : M₂} {c : R₁} :
    (smulRight (1 : R₁ →L[R₁] R₁) x).comp (smulRight (1 : R₁ →L[R₁] R₁) c) =
      smulRight (1 : R₁ →L[R₁] R₁) (c • x) := by
  ext
  simp [mul_smul]
#align continuous_linear_map.smul_right_comp ContinuousLinearMap.smulRight_comp

section ToSpanSingleton

variable (R₁)
variable [ContinuousSMul R₁ M₁]

/-- Given an element `x` of a topological space `M` over a semiring `R`, the natural continuous
linear map from `R` to `M` by taking multiples of `x`. -/
def toSpanSingleton (x : M₁) : R₁ →L[R₁] M₁
    where
  toLinearMap := LinearMap.toSpanSingleton R₁ M₁ x
  cont := continuous_id.smul continuous_const
#align continuous_linear_map.to_span_singleton ContinuousLinearMap.toSpanSingleton

theorem toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x :=
  rfl
#align continuous_linear_map.to_span_singleton_apply ContinuousLinearMap.toSpanSingleton_apply

theorem toSpanSingleton_add [ContinuousAdd M₁] (x y : M₁) :
    toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanSingleton R₁ y := by
  ext1; simp [toSpanSingleton_apply]
#align continuous_linear_map.to_span_singleton_add ContinuousLinearMap.toSpanSingleton_add

theorem toSpanSingleton_smul' {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
    [SMulCommClass R₁ α M₁] (c : α) (x : M₁) :
    toSpanSingleton R₁ (c • x) = c • toSpanSingleton R₁ x := by
  ext1; rw [toSpanSingleton_apply, smul_apply, toSpanSingleton_apply, smul_comm]
#align continuous_linear_map.to_span_singleton_smul' ContinuousLinearMap.toSpanSingleton_smul'

/-- A special case of `to_span_singleton_smul'` for when `R` is commutative. -/
theorem toSpanSingleton_smul (R) {M₁} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [TopologicalSpace R] [TopologicalSpace M₁] [ContinuousSMul R M₁] (c : R) (x : M₁) :
    toSpanSingleton R (c • x) = c • toSpanSingleton R x :=
  toSpanSingleton_smul' R c x
#align continuous_linear_map.to_span_singleton_smul ContinuousLinearMap.toSpanSingleton_smul

end ToSpanSingleton

end Semiring

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
  ⟨LinearMap.pi fun i => f i, continuous_pi fun i => (f i).continuous⟩
#align continuous_linear_map.pi ContinuousLinearMap.pi

@[simp]
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : ⇑(pi f) = fun c i => f i c :=
  rfl
#align continuous_linear_map.coe_pi' ContinuousLinearMap.coe_pi'

@[simp]
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl
#align continuous_linear_map.coe_pi ContinuousLinearMap.coe_pi

theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl
#align continuous_linear_map.pi_apply ContinuousLinearMap.pi_apply

theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [ext_iff, pi_apply, Function.funext_iff]
  exact forall_swap
#align continuous_linear_map.pi_eq_zero ContinuousLinearMap.pi_eq_zero

theorem pi_zero : pi (fun _ => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext fun _ => rfl
#align continuous_linear_map.pi_zero ContinuousLinearMap.pi_zero

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl
#align continuous_linear_map.pi_comp ContinuousLinearMap.pi_comp

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩
#align continuous_linear_map.proj ContinuousLinearMap.proj

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl
#align continuous_linear_map.proj_apply ContinuousLinearMap.proj_apply

theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun _c => rfl
#align continuous_linear_map.proj_pi ContinuousLinearMap.proj_pi

theorem iInf_ker_proj : (⨅ i, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i)) = ⊥ :=
  LinearMap.iInf_ker_proj
#align continuous_linear_map.infi_ker_proj ContinuousLinearMap.iInf_ker_proj

variable (R φ)

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i
    where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i => by
      have :=
        @continuous_subtype_val _ _ fun x =>
          x ∈ (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i))
      have := Continuous.comp (continuous_apply (π := φ) i) this
      exact this
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        -- Porting note: Was `dsimp`.
        change
          Continuous (⇑(if h : i ∈ I then LinearMap.proj (R := R) (ι := ↥I)
            (φ := fun i : ↥I => φ i) ⟨i, h⟩ else
            (0 : ((i : I) → φ i) →ₗ[R] φ i)))
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _
#align continuous_linear_map.infi_ker_proj_equiv ContinuousLinearMap.iInfKerProjEquiv

end Pi

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {R₃ : Type*} [Ring R₃] {M : Type*}
  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] {M₄ : Type*} [TopologicalSpace M₄]
  [AddCommGroup M₄] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {σ₁₃ : R →+* R₃}

section

protected theorem map_neg (f : M →SL[σ₁₂] M₂) (x : M) : f (-x) = -f x := by
  exact map_neg f x
#align continuous_linear_map.map_neg ContinuousLinearMap.map_neg

protected theorem map_sub (f : M →SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y := by
  exact map_sub f x y
#align continuous_linear_map.map_sub ContinuousLinearMap.map_sub

@[simp]
theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl
#align continuous_linear_map.sub_apply' ContinuousLinearMap.sub_apply'

end

section

variable [Module R M₂] [Module R M₃] [Module R M₄]

theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (f.prod g) = (range f).prod (range g) :=
  LinearMap.range_prod_eq h
#align continuous_linear_map.range_prod_eq ContinuousLinearMap.range_prod_eq

theorem ker_prod_ker_le_ker_coprod [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    (LinearMap.ker f).prod (LinearMap.ker g) ≤ LinearMap.ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap
#align continuous_linear_map.ker_prod_ker_le_ker_coprod ContinuousLinearMap.ker_prod_ker_le_ker_coprod

theorem ker_coprod_of_disjoint_range [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃)
    (hd : Disjoint (range f) (range g)) :
    LinearMap.ker (f.coprod g) = (LinearMap.ker f).prod (LinearMap.ker g) :=
  LinearMap.ker_coprod_of_disjoint_range f.toLinearMap g.toLinearMap hd
#align continuous_linear_map.ker_coprod_of_disjoint_range ContinuousLinearMap.ker_coprod_of_disjoint_range

end

section

variable [TopologicalAddGroup M₂]

instance neg : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩
#align continuous_linear_map.has_neg ContinuousLinearMap.neg

@[simp]
theorem neg_apply (f : M →SL[σ₁₂] M₂) (x : M) : (-f) x = -f x :=
  rfl
#align continuous_linear_map.neg_apply ContinuousLinearMap.neg_apply

@[simp, norm_cast]
theorem coe_neg (f : M →SL[σ₁₂] M₂) : (↑(-f) : M →ₛₗ[σ₁₂] M₂) = -f :=
  rfl
#align continuous_linear_map.coe_neg ContinuousLinearMap.coe_neg

@[norm_cast]
theorem coe_neg' (f : M →SL[σ₁₂] M₂) : ⇑(-f) = -f :=
  rfl
#align continuous_linear_map.coe_neg' ContinuousLinearMap.coe_neg'

instance sub : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩
#align continuous_linear_map.has_sub ContinuousLinearMap.sub

instance addCommGroup : AddCommGroup (M →SL[σ₁₂] M₂) := by
  refine'
    { ContinuousLinearMap.addCommMonoid with
      neg := (-·)
      sub := (· - ·)
      sub_eq_add_neg := _
      nsmul := (· • ·)
      zsmul := (· • ·)
      zsmul_zero' := fun f => by ext; simp
      zsmul_succ' := fun n f => by ext; simp [add_smul, add_comm]
      zsmul_neg' := fun n f => by ext; simp [Nat.succ_eq_add_one, add_smul]
      .. } <;>
    { intros
      ext
      apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm, sub_eq_add_neg] }
#align continuous_linear_map.add_comm_group ContinuousLinearMap.addCommGroup

theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
  rfl
#align continuous_linear_map.sub_apply ContinuousLinearMap.sub_apply

@[simp, norm_cast]
theorem coe_sub (f g : M →SL[σ₁₂] M₂) : (↑(f - g) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl
#align continuous_linear_map.coe_sub ContinuousLinearMap.coe_sub

@[simp, norm_cast]
theorem coe_sub' (f g : M →SL[σ₁₂] M₂) : ⇑(f - g) = f - g :=
  rfl
#align continuous_linear_map.coe_sub' ContinuousLinearMap.coe_sub'

end

@[simp]
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₂] [TopologicalAddGroup M₃]
    (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) : g.comp (-f) = -g.comp f := by
  ext x
  simp
#align continuous_linear_map.comp_neg ContinuousLinearMap.comp_neg

@[simp]
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (-g).comp f = -g.comp f := by
  ext
  simp
#align continuous_linear_map.neg_comp ContinuousLinearMap.neg_comp

@[simp]
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₂] [TopologicalAddGroup M₃]
    (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M →SL[σ₁₂] M₂) : g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ := by
  ext
  simp
#align continuous_linear_map.comp_sub ContinuousLinearMap.comp_sub

@[simp]
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (g₁ - g₂).comp f = g₁.comp f - g₂.comp f := by
  ext
  simp
#align continuous_linear_map.sub_comp ContinuousLinearMap.sub_comp

instance ring [TopologicalAddGroup M] : Ring (M →L[R] M) where
  __ := ContinuousLinearMap.semiring
  __ := ContinuousLinearMap.addCommGroup
  intCast z := z • (1 : M →L[R] M)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _
#align continuous_linear_map.ring ContinuousLinearMap.ring

@[simp]
theorem intCast_apply [TopologicalAddGroup M] (z : ℤ) (m : M) : (↑z : M →L[R] M) m = z • m :=
  rfl

theorem smulRight_one_pow [TopologicalSpace R] [TopologicalRing R] (c : R) (n : ℕ) :
    smulRight (1 : R →L[R] R) c ^ n = smulRight (1 : R →L[R] R) (c ^ n) := by
  induction' n with n ihn
  · ext
    simp
  · rw [pow_succ, ihn, mul_def, smulRight_comp, smul_eq_mul, pow_succ']
#align continuous_linear_map.smul_right_one_pow ContinuousLinearMap.smulRight_one_pow

section

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]


/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`projKerOfRightInverse f₁ f₂ h` is the projection `M →L[R] LinearMap.ker f₁` along
`LinearMap.range f₂`. -/
def projKerOfRightInverse [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) : M →L[R] LinearMap.ker f₁ :=
  (id R M - f₂.comp f₁).codRestrict (LinearMap.ker f₁) fun x => by simp [h (f₁ x)]
#align continuous_linear_map.proj_ker_of_right_inverse ContinuousLinearMap.projKerOfRightInverse

@[simp]
theorem coe_projKerOfRightInverse_apply [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    (f₁.projKerOfRightInverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl
#align continuous_linear_map.coe_proj_ker_of_right_inverse_apply ContinuousLinearMap.coe_projKerOfRightInverse_apply

@[simp]
theorem projKerOfRightInverse_apply_idem [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : LinearMap.ker f₁) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp
#align continuous_linear_map.proj_ker_of_right_inverse_apply_idem ContinuousLinearMap.projKerOfRightInverse_apply_idem

@[simp]
theorem projKerOfRightInverse_comp_inv [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff_val.2 <| by simp [h y]
#align continuous_linear_map.proj_ker_of_right_inverse_comp_inv ContinuousLinearMap.projKerOfRightInverse_comp_inv

end

end Ring

section DivisionMonoid

variable {R M : Type*}

/-- A nonzero continuous linear functional is open. -/
protected theorem isOpenMap_of_ne_zero [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
    [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]
    (f : M →L[R] R) (hf : f ≠ 0) : IsOpenMap f :=
  let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
    ⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt <| by continuity, by simp,
      fun a => by simp [hx]⟩
#align continuous_linear_map.is_open_map_of_ne_zero ContinuousLinearMap.isOpenMap_of_ne_zero

end DivisionMonoid

section SMulMonoid

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Monoid S] [Monoid S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃]
  [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃]
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
theorem smul_comp (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    (c • h).comp f = c • h.comp f :=
  rfl
#align continuous_linear_map.smul_comp ContinuousLinearMap.smul_comp

variable [DistribMulAction S₃ M₂] [ContinuousConstSMul S₃ M₂] [SMulCommClass R₂ S₃ M₂]
variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ →L[R] N₃) (c : S)
    (fₗ : M →L[R] N₂) : hₗ.comp (c • fₗ) = c • hₗ.comp fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)
#align continuous_linear_map.comp_smul ContinuousLinearMap.comp_smul

@[simp]
theorem comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
    [ContinuousConstSMul R₃ M₃] (h : M₂ →SL[σ₂₃] M₃) (c : R₂) (f : M →SL[σ₁₂] M₂) :
    h.comp (c • f) = σ₂₃ c • h.comp f := by
  ext x
  simp only [coe_smul', coe_comp', Function.comp_apply, Pi.smul_apply,
    ContinuousLinearMap.map_smulₛₗ]
#align continuous_linear_map.comp_smulₛₗ ContinuousLinearMap.comp_smulₛₗ

instance distribMulAction [ContinuousAdd M₂] : DistribMulAction S₃ (M →SL[σ₁₂] M₂) where
  smul_add a f g := ext fun x => smul_add a (f x) (g x)
  smul_zero _a := ext fun _x => smul_zero _
#align continuous_linear_map.distrib_mul_action ContinuousLinearMap.distribMulAction

end SMulMonoid

section SMul

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S] [Semiring S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃] [Module S₃ M₃]
  [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃] [Module S N₂] [ContinuousConstSMul S N₂]
  [SMulCommClass R S N₂] [Module S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃]
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : M₂ →SL[σ₂₃] M₃) (f g : M →SL[σ₁₂] M₂) (x y z : M)

/-- `ContinuousLinearMap.prod` as an `Equiv`. -/
@[simps apply]
def prodEquiv : (M →L[R] N₂) × (M →L[R] N₃) ≃ (M →L[R] N₂ × N₃) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align continuous_linear_map.prod_equiv ContinuousLinearMap.prodEquiv
#align continuous_linear_map.prod_equiv_apply ContinuousLinearMap.prodEquiv_apply

theorem prod_ext_iff {f g : M × N₂ →L[R] N₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl
#align continuous_linear_map.prod_ext_iff ContinuousLinearMap.prod_ext_iff

@[ext]
theorem prod_ext {f g : M × N₂ →L[R] N₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩
#align continuous_linear_map.prod_ext ContinuousLinearMap.prod_ext

variable [ContinuousAdd M₂] [ContinuousAdd M₃] [ContinuousAdd N₂]

instance module : Module S₃ (M →SL[σ₁₃] M₃) where
  zero_smul _ := ext fun _ => zero_smul _ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
#align continuous_linear_map.module ContinuousLinearMap.module

instance isCentralScalar [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] :
    IsCentralScalar S₃ (M →SL[σ₁₃] M₃) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
#align continuous_linear_map.is_central_scalar ContinuousLinearMap.isCentralScalar

variable (S) [ContinuousAdd N₃]

/-- `ContinuousLinearMap.prod` as a `LinearEquiv`. -/
@[simps apply]
def prodₗ : ((M →L[R] N₂) × (M →L[R] N₃)) ≃ₗ[S] M →L[R] N₂ × N₃ :=
  { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }
#align continuous_linear_map.prodₗ ContinuousLinearMap.prodₗ
#align continuous_linear_map.prodₗ_apply ContinuousLinearMap.prodₗ_apply

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
def coeLM : (M →L[R] N₃) →ₗ[S] M →ₗ[R] N₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f
#align continuous_linear_map.coe_lm ContinuousLinearMap.coeLM
#align continuous_linear_map.coe_lm_apply ContinuousLinearMap.coeLM_apply

variable {S} (σ₁₃)

/-- The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
def coeLMₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] M →ₛₗ[σ₁₃] M₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f
#align continuous_linear_map.coe_lmₛₗ ContinuousLinearMap.coeLMₛₗ
#align continuous_linear_map.coe_lmₛₗ_apply ContinuousLinearMap.coeLMₛₗ_apply

end SMul

section SMulRightₗ

variable {R S T M M₂ : Type*} [Semiring R] [Semiring S] [Semiring T] [Module R S]
  [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]
  [TopologicalSpace M₂] [ContinuousSMul S M₂] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd M₂] [Module T M₂] [ContinuousConstSMul T M₂] [SMulCommClass R T M₂]
  [SMulCommClass S T M₂]

/-- Given `c : E →L[𝕜] 𝕜`, `c.smulRightₗ` is the linear map from `F` to `E →L[𝕜] F`
sending `f` to `fun e => c e • f`. See also `ContinuousLinearMap.smulRightL`. -/
def smulRightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂ where
  toFun := c.smulRight
  map_add' x y := by
    ext e
    apply smul_add
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm
#align continuous_linear_map.smul_rightₗ ContinuousLinearMap.smulRightₗ

@[simp]
theorem coe_smulRightₗ (c : M →L[R] S) : ⇑(smulRightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smulRight :=
  rfl
#align continuous_linear_map.coe_smul_rightₗ ContinuousLinearMap.coe_smulRightₗ

end SMulRightₗ

section CommRing

variable {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  [Module R M] [Module R M₂] [Module R M₃] [ContinuousConstSMul R M₃]

variable [TopologicalAddGroup M₂] [ContinuousConstSMul R M₂]

instance algebra : Algebra R (M₂ →L[R] M₂) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _
#align continuous_linear_map.algebra ContinuousLinearMap.algebra

@[simp] theorem algebraMap_apply (r : R) (m : M₂) : algebraMap R (M₂ →L[R] M₂) r m = r • m := rfl

end CommRing

section RestrictScalars

variable {A M M₂ : Type*} [Ring A] [AddCommGroup M] [AddCommGroup M₂] [Module A M] [Module A M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] (R : Type*) [Ring R] [Module R M] [Module R M₂]
  [LinearMap.CompatibleSMul M M₂ R A]

/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `LinearMap.CompatibleSMul M M₂ R A` to match assumptions of
`LinearMap.map_smul_of_tower`. -/
def restrictScalars (f : M →L[A] M₂) : M →L[R] M₂ :=
  ⟨(f : M →ₗ[A] M₂).restrictScalars R, f.continuous⟩
#align continuous_linear_map.restrict_scalars ContinuousLinearMap.restrictScalars

variable {R}

@[simp] -- @[norm_cast] -- Porting note: This theorem can't be a `norm_cast` theorem.
theorem coe_restrictScalars (f : M →L[A] M₂) :
    (f.restrictScalars R : M →ₗ[R] M₂) = (f : M →ₗ[A] M₂).restrictScalars R :=
  rfl
#align continuous_linear_map.coe_restrict_scalars ContinuousLinearMap.coe_restrictScalars

@[simp]
theorem coe_restrictScalars' (f : M →L[A] M₂) : ⇑(f.restrictScalars R) = f :=
  rfl
#align continuous_linear_map.coe_restrict_scalars' ContinuousLinearMap.coe_restrictScalars'

@[simp]
theorem restrictScalars_zero : (0 : M →L[A] M₂).restrictScalars R = 0 :=
  rfl
#align continuous_linear_map.restrict_scalars_zero ContinuousLinearMap.restrictScalars_zero

section

variable [TopologicalAddGroup M₂]

@[simp]
theorem restrictScalars_add (f g : M →L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_add ContinuousLinearMap.restrictScalars_add

@[simp]
theorem restrictScalars_neg (f : M →L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_neg ContinuousLinearMap.restrictScalars_neg

end

variable {S : Type*}
variable [Ring S] [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂]
  [SMulCommClass R S M₂]

@[simp]
theorem restrictScalars_smul (c : S) (f : M →L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_smul ContinuousLinearMap.restrictScalars_smul

variable (A M M₂ R S)
variable [TopologicalAddGroup M₂]

/-- `ContinuousLinearMap.restrictScalars` as a `LinearMap`. See also
`ContinuousLinearMap.restrictScalarsL`. -/
def restrictScalarsₗ : (M →L[A] M₂) →ₗ[S] M →L[R] M₂ where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul
#align continuous_linear_map.restrict_scalarsₗ ContinuousLinearMap.restrictScalarsₗ

variable {A M M₂ R S}

@[simp]
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M M₂ R S) = restrictScalars R :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsₗ ContinuousLinearMap.coe_restrictScalarsₗ

end RestrictScalars

end ContinuousAlgHom



end

end TopologicalAlgebra
