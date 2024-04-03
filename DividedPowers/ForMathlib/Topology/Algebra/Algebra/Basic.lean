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

open Set Filter TopologicalSpace Function Topology Filter

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
#exit
-- ACL : exit because what is below doesn't compile here

/-- See Note [custom simps projection]. -/
def Simps.coe (h : A →A[R] B) : A →ₐ[R] B := h

initialize_simps_projections ContinuousAlgHom (toAlgHom_toFun → apply, toAlgHom → coe)

@[ext]
theorem ext {f g : A →A[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

theorem ext_iff {f g : A →A[R] B} : f = g ↔ ∀ x, f x = g x := DFunLike.ext_iff

/-- Copy of a `ContinuousAlgHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : A →A[R] B) (f' : A → B) (h : f' = ⇑f) : A →A[R] B where
  toAlgHom := (f : A →A[R] B).copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
theorem coe_copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_linear_map.coe_copy ContinuousLinearMap.coe_copy

#exit








theorem copy_eq (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h
#align continuous_linear_map.copy_eq ContinuousLinearMap.copy_eq

-- make some straightforward lemmas available to `simp`.
protected theorem map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
  map_zero f
#align continuous_linear_map.map_zero ContinuousLinearMap.map_zero

protected theorem map_add (f : M₁ →SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y :=
  map_add f x y
#align continuous_linear_map.map_add ContinuousLinearMap.map_add

-- @[simp] -- Porting note (#10618): simp can prove this
protected theorem map_smulₛₗ (f : M₁ →SL[σ₁₂] M₂) (c : R₁) (x : M₁) : f (c • x) = σ₁₂ c • f x :=
  (toLinearMap _).map_smulₛₗ _ _
#align continuous_linear_map.map_smulₛₗ ContinuousLinearMap.map_smulₛₗ

-- @[simp] -- Porting note (#10618): simp can prove this
protected theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) :
    f (c • x) = c • f x := by simp only [RingHom.id_apply, ContinuousLinearMap.map_smulₛₗ]
#align continuous_linear_map.map_smul ContinuousLinearMap.map_smul

@[simp]
theorem map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
    [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) :
    f (c • x) = c • f x :=
  LinearMap.CompatibleSMul.map_smul (f : M₁ →ₗ[S] M₂) c x
#align continuous_linear_map.map_smul_of_tower ContinuousLinearMap.map_smul_of_tower

@[deprecated _root_.map_sum]
protected theorem map_sum {ι : Type*} (f : M₁ →SL[σ₁₂] M₂) (s : Finset ι) (g : ι → M₁) :
    f (∑ i in s, g i) = ∑ i in s, f (g i) :=
  map_sum ..
#align continuous_linear_map.map_sum ContinuousLinearMap.map_sum

@[simp, norm_cast]
theorem coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl
#align continuous_linear_map.coe_coe ContinuousLinearMap.coe_coe

@[ext]
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1 <| LinearMap.ext_ring h
#align continuous_linear_map.ext_ring ContinuousLinearMap.ext_ring

theorem ext_ring_iff [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩
#align continuous_linear_map.ext_ring_iff ContinuousLinearMap.ext_ring_iff

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `Submodule.span` of this set. -/
theorem eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous
#align continuous_linear_map.eq_on_closure_span ContinuousLinearMap.eqOn_closure_span

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)
#align continuous_linear_map.ext_on ContinuousLinearMap.ext_on

/-- Under a continuous linear map, the image of the `TopologicalClosure` of a submodule is
contained in the `TopologicalClosure` of its image. -/
theorem _root_.Submodule.topologicalClosure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂) (s : Submodule R₁ M₁) :
    s.topologicalClosure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤
      (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous
#align submodule.topological_closure_map Submodule.topologicalClosure_map

/-- Under a dense continuous linear map, a submodule whose `TopologicalClosure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_submodule [RingHomSurjective σ₁₂]
    [TopologicalSpace R₁] [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁]
    [ContinuousSMul R₂ M₂] [ContinuousAdd M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f)
    {s : Submodule R₁ M₁} (hs : s.topologicalClosure = ⊤) :
    (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs
#align dense_range.topological_clo


end Semiring

end ContinuousAlgHom

#exit






end

end TopologicalAlgebra
