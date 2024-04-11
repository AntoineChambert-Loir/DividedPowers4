import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!

# Topological algebras

A topological algebra `S` over a commutative topological ring `R` is an `R`-algebra `S`
which is a topological ring and such that the algebra map from `R` to `S` is continuous.

-/

section
--TODO: move to correct file

def AlgHom.prodMap {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Semiring D] [Algebra R A] [Algebra R B] [Algebra R C]  [Algebra R D] (f : A →ₐ[R] B)
    (g : C →ₐ[R] D) :
    A × C →ₐ[R] B × D :=
  { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, Prod.algebraMap_apply,
        OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_prodMap,
        RingHom.coe_coe, Prod_map, commutes] }

-- NOTE: RingHom.pi and AlgHom.pi are not available.
end


open Set Filter TopologicalSpace Function Topology Filter BigOperators

section TopologicalAlgebra

/-- A topological algebra `S` over a commutative topological semiring `R` is an `R`-algebra `S`
  which is a topological semiring and such that the algebra map from `R` to `S` is continuous. -/
class TopologicalAlgebra (R : Type*) [CommSemiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (A : Type*) [Semiring A] [TopologicalSpace A] [TopologicalSemiring A] extends
    Algebra R A where
  continuous_algebraMap : Continuous (algebraMap R A)

variable (R : Type*) [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]
  (A : Type*) [Semiring A] [TopologicalSpace A] [TopologicalSemiring A]

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
instance Pi.topologicalAlgebra {β : Type*} {C : β → Type*} [∀ b, Semiring (C b)]
    [∀ b, TopologicalSpace (C b)] [∀ b, TopologicalSemiring (C b)]
    [∀ b, TopologicalAlgebra R (C b)] :
  TopologicalAlgebra R (Π b , C b) :=
{ toAlgebra := Pi.algebra _ _
  continuous_algebraMap :=
    continuous_pi_iff.mpr fun _ =>  TopologicalAlgebra.continuous_algebraMap }

end Pi

section
/-- Continuous algebra homomorphisms between algebras. We only put the type classes that are necessary for the
definition, although in applications `M` and `B` will be topological algebras over the topological
ring `R`. -/
structure ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [TopologicalSpace A] (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    extends A →ₐ[R] B where
  cont : Continuous toFun := by continuity

/-- `ContinuousAlgHomClass F R A B` asserts `F` is a type of bundled continuous `R`-agebra
  homomorphisms `A → B`. -/
class ContinuousAlgHomClass (F : Type*) (R : outParam (Type*)) [CommSemiring R]
    (A : outParam (Type*)) [Semiring A] [TopologicalSpace A]
    (B : outParam (Type*)) [Semiring B] [TopologicalSpace B][Algebra R A]
    [Algebra R B] [FunLike F A B]
    extends AlgHomClass F R A B, ContinuousMapClass F A B : Prop
attribute [inherit_doc ContinuousAlgHom] ContinuousAlgHom.cont

@[inherit_doc]
notation:25 A " →A[" R "] " B => ContinuousAlgHom R A B

variable {R} {A}
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

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

protected theorem map_zero (f : A →A[R] B) : f (0 : A) = 0 := map_zero f

protected theorem map_add (f : A →A[R] B) (x y : A) : f (x + y) = f x + f y := map_add f x y

protected theorem map_smul [Module R A] (f : A →A[R] B) (c : R) (x : A) :
    f (c • x) = c • f x := (toAlgHom _).map_smul _ _

@[simp]
theorem map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
    [Algebra S B] [MulActionHomClass (A →A[S] B) R A B] (f : A →A[S] B) (c : R) (x : A) :
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

variable (R) (A)

/-- The identity map as a continuous algebra homomorphism. -/
def id : A →A[R] A := ⟨AlgHom.id R A, continuous_id⟩

instance one : One (A →A[R] A) := ⟨id R A⟩

theorem one_def : (1 : A →A[R] A) = id R A := rfl

theorem id_apply (x : A) : id R A x = x := rfl

@[simp, norm_cast]
theorem coe_id : ((id R A) : A →ₐ[R] A) = AlgHom.id R A:= rfl

@[simp, norm_cast]
theorem coe_id' : ⇑(id R A ) = _root_.id := rfl

@[simp, norm_cast]
theorem coe_eq_id {f : A →A[R] A} : (f : A →ₐ[R] A) = AlgHom.id R A ↔ f = id R A:= by
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

theorem comp_apply (g : B →A[R] C) (f : A →A[R] B) (x : A) : (g.comp f) x = g (f x) := rfl

@[simp]
theorem comp_id (f : A →A[R] B) : f.comp (id R A) = f := ext fun _x => rfl

@[simp]
theorem id_comp (f : A →A[R] B) : (id R B).comp f = f := ext fun _x => rfl

theorem comp_assoc {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h : C →A[R] D)
    (g : B →A[R] C) (f : A →A[R] B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

instance instMul : Mul (A →A[R] A) := ⟨comp⟩

theorem mul_def (f g : A →A[R] A) : f * g = f.comp g := rfl

@[simp]
theorem coe_mul (f g : A →A[R] A) : ⇑(f * g) = f ∘ g := rfl

theorem mul_apply (f g : A →A[R] A) (x : A) : (f * g) x = f (g x) := rfl

instance monoidWithZero : Monoid (A →A[R] A) where
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

theorem coe_pow (f : A →A[R] A) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

/-- `ContinuousLinearMap.toLinearMap` as a `RingHom`. -/
@[simps]
def toAlgHomMonoidHom [ContinuousAdd A] : (A →A[R] A) →* A →ₐ[R] A where
  toFun        := toAlgHom
  map_one'     := rfl
  map_mul' _ _ := rfl

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod [Module R B] [Module R C] (f₁ : A →A[R] B) (f₂ : A →A[R] C) :
    A →A[R] B × C :=
  ⟨(f₁ : A →ₐ[R] B).prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod [Module R B] [Module R C] (f₁ : A →A[R] B) (f₂ : A →A[R] C) :
    (f₁.prod f₂ : A →ₐ[R] B × C) = AlgHom.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
theorem prod_apply [Module R B] [Module R C] (f₁ : A →A[R] B) (f₂ : A →A[R] C) (x : A) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl


variable {F : Type*}

instance completeSpace_eqLocus {D : Type*} [UniformSpace D] [CompleteSpace D]
    [Semiring D] [Algebra R D] [T2Space B]
    [FunLike F D B] [ContinuousAlgHomClass F R D B]
    (f g : F) : CompleteSpace (LinearMap.eqLocus f g) :=
  IsClosed.completeSpace_coe <| isClosed_eq (map_continuous f) (map_continuous g)


/-- Restrict codomain of a continuous linear map. -/
def codRestrict (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) : A →A[R] p where
  cont     := f.continuous.subtype_mk _
  toAlgHom := (f : A →ₐ[R] B).codRestrict p h

@[norm_cast]
theorem coe_codRestrict (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : A →ₐ[R] p) = (f : A →ₐ[R] B).codRestrict p h :=
  rfl

@[simp]
theorem coe_codRestrict_apply (f : A →A[R] B) (p : Subalgebra R B) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : B) = f x :=
  rfl

/-- Restrict the codomain of a continuous algebra homomorphism `f` to `f.range`. -/
@[reducible]
def rangeRestrict (f : A →A[R] B) :=
  f.codRestrict (@AlgHom.range R A B  _ _ _ _ _ f) (@AlgHom.mem_range_self R A B  _ _ _ _ _ f)

@[simp]
theorem coe_rangeRestrict (f : A →A[R] B) :
    (f.rangeRestrict : A →ₐ[R] (@AlgHom.range R A B  _ _ _ _ _ f)) =
      (f : A →ₐ[R] B).rangeRestrict :=
  rfl

/-- `Subalgebra.val` as a `ContinuousLinearMap`. -/
def _root_.Subalgebra.valA (p : Subalgebra R A) : p →A[R] A where
  cont := continuous_subtype_val
  toAlgHom := p.val


@[simp, norm_cast]
theorem _root_.Subalgebra.coe_valA (p : Subalgebra R A) :
    (p.valA : p →ₐ[R] A) = p.subtype :=
  rfl

@[simp]
theorem _root_.Subalgebra.coe_valA' (p : Subalgebra R A) : ⇑p.valA = p.subtype :=
  rfl
set_option linter.uppercaseLean3 false in
#align Subalgebra.coe_valA' Subalgebra.coe_valA'

@[simp] -- @[norm_cast] -- Porting note: A theorem with this can't have a rhs starting with `↑`.
theorem _root_.Subalgebra.valA_apply (p : Subalgebra R A) (x : p) : p.valA x = x :=
  rfl

@[simp]
theorem _root_.Submodule.range_valA (p : Subalgebra R A) :
    @AlgHom.range R p A _ _ _ _ _ p.valA = p :=
  Subalgebra.range_val p

variable (R A B)

/-- `Prod.fst` as a `ContinuousLinearMap`. -/
def fst : A × B →A[R] A where
  cont     := continuous_fst
  toAlgHom := AlgHom.fst R A B

/-- `Prod.snd` as a `ContinuousLinearMap`. -/
def snd : A × B →A[R] B where
  cont := continuous_snd
  toAlgHom := AlgHom.snd R A B

variable {R A B}

@[simp, norm_cast]
theorem coe_fst : ↑(fst R A B) = AlgHom.fst R A B :=
  rfl

@[simp, norm_cast]
theorem coe_fst' : ⇑(fst R A B) = Prod.fst :=
  rfl

@[simp, norm_cast]
theorem coe_snd : ↑(snd R A B) = AlgHom.snd R A B :=
  rfl

@[simp, norm_cast]
theorem coe_snd' : ⇑(snd R A B) = Prod.snd :=
  rfl

@[simp]
theorem fst_prod_snd  : (fst R A B).prod (snd R A B) = id R (A × B) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
theorem fst_comp_prod (f : A →A[R] B) (g : A →A[R] C) :
    (fst R B C).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
theorem snd_comp_prod  (f : A →A[R] B) (g : A →A[R] C) :
    (snd R B C).comp (f.prod g) = g :=
  ext fun _x => rfl

/-- `Prod.map` of two continuous algebra homomorphisms. -/
def prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) : A × C →A[R] B × D :=
  (f₁.comp (fst R A C)).prod (f₂.comp (snd R A C))

/-   variable {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D)

#check f₁.prodMap f₂ -/



@[simp, norm_cast]
theorem coe_prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) :
    (f₁.prodMap f₂ : A × C →ₐ[R] B × D) = (f₁ : A →ₐ[R] B).prodMap (f₂ : C →ₐ[R] D) :=
  rfl

@[simp, norm_cast]
theorem coe_prodMap' {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A →A[R] B)
    (f₂ : C →A[R] D) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

section Ring

variable {M : Type*} [Ring M] [TopologicalSpace M] [Algebra R M] {N : Type*} [Ring N]
  [TopologicalSpace N] [Algebra R N]

protected theorem map_neg (f : M →A[R] N) (x : M) : f (-x) = -f x := map_neg f x

protected theorem map_sub (f : M →A[R] N) (x y : M) : f (x - y) = f x - f y := map_sub f x y

#exit
section

variable [Module R B] [Module R C] [Module R M₄]

theorem range_prod_eq {f : M →A[R] B} {g : M →A[R] C} (h : ker f ⊔ ker g = ⊤) :
    range (f.prod g) = (range f).prod (range g) :=
  LinearMap.range_prod_eq h
#align continuous_linear_map.range_prod_eq ContinuousLinearMap.range_prod_eq

theorem ker_prod_ker_le_ker_coprod [ContinuousAdd C] (f : M →A[R] C) (g : B →A[R] C) :
    (LinearMap.ker f).prod (LinearMap.ker g) ≤ LinearMap.ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap
#align continuous_linear_map.ker_prod_ker_le_ker_coprod ContinuousLinearMap.ker_prod_ker_le_ker_coprod

theorem ker_coprod_of_disjoint_range [ContinuousAdd C] (f : M →A[R] C) (g : B →A[R] C)
    (hd : Disjoint (range f) (range g)) :
    LinearMap.ker (f.coprod g) = (LinearMap.ker f).prod (LinearMap.ker g) :=
  LinearMap.ker_coprod_of_disjoint_range f.toLinearMap g.toLinearMap hd
#align continuous_linear_map.ker_coprod_of_disjoint_range ContinuousLinearMap.ker_coprod_of_disjoint_range

end

section

variable [TopologicalAddGroup B]

instance neg : Neg (M →A[R] B) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩
#align continuous_linear_map.has_neg ContinuousLinearMap.neg

@[simp]
theorem neg_apply (f : M →A[R] B) (x : M) : (-f) x = -f x :=
  rfl
#align continuous_linear_map.neg_apply ContinuousLinearMap.neg_apply

@[simp, norm_cast]
theorem coe_neg (f : M →A[R] B) : (↑(-f) : M →ₐ[R] B) = -f :=
  rfl
#align continuous_linear_map.coe_neg ContinuousLinearMap.coe_neg

@[norm_cast]
theorem coe_neg' (f : M →A[R] B) : ⇑(-f) = -f :=
  rfl
#align continuous_linear_map.coe_neg' ContinuousLinearMap.coe_neg'

instance sub : Sub (M →A[R] B) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩
#align continuous_linear_map.has_sub ContinuousLinearMap.sub

instance addCommGroup : AddCommGroup (M →A[R] B) := by
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

theorem sub_apply (f g : M →A[R] B) (x : M) : (f - g) x = f x - g x :=
  rfl
#align continuous_linear_map.sub_apply ContinuousLinearMap.sub_apply

@[simp, norm_cast]
theorem coe_sub (f g : M →A[R] B) : (↑(f - g) : M →ₐ[R] B) = f - g :=
  rfl
#align continuous_linear_map.coe_sub ContinuousLinearMap.coe_sub

@[simp, norm_cast]
theorem coe_sub' (f g : M →A[R] B) : ⇑(f - g) = f - g :=
  rfl
#align continuous_linear_map.coe_sub' ContinuousLinearMap.coe_sub'

end

@[simp]
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup B] [TopologicalAddGroup C]
    (g : B →SL[σ₂₃] C) (f : M →A[R] B) : g.comp (-f) = -g.comp f := by
  ext x
  simp
#align continuous_linear_map.comp_neg ContinuousLinearMap.comp_neg

@[simp]
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup C] (g : B →SL[σ₂₃] C)
    (f : M →A[R] B) : (-g).comp f = -g.comp f := by
  ext
  simp
#align continuous_linear_map.neg_comp ContinuousLinearMap.neg_comp

@[simp]
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup B] [TopologicalAddGroup C]
    (g : B →SL[σ₂₃] C) (f₁ f₂ : M →A[R] B) : g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ := by
  ext
  simp
#align continuous_linear_map.comp_sub ContinuousLinearMap.comp_sub

@[simp]
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup C] (g₁ g₂ : B →SL[σ₂₃] C)
    (f : M →A[R] B) : (g₁ - g₂).comp f = g₁.comp f - g₂.comp f := by
  ext
  simp
#align continuous_linear_map.sub_comp ContinuousLinearMap.sub_comp

instance ring [TopologicalAddGroup M] : Ring (M →A[R] M) where
  __ := ContinuousLinearMap.semiring
  __ := ContinuousLinearMap.addCommGroup
  intCast z := z • (1 : M →A[R] M)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _
#align continuous_linear_map.ring ContinuousLinearMap.ring

@[simp]
theorem intCast_apply [TopologicalAddGroup M] (z : ℤ) (m : M) : (↑z : M →A[R] M) m = z • m :=
  rfl

theorem smulRight_one_pow [TopologicalSpace R] [TopologicalRing R] (c : R) (n : ℕ) :
    smulRight (1 : R →A[R] R) c ^ n = smulRight (1 : R →A[R] R) (c ^ n) := by
  induction' n with n ihn
  · ext
    simp
  · rw [pow_succ, ihn, mul_def, smulRight_comp, smul_eq_mul, pow_succ']
#align continuous_linear_map.smul_right_one_pow ContinuousLinearMap.smulRight_one_pow

section

variable {σ₂₁ : R →+* R} [RingHomInvPair σ₁₂ σ₂₁]


/-- Given a right inverse `f₂ : B →A[R] M` to `f₁ : M →A[R] B`,
`projKerOfRightInverse f₁ f₂ h` is the projection `M →A[R] LinearMap.ker f₁` along
`LinearMap.range f₂`. -/
def projKerOfRightInverse [TopologicalAddGroup M] (f₁ : M →A[R] B) (f₂ : B →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) : M →A[R] LinearMap.ker f₁ :=
  (id R M - f₂.comp f₁).codRestrict (LinearMap.ker f₁) fun x => by simp [h (f₁ x)]
#align continuous_linear_map.proj_ker_of_right_inverse ContinuousLinearMap.projKerOfRightInverse

@[simp]
theorem coe_projKerOfRightInverse_apply [TopologicalAddGroup M] (f₁ : M →A[R] B)
    (f₂ : B →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    (f₁.projKerOfRightInverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl
#align continuous_linear_map.coe_proj_ker_of_right_inverse_apply ContinuousLinearMap.coe_projKerOfRightInverse_apply

@[simp]
theorem projKerOfRightInverse_apply_idem [TopologicalAddGroup M] (f₁ : M →A[R] B)
    (f₂ : B →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : LinearMap.ker f₁) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp
#align continuous_linear_map.proj_ker_of_right_inverse_apply_idem ContinuousLinearMap.projKerOfRightInverse_apply_idem

@[simp]
theorem projKerOfRightInverse_comp_inv [TopologicalAddGroup M] (f₁ : M →A[R] B)
    (f₂ : B →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (y : B) :
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
    (f : M →A[R] R) (hf : f ≠ 0) : IsOpenMap f :=
  let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
    ⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt <| by continuity, by simp,
      fun a => by simp [hx]⟩
#align continuous_linear_map.is_open_map_of_ne_zero ContinuousLinearMap.isOpenMap_of_ne_zero

end DivisionMonoid

section SMulMonoid

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R R₃ S S₃ : Type*} [Semiring R] [Semiring R] [Semiring R₃] [Monoid S] [Monoid S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {B : Type*}
  [TopologicalSpace B] [AddCommMonoid B] [Module R B] {C : Type*} [TopologicalSpace C]
  [AddCommMonoid C] [Module R₃ C] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃]
  [DistribMulAction S₃ C] [SMulCommClass R₃ S₃ C] [ContinuousConstSMul S₃ C]
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R →+* R}
  {σ₂₃ : R →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
theorem smul_comp (c : S₃) (h : B →SL[σ₂₃] C) (f : M →A[R] B) :
    (c • h).comp f = c • h.comp f :=
  rfl
#align continuous_linear_map.smul_comp ContinuousLinearMap.smul_comp

variable [DistribMulAction S₃ B] [ContinuousConstSMul S₃ B] [SMulCommClass R S₃ B]
variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ →A[R] N₃) (c : S)
    (fₗ : M →A[R] N₂) : hₗ.comp (c • fₗ) = c • hₗ.comp fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)
#align continuous_linear_map.comp_smul ContinuousLinearMap.comp_smul

@[simp]
theorem comp_smulₛₗ [SMulCommClass R R B] [SMulCommClass R₃ R₃ C] [ContinuousConstSMul R B]
    [ContinuousConstSMul R₃ C] (h : B →SL[σ₂₃] C) (c : R) (f : M →A[R] B) :
    h.comp (c • f) = σ₂₃ c • h.comp f := by
  ext x
  simp only [coe_smul', coe_comp', Function.comp_apply, Pi.smul_apply,
    ContinuousLinearMap.map_smulₛₗ]
#align continuous_linear_map.comp_smulₛₗ ContinuousLinearMap.comp_smulₛₗ

instance distribMulAction [ContinuousAdd B] : DistribMulAction S₃ (M →A[R] B) where
  smul_add a f g := ext fun x => smul_add a (f x) (g x)
  smul_zero _a := ext fun _x => smul_zero _
#align continuous_linear_map.distrib_mul_action ContinuousLinearMap.distribMulAction

end SMulMonoid

section SMul

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R R₃ S S₃ : Type*} [Semiring R] [Semiring R] [Semiring R₃] [Semiring S] [Semiring S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {B : Type*}
  [TopologicalSpace B] [AddCommMonoid B] [Module R B] {C : Type*} [TopologicalSpace C]
  [AddCommMonoid C] [Module R₃ C] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃] [Module S₃ C]
  [SMulCommClass R₃ S₃ C] [ContinuousConstSMul S₃ C] [Module S N₂] [ContinuousConstSMul S N₂]
  [SMulCommClass R S N₂] [Module S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃]
  {σ₁₂ : R →+* R} {σ₂₃ : R →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : B →SL[σ₂₃] C) (f g : M →A[R] B) (x y z : M)

/-- `ContinuousLinearMap.prod` as an `Equiv`. -/
@[simps apply]
def prodEquiv : (M →A[R] N₂) × (M →A[R] N₃) ≃ (M →A[R] N₂ × N₃) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align continuous_linear_map.prod_equiv ContinuousLinearMap.prodEquiv
#align continuous_linear_map.prod_equiv_apply ContinuousLinearMap.prodEquiv_apply

theorem prod_ext_iff {f g : M × N₂ →A[R] N₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl
#align continuous_linear_map.prod_ext_iff ContinuousLinearMap.prod_ext_iff

@[ext]
theorem prod_ext {f g : M × N₂ →A[R] N₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩
#align continuous_linear_map.prod_ext ContinuousLinearMap.prod_ext

variable [ContinuousAdd B] [ContinuousAdd C] [ContinuousAdd N₂]

instance module : Module S₃ (M →SL[σ₁₃] C) where
  zero_smul _ := ext fun _ => zero_smul _ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
#align continuous_linear_map.module ContinuousLinearMap.module

instance isCentralScalar [Module S₃ᵐᵒᵖ C] [IsCentralScalar S₃ C] :
    IsCentralScalar S₃ (M →SL[σ₁₃] C) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
#align continuous_linear_map.is_central_scalar ContinuousLinearMap.isCentralScalar

variable (S) [ContinuousAdd N₃]

/-- `ContinuousLinearMap.prod` as a `LinearEquiv`. -/
@[simps apply]
def prodₗ : ((M →A[R] N₂) × (M →A[R] N₃)) ≃ₗ[S] M →A[R] N₂ × N₃ :=
  { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }
#align continuous_linear_map.prodₗ ContinuousLinearMap.prodₗ
#align continuous_linear_map.prodₗ_apply ContinuousLinearMap.prodₗ_apply

/-- The coercion from `M →A[R] B` to `M →ₐ[R] B`, as a linear map. -/
@[simps]
def coeLM : (M →A[R] N₃) →ₐ[S] M →ₐ[R] N₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f
#align continuous_linear_map.coe_lm ContinuousLinearMap.coeLM
#align continuous_linear_map.coe_lm_apply ContinuousLinearMap.coeLM_apply

variable {S} (σ₁₃)

/-- The coercion from `M →SL[σ] B` to `M →ₛₗ[σ] B`, as a linear map. -/
@[simps]
def coeLMₛₗ : (M →SL[σ₁₃] C) →ₐ[S₃] M →ₛₗ[σ₁₃] C where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f
#align continuous_linear_map.coe_lmₛₗ ContinuousLinearMap.coeLMₛₗ
#align continuous_linear_map.coe_lmₛₗ_apply ContinuousLinearMap.coeLMₛₗ_apply

end SMul

section SMulRightₗ

variable {R S T M B : Type*} [Semiring R] [Semiring S] [Semiring T] [Module R S]
  [AddCommMonoid B] [Module R B] [Module S B] [IsScalarTower R S B] [TopologicalSpace S]
  [TopologicalSpace B] [ContinuousSMul S B] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd B] [Module T B] [ContinuousConstSMul T B] [SMulCommClass R T B]
  [SMulCommClass S T B]

/-- Given `c : E →A[𝕜] 𝕜`, `c.smulRightₗ` is the linear map from `F` to `E →A[𝕜] F`
sending `f` to `fun e => c e • f`. See also `ContinuousLinearMap.smulRightL`. -/
def smulRightₗ (c : M →A[R] S) : B →ₐ[T] M →A[R] B where
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
theorem coe_smulRightₗ (c : M →A[R] S) : ⇑(smulRightₗ c : B →ₐ[T] M →A[R] B) = c.smulRight :=
  rfl
#align continuous_linear_map.coe_smul_rightₗ ContinuousLinearMap.coe_smulRightₗ

end SMulRightₗ

section CommRing

variable {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {B : Type*}
  [TopologicalSpace B] [AddCommGroup B] {C : Type*} [TopologicalSpace C] [AddCommGroup C]
  [Module R M] [Module R B] [Module R C] [ContinuousConstSMul R C]

variable [TopologicalAddGroup B] [ContinuousConstSMul R B]

instance algebra : Algebra R (B →A[R] B) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _
#align continuous_linear_map.algebra ContinuousLinearMap.algebra

@[simp] theorem algebraMap_apply (r : R) (m : B) : algebraMap R (B →A[R] B) r m = r • m := rfl

end CommRing

section RestrictScalars

variable {A M B : Type*} [Ring A] [AddCommGroup M] [AddCommGroup B] [Module A M] [Module A B]
  [TopologicalSpace M] [TopologicalSpace B] (R : Type*) [Ring R] [Module R M] [Module R B]
  [LinearMap.CompatibleSMul M B R A]

/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `LinearMap.CompatibleSMul M B R A` to match assumptions of
`LinearMap.map_smul_of_tower`. -/
def restrictScalars (f : M →A[A] B) : M →A[R] B :=
  ⟨(f : M →ₐ[A] B).restrictScalars R, f.continuous⟩
#align continuous_linear_map.restrict_scalars ContinuousLinearMap.restrictScalars

variable {R}

@[simp] -- @[norm_cast] -- Porting note: This theorem can't be a `norm_cast` theorem.
theorem coe_restrictScalars (f : M →A[A] B) :
    (f.restrictScalars R : M →ₐ[R] B) = (f : M →ₐ[A] B).restrictScalars R :=
  rfl
#align continuous_linear_map.coe_restrict_scalars ContinuousLinearMap.coe_restrictScalars

@[simp]
theorem coe_restrictScalars' (f : M →A[A] B) : ⇑(f.restrictScalars R) = f :=
  rfl
#align continuous_linear_map.coe_restrict_scalars' ContinuousLinearMap.coe_restrictScalars'

@[simp]
theorem restrictScalars_zero : (0 : M →A[A] B).restrictScalars R = 0 :=
  rfl
#align continuous_linear_map.restrict_scalars_zero ContinuousLinearMap.restrictScalars_zero

section

variable [TopologicalAddGroup B]

@[simp]
theorem restrictScalars_add (f g : M →A[A] B) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_add ContinuousLinearMap.restrictScalars_add

@[simp]
theorem restrictScalars_neg (f : M →A[A] B) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_neg ContinuousLinearMap.restrictScalars_neg

end

variable {S : Type*}
variable [Ring S] [Module S B] [ContinuousConstSMul S B] [SMulCommClass A S B]
  [SMulCommClass R S B]

@[simp]
theorem restrictScalars_smul (c : S) (f : M →A[A] B) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_smul ContinuousLinearMap.restrictScalars_smul

variable (A M B R S)
variable [TopologicalAddGroup B]

/-- `ContinuousLinearMap.restrictScalars` as a `LinearMap`. See also
`ContinuousLinearMap.restrictScalarsL`. -/
def restrictScalarsₗ : (M →A[A] B) →ₐ[S] M →A[R] B where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul
#align continuous_linear_map.restrict_scalarsₗ ContinuousLinearMap.restrictScalarsₗ

variable {A M B R S}

@[simp]
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M B R S) = restrictScalars R :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsₗ ContinuousLinearMap.coe_restrictScalarsₗ

end RestrictScalars

end ContinuousAlgHom



end

end TopologicalAlgebra
