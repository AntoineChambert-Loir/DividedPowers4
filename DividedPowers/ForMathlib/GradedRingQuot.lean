import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.QuotientOperations

section Classes

section LinearMap

variable {R : Type _} [Semiring R]

variable {β γ : Type _} [AddCommMonoid β] [Module R β] [AddCommMonoid γ] [Module R γ]

instance {F : Type _} [LinearMapClass F R β γ] : CoeTC F (β →ₗ[R] γ) where 
  coe h := {
    toFun := h
    map_add' := map_add h 
    map_smul' := map_smul h }

theorem LinearMap.coe_coe {F : Type _} [LinearMapClass F R β γ] (f : F) :
    ((f : β →ₗ[R] γ) : β → γ) = f :=
  rfl
#align linear_map.coe_coe LinearMap.coe_coe

theorem LinearMap.coe_coe' {F : Type _} [LinearMapClass F R β γ] (f : F) :
    ((f : β →ₗ[R] γ) : β →+ γ) = f :=
  rfl
#align linear_map.coe_coe' LinearMap.coe_coe'

example {F : Type _} [LinearMapClass F R β γ] (h : F) (b : β) : (h : β →ₗ[R] γ) b = h b :=
  rfl

end LinearMap

section AlgHom

variable {R : Type _} [CommSemiring R]

variable {β γ : Type _} [Semiring β] [Algebra R β] [Semiring γ] [Algebra R γ]

theorem AlgHom.to_linearMap_coe_coe {F : Type _} [AlgHomClass F R β γ] (h : F) :
    ((h : β →ₗ[R] γ) : β → γ) = h :=
  rfl
#align alg_hom.to_linear_map_coe_coe AlgHom.to_linearMap_coe_coe

end AlgHom

section NatModule

example {β : Type _} [AddCommMonoid β] : Module ℕ β :=
  AddCommMonoid.natModule

example {β γ : Type _} [AddCommMonoid β] [AddCommMonoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun r x => by simp only [map_nsmul, eq_natCast, Nat.cast_id] }

example {β γ : Type _} [AddCommMonoid β] [AddCommMonoid γ] (f : β →+ γ) : β →ₗ[ℕ] γ :=
  f.toNatLinearMap

example {β γ : Type _} [AddCommMonoid β] [AddCommMonoid γ] (f : β →ₗ[ℕ] γ) : β →+ γ :=
  f.toAddMonoidHom

example {β γ : Type _} [AddCommMonoid β] [AddCommMonoid γ] (f : β →ₗ[ℕ] γ) :
    f = f.toAddMonoidHom.toNatLinearMap :=
  LinearMap.ext fun _ => Eq.refl _

example {β γ : Type _} [AddCommMonoid β] [AddCommMonoid γ] (f : β →+ γ) :
    f = f.toNatLinearMap.toAddMonoidHom :=
  AddMonoidHom.ext fun _ => Eq.refl _

end NatModule

section IntModule

example {β : Type _} [AddCommGroup β] : Module ℤ β :=
  AddCommGroup.intModule β

example {β γ : Type _} [AddCommGroup β] [AddCommGroup γ] (f : β →+ γ) : β →ₗ[ℤ] γ :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun r x => by simp only [eq_intCast, Int.cast_id, map_zsmul f r x] }

example {β γ : Type _} [AddCommGroup β] [AddCommGroup γ] (f : β →+ γ) : β →ₗ[ℤ] γ :=
  f.toIntLinearMap

end IntModule

section DirectSum

variable {ι : Type _} [DecidableEq ι]

variable {R : Type _} [Semiring R]

/-- The components of a direct sum, as add_monoid_hom -/
def DirectSum.component' {β : ι → Type _} [∀ i, AddCommMonoid (β i)] (i : ι) :
    DirectSum ι β →+ β i :=
  DirectSum.component ℕ ι β i
#align direct_sum.component' DirectSum.component'

theorem DirectSum.component'_eq {β : ι → Type _} [∀ i, AddCommMonoid (β i)] (x : DirectSum ι β)
    (i : ι) : DirectSum.component' i x = x i :=
  rfl
#align direct_sum.component'_eq DirectSum.component'_eq

theorem DirectSum.eq_iff_component'_eq {β : ι → Type _} [∀ i, AddCommMonoid (β i)]
    (x y : DirectSum ι β) : x = y ↔ ∀ i, DirectSum.component' i x = DirectSum.component' i y :=
  DirectSum.ext_iff ℕ
#align direct_sum.eq_iff_component'_eq DirectSum.eq_iff_component'_eq

-- add_monoid_hom from a direct_sum to an add_comm_monoid
example {β : ι → Type _} [∀ i, AddCommMonoid (β i)] {γ : Type _} [AddCommMonoid γ]
    (h : ∀ i, β i →+ γ) : DirectSum ι β →+ γ :=
  DirectSum.toAddMonoid h

-- linear_map from a direct_sum to a module
example {β : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] {γ : Type _}
    [AddCommMonoid γ] [Module R γ] (h : ∀ i, β i →ₗ[R] γ) : DirectSum ι β →ₗ[R] γ :=
  DirectSum.toModule R ι γ h

-- linear_map, with classes :
example {β : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] {γ : Type _}
    [AddCommMonoid γ] [Module R γ] {F : ∀ _ : ι, Type _} [∀ i, LinearMapClass (F i) R (β i) γ]
    (h : ∀ i, F i) : DirectSum ι β →ₗ[R] γ :=
  DirectSum.toModule R ι γ fun i => h i

-- ⟨h i, map_add _, map_smulₛₗ _⟩
example {β : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] {γ : Type _}
    [AddCommMonoid γ] [Module R γ] {F : ∀ _ : ι, Type _} [∀ i, LinearMapClass (F i) R (β i) γ]
    (h : ∀ i, F i) : DirectSum ι β →ₗ[R] γ :=
  DirectSum.toModule R ι γ fun i => h i

/- Four versions of a direct sum of maps 
   direct_sum.map' : for add_monoid_hom 
   direct_sum.lmap'  : for linear_map
   the unprimed versions are defined in terms of classes 
   In principle, the latter should suffice. -/
/-- Linear_maps from a direct sum to a direct sum given by families of linear_maps-/
def DirectSum.map {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    {F : ∀ _ : ι, Type _} [∀ i, AddMonoidHomClass (F i) (β i) (γ i)] (h : ∀ i, F i) :
    DirectSum ι β →+ DirectSum ι γ :=
  DirectSum.toAddMonoid fun i => AddMonoidHom.comp (DirectSum.of γ i) (h i)
#align direct_sum.map DirectSum.map

def DirectSum.lmap {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] {F : ∀ _ : ι, Type _}
    [∀ i, LinearMapClass (F i) R (β i) (γ i)] (h : ∀ i, F i) : DirectSum ι β →ₗ[R] DirectSum ι γ :=
  DirectSum.toModule R ι (DirectSum ι γ) fun i =>
    LinearMap.comp (DirectSum.lof R ι γ i) (h i : β i →ₗ[R] γ i)
#align direct_sum.lmap DirectSum.lmap

def DirectSum.map' {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    (h : ∀ i, β i →+ γ i) : DirectSum ι β →+ DirectSum ι γ :=
  DirectSum.toAddMonoid fun i => AddMonoidHom.comp (DirectSum.of γ i) (h i)
#align direct_sum.map' DirectSum.map'

example {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    (h : ∀ i, β i →+ γ i) : DirectSum.map' h = DirectSum.map h :=
  rfl

def DirectSum.lmap' {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] (h : ∀ i, β i →ₗ[R] γ i) :
    DirectSum ι β →ₗ[R] DirectSum ι γ :=
  DirectSum.toModule R ι _ fun i => LinearMap.comp (DirectSum.lof R ι γ i) (h i)
#align direct_sum.lmap' DirectSum.lmap'

example {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    -- [Π i, module R (β i)]
    [∀ i, AddCommMonoid (γ i)]
    -- [Π i, module R (γ i)]
    (h : ∀ i, β i →+ γ i) :
    DirectSum ι β →+ DirectSum ι γ :=
  DirectSum.map' h

example {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    -- [Π i, module ℕ (β i)]
    [∀ i, AddCommMonoid (γ i)]
    -- [Π i, module ℕ (γ i)]
    (h : ∀ i, β i →+ γ i) :
    DirectSum ι β →+ DirectSum ι γ :=
  DirectSum.lmap' fun i => ((h i).toNatLinearMap : β i →ₗ[ℕ] γ i)

theorem DirectSum.map'_eq_lmap'_toAddMonoidHom {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    -- [Π i, module R (β i)]
    [∀ i, AddCommMonoid (γ i)]
    -- [Π i, module R (γ i)]
    (h : ∀ i, β i →+ γ i) :
    DirectSum.map' h = (DirectSum.lmap' fun i => (h i).toNatLinearMap).toAddMonoidHom :=
  rfl
#align direct_sum.map'_eq_lmap'_to_add_monoid_hom DirectSum.map'_eq_lmap'_toAddMonoidHom

theorem DirectSum.lmap'_toAddMonoidHom_eq_map' {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ i, Module R (β i)] [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)]
    (h : ∀ i, β i →ₗ[R] γ i) :
    (DirectSum.lmap' h).toAddMonoidHom = DirectSum.map' fun i => (h i).toAddMonoidHom :=
  rfl
#align direct_sum.lmap'_to_add_monoid_hom_eq_map' DirectSum.lmap'_toAddMonoidHom_eq_map'

example {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] (h : ∀ i, β i →ₗ[R] γ i) :
    DirectSum.lmap' h = DirectSum.lmap h := by rfl

-- Lemmas to help computation
theorem DirectSum.map_of {β γ : ι → Type _} 
    [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    {F : ∀ _, Type _} [∀ i, AddMonoidHomClass (F i) (β i) (γ i)] 
    (h : ∀ i, F i) (i : ι) (x : β i) :
  DirectSum.map h (DirectSum.of β i x) = DirectSum.of γ i (h i x) := by
  simp only [DirectSum.map, DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe]
  rfl
#align direct_sum.map_of DirectSum.map_of

/- unknown constant…
lemma direct_sum.map_apply {β γ : ι → Type*} 
  [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (γ i)]
  {F : Π i, Type*} [Π i, add_monoid_hom_class (F i) (β i) (γ i)] 
  (h : Π i, F i) (x : direct_sum ι β) (i : ι) : 
  direct_sum.map h x i = h i (x i) :=
begin
  let f : direct_sum ι β →+ γ i := 
  { to_fun := λ x, direct_sum.map' h x i,
    map_zero' := by simp, 
    map_add' := by simp, },
  let g : direct_sum ι β →+ γ i := 
  { to_fun := λ y, h i (y i), 
    map_zero' := by simp,
    map_add' := by simp, } ,
  change f x = g x,
  suffices : f = g, 
  rw this, 
  apply direct_sum.add_hom_ext , 
  intros j y,
  simp [f, g, direct_sum.map'_of], 
  by_cases hj : j = i,
  { rw ← hj, simp only [direct_sum.of_eq_same], },
  { simp only [direct_sum.of_eq_of_ne _ j i _ hj, map_zero], },
end
-/
theorem DirectSum.map'_of {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    (h : ∀ i, β i →+ γ i) (i : ι) (x : β i) :
    DirectSum.map' h (DirectSum.of β i x) = DirectSum.of γ i (h i x) := by
  dsimp only [DirectSum.map']
  rw [DirectSum.toAddMonoid_of]
  simp only [AddMonoidHom.coe_comp]
  rfl
#align direct_sum.map'_of DirectSum.map'_of

theorem DirectSum.lmap'_lof {β γ : ι → Type _} 
    [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    [∀ i, Module R (β i)] [∀ i, Module R (γ i)] (h : ∀ i, β i →ₗ[R] γ i) 
    (i : ι) (x : β i) :
  DirectSum.lmap' h (DirectSum.lof R ι β i x) = 
    DirectSum.lof R ι γ i (h i x) := by
  dsimp only [DirectSum.lmap']
  rw [DirectSum.toModule_lof]
  simp only [LinearMap.coe_comp]
  rfl
#align direct_sum.lmap'_lof DirectSum.lmap'_lof

theorem DirectSum.lmap'_apply {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (β i)] [∀ i, Module R (γ i)] 
    (h : ∀ i, β i →ₗ[R] γ i) (x : DirectSum ι β) (i : ι) : 
  DirectSum.lmap' h x i = h i (x i) := by
  simp only [DirectSum.apply_eq_component R]
  rw [← LinearMap.comp_apply]
  rw [← LinearMap.comp_apply]
  revert x; rw [← LinearMap.ext_iff]
  apply DirectSum.linearMap_ext
  intro j; ext y
  simp only [LinearMap.comp_apply]
  rw [DirectSum.lmap'_lof]
  simp only [DirectSum.lof_eq_of]
  simp only [← DirectSum.apply_eq_component]
  by_cases hji : j = i
  · rw [← hji]; simp only [DirectSum.of_eq_same]
  · simp only [DirectSum.of_eq_of_ne _ j i _ hji, map_zero]
#align direct_sum.lmap'_apply DirectSum.lmap'_apply

theorem DirectSum.toModule_comp_lmap'_eq {β γ : ι → Type _} {δ : Type _} 
    [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)] [AddCommMonoid δ] 
    [∀ i, Module R (β i)] [∀ i, Module R (γ i)] [Module R δ] 
    (h : ∀ i, β i →ₗ[R] γ i) (f : ∀ i, γ i →ₗ[R] δ) (x : DirectSum ι β) :
  DirectSum.toModule R ι δ f (DirectSum.lmap' h x) =
    DirectSum.toModule R ι δ (fun i => (f i).comp (h i)) x :=
  by
  rw [← LinearMap.comp_apply]
  revert x
  rw [← LinearMap.ext_iff]
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro b
  simp
  rw [DirectSum.lmap'_lof]
  rw [DirectSum.toModule_lof]
#align direct_sum.to_module_comp_lmap'_eq DirectSum.toModule_comp_lmap'_eq

theorem DirectSum.map'_apply {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : γ i), Decidable (x ≠ 0)] 
    (h : ∀ i, β i →+ γ i) (x : DirectSum ι β) (i : ι) :
  DirectSum.map' h x i = h i (x i) := by
  let f : DirectSum ι β →+ γ i :=
    { toFun := fun x => DirectSum.map' h x i
      map_zero' := by simp only [map_zero, DirectSum.zero_apply]
      map_add' := by simp only [map_add, DirectSum.add_apply, eq_self_iff_true, forall_const] }
  let g : DirectSum ι β →+ γ i :=
    { toFun := fun y => h i (y i)
      map_zero' := by simp only [DirectSum.zero_apply, map_zero]
      map_add' := by simp only [DirectSum.add_apply, map_add, eq_self_iff_true, forall_const] }
  change f x = g x
  suffices : f = g
  rw [this]
  apply DirectSum.addHom_ext
  intro j y
  simp [DirectSum.map'_of]
  by_cases hj : j = i
  · rw [← hj]; simp only [DirectSum.of_eq_same]
  · simp only [DirectSum.of_eq_of_ne _ j i _ hj, map_zero]
#align direct_sum.map'_apply DirectSum.map'_apply

-- Lemmas using direct_sum.mk   : could probably be removed
theorem DirectSum.mk_apply {β : ι → Type _} [∀ i, AddCommMonoid (β i)] (s : Finset ι)
    (f : ∀ i : s, β ↑i) (i : ι) :
    DirectSum.mk β s f i = if h : i ∈ s then f ⟨i, h⟩ else 0 :=
  rfl
#align direct_sum.mk_apply DirectSum.mk_apply

theorem DirectSum.mk_eq_sum' {β : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (s : Finset ι) (f : ∀ i, β i) :
    (DirectSum.mk β s (fun i => f i)) = 
      s.sum (fun i => DirectSum.of β i (f i)) := by
  simp only [Finset.coe_sort_coe]
  apply DFinsupp.ext
  intro i
  rw [DirectSum.mk_apply, DFinsupp.finset_sum_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single_of_mem i hi]
    · rw [← DirectSum.lof_eq_of ℕ, DirectSum.lof_apply]
    · intro j _ hij
      exact DirectSum.of_eq_of_ne _ _ _ _ hij
  · apply symm
    apply Finset.sum_eq_zero
    intro j hj
    exact DirectSum.of_eq_of_ne _ _ _ _ (ne_of_mem_of_not_mem hj hi)
#align direct_sum.mk_eq_sum' DirectSum.mk_eq_sum'

theorem DFinsupp.mk_eq_sum {β : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (s : Finset ι) (f : ∀ i, β i) :
    (DFinsupp.mk s fun i => f i) = s.sum fun i => DirectSum.of β i (f i) :=
  by
  ext i
  simp only [DFinsupp.mk_apply, DFinsupp.finset_sum_apply]
  
  split_ifs with hi
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single_of_mem i hi, 
      DirectSum.of_eq_same]
    . intro j _ hij
      rw [DirectSum.of_eq_of_ne]
      exact hij
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_zero]
    intro j hj
    rw [DirectSum.of_eq_of_ne]
    intro hij; apply hi; rw [← hij]; exact hj
#align dfinsupp.mk_eq_sum DFinsupp.mk_eq_sum

theorem DirectSum.mk_eq_sum {β : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] 
    (s : Finset ι) (x : ∀ i : s, β i) :
  DirectSum.mk β s x =
    s.sum fun i => DirectSum.of β i (if h : i ∈ s then x ⟨i, h⟩ else 0) := by
  apply DFinsupp.ext
  intro i
  rw [DirectSum.mk_apply]
  split_ifs with hi 
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single i]
    · rw [DirectSum.of_eq_same, dif_pos hi]
    · intro j _ hji
      rw [DirectSum.of_eq_of_ne]
      exact hji
    · intro his
      rw [DirectSum.of_eq_same, dif_neg his]
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_zero]
    intro j hj
    rw [DirectSum.of_eq_of_ne]
    exact ne_of_mem_of_not_mem hj hi
#align direct_sum.mk_eq_sum DirectSum.mk_eq_sum

theorem DirectSum.toAddMonoid_mk {β : ι → Type _} [∀ i, AddCommMonoid (β i)] 
    {γ : Type _} [AddCommMonoid γ] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] 
    [∀ x : γ, Decidable (x ≠ 0)]
    (ψ : ∀ i, β i →+ γ) (s : Finset ι) (x : ∀ i : s, β i) :
  DirectSum.toAddMonoid ψ (DirectSum.mk β s x) =
    s.sum fun i => ψ i (if h : i ∈ s then x ⟨i, h⟩ else 0) :=
  by
  rw [DirectSum.mk_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [DirectSum.toAddMonoid_of]
#align direct_sum.to_add_monoid_mk DirectSum.toAddMonoid_mk

theorem DirectSum.map'_apply'_old {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : γ i), Decidable (x ≠ 0)] 
    (h : ∀ i, β i →+ γ i) (x : DirectSum ι β) :
  DirectSum.map' h x = DirectSum.mk γ x.support fun i => h i (x i) := by
  apply DFinsupp.ext
  intro i
  conv_lhs => rw [← DirectSum.sum_support_of β x, map_sum, DFinsupp.finset_sum_apply]
  rw [DirectSum.mk_eq_sum]
  simp only [DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite]
  rw [DFinsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  . simp only [h, map_zero, zero_apply]
  . by_cases hij : j = i
    . rw [hij]
      simp only [of_eq_same]
      simp [map']
    . rw [of_eq_of_ne]
      simp [map']
      rw [of_eq_of_ne]
      exact hij
      exact hij
#align direct_sum.map'_apply'_old DirectSum.map'_apply'_old

def zoto {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] [∀ (i : ι) (x : γ i), Decidable (x ≠ 0)]
    {F : ∀ _, Type _} [∀ i, AddMonoidHomClass (F i) (β i) (γ i)] (h : ∀ i, F i)
    (B : DirectSum ι β) : ∀ i : (B.support : Set ι), γ i := fun i => (h i) (B i)
#align zoto zoto

theorem DirectSum.map_apply' {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : γ i), Decidable (x ≠ 0)] {F : ∀ _, Type _}
    [∀ i, AddMonoidHomClass (F i) (β i) (γ i)] (h : ∀ i, F i) (x : DirectSum ι β) :
    DirectSum.map h x = DirectSum.mk γ x.support (zoto h x) := by
  -- (λ i, (h i) (x i))  gives `unknown fresh 0._ ` error
  conv_lhs => rw [← DirectSum.sum_support_of β x]
  rw [map_sum]
  simp_rw [DirectSum.map_of]
  apply symm
  convert DirectSum.mk_eq_sum x.support fun i => (h i) (x i)
  rw [dif_pos]
  assumption
#align direct_sum.map_apply' DirectSum.map_apply'

end DirectSum

section GradedQuot

variable (R : Type _) [CommRing R]

variable {ι : Type _} [DecidableEq ι] [AddMonoid ι]

variable {A : Type _} [CommRing A] [DecidableEq A] [Algebra R A]

/-  graded_algebra does not work with `submodule_class`

variables {σ : Type*} [set_like σ A] [add_submonoid_class σ A] 
[submodule_class σ R A] 

variable (𝒜 : ι → σ) [h𝒜 : graded_algebra 𝒜]
-/
section

variable {σ : Type _} [SetLike σ A] [AddSubmonoidClass σ A] [SMulMemClass σ R A]

variable (ℬ : ι → σ)

@[reducible]
def GradedAlgebra' :=
  @GradedRing _ A _ _ _ _ _ _ ℬ
#align graded_algebra' GradedAlgebra'

variable [hℬ : GradedAlgebra' ℬ]

end

variable (𝒜 : ι → Submodule R A)

section Ideal

variable (I : Ideal A)

-- variables [h𝒜 : graded_algebra 𝒜] (hI: ideal.is_homogeneous 𝒜 I)
-- It seems I start understanding what I'm doing
example : SemilinearMapClass (A →+* A ⧸ I) (RingHom.id ℤ) A (A ⧸ I) :=
  { coe := fun f a => f a
    coe_injective' := fun f g hfg => RingHom.ext fun x => Function.funext_iff.mp hfg x
    map_add := map_add
    map_smulₛₗ := fun f r a => by
      simp only [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, Int.cast_id] }

-- This will probably be useless in the end, because I "R-modulify" everything
-- ideal.quotient.mk vs ideal.quotient.mkₐ
example (I : Ideal A) (r : R) (a : A) : r • Ideal.Quotient.mk I a = Ideal.Quotient.mk I (r • a) :=
  map_smul (Ideal.Quotient.mkₐ R I) r a

/-- The graded pieces of A ⧸ I -/
def quotSubmodule : ι → Submodule R (A ⧸ I) := fun i => Submodule.map (Ideal.Quotient.mkₐ R I) (𝒜 i)
#align quot_submodule quotSubmodule

/- broken by the passage to modules…
-- I think this one can be erased, since we have the laux version
/-- The decomposition at the higher level -/
def quot_decompose_aux [graded_ring 𝒜] :
  A → direct_sum ι (λ (i : ι), ↥(quot_submodule R 𝒜 I i)) := λ a,
begin
  refine (direct_sum.map _) (direct_sum.decompose_linear_equiv 𝒜 a),
  exact λ i, {
  to_fun := λu, ⟨ideal.quotient.mk I ↑u,
  begin
    simp [quot_submodule, submodule.mem_map],
    exact ⟨↑u, u.prop, rfl⟩,
  end⟩,
  map_zero' := by simp only [←subtype.coe_inj, submodule.coe_zero, map_zero, submodule.coe_mk],
  map_add' := λ u v, by simp only [←subtype.coe_inj, submodule.coe_add, map_add,
                add_mem_class.mk_add_mk] },
end
-/
def quotCompMap (i : ι) : ↥(𝒜 i) →ₗ[R] ↥(quotSubmodule R 𝒜 I i)
    where
  toFun u :=
    ⟨Ideal.Quotient.mkₐ R I ↑u, by
      rw [quotSubmodule, Submodule.mem_map]
      exact ⟨↑u, u.prop, rfl⟩⟩
  map_add' u v := by
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add, 
      Ideal.Quotient.mkₐ_eq_mk, AddSubmonoid.mk_add_mk]
  map_smul' r u := by
    simp only [SetLike.val_smul, map_smul, Ideal.Quotient.mkₐ_eq_mk, RingHom.id_apply]
    rfl
#align quot_comp_map quotCompMap

-- lemma quot_comp_map_surjective (i : ι) : function.surjective (quot_comp_map R 𝒜 I i) := sorry
example : Submodule R A := I.restrictScalars R

/-- The decomposition at the higher level -/
def quotDecomposeLaux [GradedAlgebra 𝒜] :
    A →ₗ[R] DirectSum ι fun i : ι => ↥(quotSubmodule R 𝒜 I i) :=
  LinearMap.comp (DirectSum.lmap' (quotCompMap R 𝒜 I)) (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap
#align quot_decompose_laux quotDecomposeLaux

theorem quotDecomposeLaux_of_mem_eq_zero [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) (x : A)
    (hx : x ∈ I) (i : ι) : ((quotDecomposeLaux R 𝒜 I) x) i = 0 :=
  by
  rw [quotDecomposeLaux, LinearMap.comp_apply, DirectSum.lmap'_apply, quotCompMap]
  simp only [Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toLinearMap_apply, 
    DirectSum.decomposeAlgEquiv_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mk_eq_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI i hx
#align quot_decompose_laux_of_mem_eq_zero quotDecomposeLaux_of_mem_eq_zero

theorem quotDecomposeLaux_ker [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    I.restrictScalars R ≤ LinearMap.ker (quotDecomposeLaux R 𝒜 I) :=
  by
  intro x hx
  simp only [Submodule.restrictScalars_mem] at hx 
  rw [LinearMap.mem_ker]
  apply DFinsupp.ext
  intro i
  simp only [DirectSum.zero_apply]
  apply quotDecomposeLaux_of_mem_eq_zero R 𝒜 I hI x hx
#align quot_decompose_laux_ker quotDecomposeLaux_ker

/-- The decomposition at the higher level -/
def quotDecompose [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    A ⧸ I →ₗ[R] DirectSum ι fun i : ι => ↥(quotSubmodule R 𝒜 I i) := by
  apply @Submodule.liftQ R A _ _ _ (I.restrictScalars R) R 
    (DirectSum ι fun i => quotSubmodule R 𝒜 I i)
    _ _ _ (RingHom.id R) (quotDecomposeLaux R 𝒜 I)
  -- without explicit arguments, it is too slow
  -- apply submodule.liftq (I.restrict_scalars R) (quot_decompose_laux R 𝒜 I),
  apply quotDecomposeLaux_ker R 𝒜 I hI
#align quot_decompose quotDecompose

theorem quotDecomposeLaux_apply_mk [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) 
    (a : A) :
  quotDecompose R 𝒜 I hI (Ideal.Quotient.mk I a) = quotDecomposeLaux R 𝒜 I a := by
  rw [quotDecompose]
  have : Ideal.Quotient.mk I a = Submodule.Quotient.mk a := rfl
  rw [this]
  -- exact Submodule.liftQ_apply (I.restrictScalars R) (quotDecomposeLaux R 𝒜 I) a
  -- apply works
  apply Submodule.liftQ_apply
#align quot_decompose_laux_apply_mk quotDecomposeLaux_apply_mk

def quotDecomposition_left_inv' [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
  Function.LeftInverse 
    (DirectSum.coeLinearMap (quotSubmodule R 𝒜 I))
    (quotDecompose R 𝒜 I hI) := by
  intro x
  obtain ⟨(a : A), rfl⟩ := Ideal.Quotient.mk_surjective x
  let h𝒜 : DirectSum.Decomposition 𝒜 := by infer_instance
  have ha : (DirectSum.coeLinearMap 𝒜) (DirectSum.decomposeAlgEquiv 𝒜 a) = a
  . conv_rhs => rw [← h𝒜.left_inv a]
  conv_rhs => 
    change Submodule.mkQ (I.restrictScalars R) a
    rw [← ha]
    simp only [← LinearMap.comp_apply]
  conv_lhs =>
    rw [quotDecomposeLaux_apply_mk, quotDecomposeLaux, LinearMap.comp_apply]
    simp only [AlgEquiv.toLinearMap_apply] 
    simp only [← LinearMap.comp_apply]
  generalize DirectSum.decomposeAlgEquiv 𝒜 a = b
  revert b
  suffices h : (LinearMap.comp (DirectSum.coeLinearMap (quotSubmodule R 𝒜 I)) (DirectSum.lmap' (quotCompMap R 𝒜 I))) =
    (LinearMap.comp (Submodule.mkQ (Submodule.restrictScalars R I)) (DirectSum.coeLinearMap 𝒜))
  intro b ; rw [h] ; rfl
  apply DirectSum.linearMap_ext
  intro i
  ext x
  dsimp
  change _ = (Submodule.mkQ (Submodule.restrictScalars R I)) (_)
  simp only [DirectSum.lmap'_lof]
  simp only [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  simp only [Submodule.mkQ_apply]
  rfl

def quotDecomposition_left_inv [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
  Function.LeftInverse 
    (DirectSum.coeAddMonoidHom (quotSubmodule R 𝒜 I))
    (quotDecompose R 𝒜 I hI) := by
  rw [Function.leftInverse_iff_comp]
  change (DirectSum.coeLinearMap _) ∘ _ = _
  rw [← Function.leftInverse_iff_comp]
  exact quotDecomposition_left_inv' R 𝒜 I hI
#align quot_decomposition_left_inv quotDecomposition_left_inv

def quotDecomposition_right_inv' [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
  Function.RightInverse 
    (DirectSum.coeLinearMap (quotSubmodule R 𝒜 I))
    (quotDecompose R 𝒜 I hI) := by
  rw [Function.rightInverse_iff_comp, ← LinearMap.coe_comp]
  rw [← @LinearMap.id_coe R]
  apply congr_arg
  apply DirectSum.linearMap_ext
  intro i
  ext y
  obtain ⟨x, hx, hxy⟩ := y.prop
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_comp]
  simp only [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  rw [← hxy]
  rw [Ideal.Quotient.mkₐ_eq_mk]
  rw [quotDecomposeLaux_apply_mk]
  rw [quotDecomposeLaux]  
  simp only [LinearMap.coe_comp, Function.comp_apply]
  change DirectSum.lmap' _ (DirectSum.decompose 𝒜 x) = _
  suffices : DirectSum.decompose 𝒜 x = DirectSum.lof R ι (fun i => 𝒜 i) i (⟨x, hx⟩ : 𝒜 i)
  rw [this]
  rw [DirectSum.lmap'_lof, DirectSum.lof_eq_of]
  apply congr_arg₂ _ rfl
  rw [quotCompMap]
  simp only [Ideal.Quotient.mkₐ_eq_mk, Submodule.coe_mk, LinearMap.coe_mk]
  rw [← Subtype.coe_inj, Subtype.coe_mk]
  rw [← hxy]
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  rfl
  . conv_lhs => rw [← Subtype.coe_mk x hx]
    rw [DirectSum.decompose_coe, DirectSum.lof_eq_of]

def quotDecomposition_right_inv [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (quotSubmodule R 𝒜 I))
      (quotDecompose R 𝒜 I hI) := by
  rw [Function.rightInverse_iff_comp]
  change _ ∘ (DirectSum.coeLinearMap _) = _
  rw [← Function.rightInverse_iff_comp]
  exact quotDecomposition_right_inv' R 𝒜 I hI
#align quot_decomposition_right_inv quotDecomposition_right_inv

def quotDecomposition [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (quotSubmodule R 𝒜 I)
    where
  decompose' := quotDecompose R 𝒜 I hI
  left_inv := quotDecomposition_left_inv R 𝒜 I hI
  right_inv := quotDecomposition_right_inv R 𝒜 I hI
#align quot_decomposition quotDecomposition

theorem mem_quotSubmodule_iff (i : ι) (g : A ⧸ I) :
    g ∈ quotSubmodule R 𝒜 I i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = g := by
  rw [quotSubmodule, Submodule.mem_map, Ideal.Quotient.mkₐ_eq_mk]
#align mem_quot_submodule_iff mem_quotSubmodule_iff

/-- The quotient of a graded algebra by a homogeneous ideal, as a graded algebra -/
def gradedQuotAlg [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (quotSubmodule R 𝒜 I)
    where
  toDecomposition := quotDecomposition R 𝒜 I hI
  toGradedMonoid :=
    { one_mem := by
        rw [quotSubmodule, Submodule.mem_map]
        exact ⟨1, SetLike.one_mem_graded 𝒜, rfl⟩
      mul_mem := fun i j gi gj hgi hgj =>
        by
        rw [mem_quotSubmodule_iff] at hgi hgj ⊢
        obtain ⟨ai, hai, rfl⟩ := hgi
        obtain ⟨aj, haj, rfl⟩ := hgj
        exact ⟨ai * aj, SetLike.mul_mem_graded hai haj, map_mul _ _ _⟩ }
#align graded_quot_alg gradedQuotAlg

end Ideal

section Rel

/- THIS SECTION IS A MESS
ITS GOAL IS TO TRANSFER THE GRADED ALGEBRA STRUCTURE TO
THE CASE WHERE THE QUOTIENT IS DEFINED VIA A RELATION 

ALSO : 

-/


-- variable (𝒜 : ι → Submodule R A) 
-- variable [GradedAlgebra 𝒜]

variable (r : A → A → Prop)

variable {R}

/-- A relation is homogeneous iff r a b implies that a and b 
are homogeneous of the same degree -/
def RelIsHomogeneous :=
  ∀ {a b : A} (_ : r a b), ∃ i, a ∈ 𝒜 i ∧ b ∈ 𝒜 i
#align rel_is_homogeneous RelIsHomogeneous

/-- The ideal generated by a homogeneous relation is homogeneous -/
theorem _root_.IsHomogeneous_of_rel [GradedAlgebra 𝒜] (hr : RelIsHomogeneous 𝒜 r) : 
  Ideal.IsHomogeneous 𝒜 (Ideal.ofRel r):= by
  apply Ideal.homogeneous_span
  rintro x  ⟨a, b, ⟨h, heq⟩⟩
  obtain ⟨i, hi⟩ := hr h
  use i
  rw [eq_comm, ← sub_eq_iff_eq_add] at heq
  rw [← heq]
  apply Submodule.sub_mem _ hi.1 hi.2

/-- Adding the alg_hom component to the natural ring_equiv -/
def ringQuotEquivAlgIdealQuotient : RingQuot r ≃ₐ[R] A ⧸ Ideal.ofRel r :=
  { RingQuot.ringQuotEquivIdealQuotient r with
    commutes' := fun s => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe_apply, RingEquiv.coe_toEquiv]
      rw [← AlgHom.commutes (RingQuot.mkAlgHom R r), ←
        AlgHom.commutes (Ideal.Quotient.mkₐ R (Ideal.ofRel r)), Ideal.Quotient.mkₐ_eq_mk, ←
        RingQuot.ringQuotToIdealQuotient_apply r _, ← RingQuot.mkAlgHom_coe R r]
      rfl }
#align ring_quot_equiv_alg_ideal_quotient ringQuotEquivAlgIdealQuotient

/- example [decidable_eq (submodule R A)] (i : ι) : 
quot_submodule R 𝒜 (ideal.of_rel r) i = submodule.map ((ideal.quotient.mkₐ  R _).comp 
  (ring_quot.mk_alg_hom R r)) i :=
begin

end -/

-- TODO ? : Unclear of what remains to do 
-- Probably writing what we did for DPAlgebra in full generality
-- For the moment, it is commented out

/- 
def gradedQuotAlgRel [GradedAlgebra 𝒜] [DecidableEq (Submodule R A)] (hr : RelIsHomogeneous 𝒜 r) :
    GradedAlgebra fun i => Submodule.map (RingQuot.mkAlgHom R r) i :=
  sorry
#align graded_quot_alg_rel gradedQuotAlgRel

-/
end Rel

