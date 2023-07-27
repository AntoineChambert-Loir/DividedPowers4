import Mathlib.Algebra.Module.LinearMap
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.QuotientOperations

section RingQuot

variable {R A B : Type _} (r : A → A → Prop) 
  [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

example (f : A →ₐ[R] B) (M : Submodule R A) : Submodule R B :=
  M.map f.toLinearMap



end RingQuot

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


theorem DirectSum.lmap'_surjective {β γ : ι → Type _} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] (f : ∀ i, β i →ₗ[R] γ i) (h : ∀ i, Function.Surjective (f i)) :
  Function.Surjective (DirectSum.lmap' f) := by  
  intro c
  induction' c using DirectSum.induction_on with i xi x y hx hy
  . use 0
    rw [map_zero]
  . use DirectSum.of _ i (h i xi).choose
    rw [←DirectSum.lof_eq_of R, DirectSum.lmap'_lof, DirectSum.lof_eq_of]
    rw [(h i xi).choose_spec]
  . obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    use a + b
    simp only [map_add]

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

variable {ι : Type _} [DecidableEq ι] [AddCommMonoid ι]

variable {A : Type _} [CommRing A] [DecidableEq A] [Algebra R A]

/-  graded_algebra does not work with `submodule_class`
-/
section

variable {σ : Type _} [SetLike σ A] [AddSubmonoidClass σ A] [SMulMemClass σ R A]

variable (ℬ : ι → σ)

@[reducible]
def GradedAlgebra' := @GradedRing _ A _ _ _ _ _ _ ℬ
#align graded_algebra' GradedAlgebra'

variable [hℬ : GradedAlgebra' ℬ]

end

variable (𝒜 : ι → Submodule R A)


section HomogeneousRelation

variable {R}

variable (r : A → A → Prop)

/-- A relation is PureHomogeneous iff r a b implies that a and b 
are homogeneous of the same degree -/
def RelIsPureHomogeneous :=
  ∀ {a b : A} (_ : r a b), ∃ i, a ∈ 𝒜 i ∧ b ∈ 𝒜 i
#align rel_is_homogeneous RelIsPureHomogeneous

/-- The ideal generated by a pure homogeneous relation is homogeneous -/
theorem _root_.IsHomogeneous_of_rel_isPureHomogeneous [GradedAlgebra 𝒜] 
    (hr : RelIsPureHomogeneous 𝒜 r) : 
  Ideal.IsHomogeneous 𝒜 (Ideal.ofRel r):= by
  apply Ideal.homogeneous_span
  rintro x  ⟨a, b, ⟨h, heq⟩⟩
  obtain ⟨i, hi⟩ := hr h
  use i
  rw [eq_comm, ← sub_eq_iff_eq_add] at heq
  rw [← heq]
  apply Submodule.sub_mem _ hi.1 hi.2

/-- A relation is Homogeneous iff r a b implies that 
  the components of a and b are related by r -/
def RelIsHomogeneous [GradedAlgebra 𝒜] : Prop := ∀ {a b : A} (_ : r a b),
  ∀ i, r ((DirectSum.decomposeAlgEquiv 𝒜).toLinearMap a i) ((DirectSum.decomposeAlgEquiv 𝒜).toLinearMap b i)

/-- The ring relation generated by a homogeneous relation is homogeneous -/

lemma RingConGen.Rel.sum {α : Type _} [Ring α] (r : RingCon α) 
    {ι : Type _} [DecidableEq ι] {a b : ι → α} (s : Finset ι) 
    (hs : ∀ i ∈ s, r (a i) (b i)) :
  RingConGen.Rel r (s.sum a) (s.sum b) := by
  revert hs
  induction' s using Finset.induction_on with j t hj ht hjt
  . intro _
    simp only [Finset.sum_empty]
    apply RingConGen.Rel.refl
  . intro hs
    simp only [Finset.sum_insert hj]
    apply RingConGen.Rel.add
    . apply RingConGen.Rel.of 
      apply hs j (Finset.mem_insert_self j t)
    . apply ht
      intro i hi
      apply hs i (Finset.mem_insert_of_mem hi)

theorem DFinsupp.sum_of_support_le 
    {M : Type _} [AddCommMonoid M]
    {ι : Type v} [dec_ι : DecidableEq ι] (β : ι → Type w) 
    [inst : (i : ι) → AddCommMonoid (β i)] 
    [inst : (i : ι) → (x : β i) → Decidable (x ≠ 0)] 
    (h : (i : ι) → (β i →+ M))
    (x : DFinsupp β)
    (s : Finset ι) (hs : DFinsupp.support x ⊆ s) :
  x.sum (fun i y => h i y) = s.sum (fun i => h i (x i)) := by
  simp only [DFinsupp.sum]
  apply Finset.sum_subset hs
  . intro i _ hi'
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
    rw [hi', map_zero]

theorem DirectSum.sum_of_support_le 
    {ι : Type v} [dec_ι : DecidableEq ι] (β : ι → Type w) 
    [inst : (i : ι) → AddCommMonoid (β i)] 
    [inst : (i : ι) → (x : β i) → Decidable (x ≠ 0)] 
    (x : ⨁ (i : ι), β i) 
    (s : Finset ι) (hs : DFinsupp.support x ⊆ s) :
  s.sum (fun i => (DirectSum.of β i) (x i)) = x := by
  conv_rhs => rw [← DirectSum.sum_support_of β x]
  apply symm
  apply Finset.sum_subset hs
  . intro i _ hi'
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
    rw [hi', map_zero]
  
theorem DirectSum.finsupp_sum_support_decompose' 
    {ι : Type u_3} {M : Type u_1} {σ : Type u_2} [inst : DecidableEq ι] [inst : AddCommMonoid M] [inst : SetLike σ M] 
    [inst : AddSubmonoidClass σ M] 
    (ℳ : ι → σ) [inst : DirectSum.Decomposition ℳ] 
    [inst : (i : ι) → (x : { x // x ∈ ℳ i }) → Decidable (x ≠ 0)] 
    (r : M) :
    r = ((DirectSum.decompose ℳ) r).sum (fun i x => ↑x) := by
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ r]

theorem EqvGenIsHomogeneous_of [h𝒜 : GradedAlgebra 𝒜] (hr :RelIsHomogeneous 𝒜 r) : 
  RelIsHomogeneous 𝒜 (EqvGen r) := by
  intro a b h
  induction h with
  | rel a b h =>
    intro i
    apply EqvGen.rel
    exact hr h i
  | refl a =>
    intro i
    apply EqvGen.refl
  | symm a b _ k => 
    intro i
    apply EqvGen.symm
    exact k i
  | trans a b c _ _ k k' => 
    intro i
    apply EqvGen.trans _ _ _ (k i) (k' i)


lemma rel_of_sum_of_rel_add {A : Type _} [AddCommMonoid A] 
    (r : A → A → Prop) (hr_zero : r 0 0)
    (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d)) 
    {ι : Type _} [DecidableEq ι] (f g : ι → A) (s : Finset ι) 
    (H : ∀ i ∈ s, r (f i) (g i)) :
  r (s.sum f) (s.sum g) := by 
  revert H
  induction s using Finset.induction_on with
  | empty => 
    intro _
    simp only [Finset.sum_empty]
    exact hr_zero
  | @insert i s hi hs => 
    intro H
    simp only [Finset.sum_insert hi]
    apply hr_add
    . apply H
      apply Finset.mem_insert_self
    . apply hs
      intro i hi
      apply H
      apply Finset.mem_insert_of_mem hi

lemma rel_of_finsupp_sum_of_rel_add {A : Type _} [AddCommMonoid A] 
    (r : A → A → Prop) (hr_zero : r 0 0)
    (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d)) 
    {ι : Type _} [DecidableEq ι] (f g : ι →₀ A) 
    (H : ∀ i, r (f i) (g i)) : 
  r (f.sum fun _ x => x) (g.sum fun _ x => x) := by
  rw [Finsupp.sum_of_support_subset f (Finset.subset_union_left _ g.support)]
  rw [Finsupp.sum_of_support_subset g (Finset.subset_union_right f.support _)]
  apply rel_of_sum_of_rel_add r hr_zero hr_add
  . intro i _ ; exact H i
  all_goals { intro _ _ ; rfl }

lemma rel_of_dsum_of_rel_add {A : Type _} [AddCommMonoid A] 
    (r : A → A → Prop) (hr_zero : r 0 0)
    (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d)) 
    {ι : Type _} [DecidableEq ι] {β : ι → Type _} 
    [∀ i, AddCommMonoid (β i)] (f g : (i : ι) → β i) 
    (h : (i : ι) → (β i →+ A))
    (s : Finset ι) 
    (H : ∀ i ∈ s, r (h i (f i)) (h i (g i))) :
  r (s.sum (fun i => h i (f i))) (s.sum (fun i => h i (g i))) := by 
  revert H
  induction s using Finset.induction_on with
  | empty => 
    intro _
    simp only [Finset.sum_empty]
    exact hr_zero
  | @insert i s hi hs => 
    intro H
    simp only [Finset.sum_insert hi]
    apply hr_add
    . apply H
      apply Finset.mem_insert_self
    . apply hs
      intro i hi
      apply H
      apply Finset.mem_insert_of_mem hi

lemma rel_of_dfinsupp_sum_of_rel_add {A : Type _} [AddCommMonoid A] 
    (r : A → A → Prop) (hr_zero : r 0 0)
    (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d)) 
    {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    [∀ i, AddCommMonoid (β i)] 
    [∀ i (y : β i), Decidable (y ≠ 0)]
    (h : (i : ι) → (β i →+ A)) (h' : (i : ι) → (β i →+ A))
    (f g : DFinsupp β)
    (H : ∀ i, r (h i (f i)) (h' i (g i))) : 
  r (f.sum fun i y => h i y) (g.sum fun i y => h' i y) := by
  rw [DFinsupp.sum_of_support_le _ _ _ _  (Finset.subset_union_left f.support g.support)] 
  rw [DFinsupp.sum_of_support_le _ _ _ _  (Finset.subset_union_right f.support g.support)] 
  apply rel_of_sum_of_rel_add r hr_zero hr_add
  . intro i _ ; exact H i

def Φ (n i j : ι) : 𝒜 i →+ 𝒜 j →+ A := {
  toFun := fun x => {
    toFun := fun y => if i + j = n then x * y else (0 : A)
    map_add' := fun a a' => by
      split_ifs <;>
      simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, mul_add, add_zero]
    map_zero' := by simp only [ZeroMemClass.coe_zero, mul_zero, ite_self] }
  map_add' := fun b b' => by 
    ext a
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.add_apply]
    split_ifs <;> simp only [add_mul, add_zero]
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, zero_mul, ite_self]
    rfl }
    
def Φy (n : ι) (y : DirectSum ι (fun i => 𝒜 i)) (i : ι) : (𝒜 i) →+ A := { 
    toFun := fun a => y.sum (fun j b => Φ 𝒜 n i j a b)
    map_add' := fun a a' => by
      simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, DFinsupp.sum_add]
    map_zero' := by
      simp only [map_zero, AddMonoidHom.zero_apply, DFinsupp.sum_zero] }

/-- The equivalence ring relation generated by a homogeneous relation
  is homogeneous -/
theorem RingConGen.RelIsHomogeneous_of 
    [h𝒜 : GradedAlgebra 𝒜] (hr :RelIsHomogeneous 𝒜 r) : 
  RelIsHomogeneous 𝒜 (RingConGen.Rel r) := by
  intro a b h
  induction h with 
  | of x y h =>
    intro i
    exact RingConGen.Rel.of _ _ (hr h i)
  | refl x => 
    intro i
    apply RingConGen.Rel.refl
  | symm _ h' => 
    intro i
    exact RingConGen.Rel.symm (h' i)
  | trans _ _ k k' =>
    intro i
    exact RingConGen.Rel.trans (k i) (k' i)
  | add _ _  k k' =>
    intro i
    simp only [map_add]
    apply RingConGen.Rel.add (k i) (k' i)
  | @mul a b c d _ _ k k' => 
    intro n
    simp only [AlgEquiv.toLinearMap_apply, map_mul]
    simp only [DirectSum.coe_mul_apply_eq_dfinsupp_sum]
    apply rel_of_dfinsupp_sum_of_rel_add (RingConGen.Rel r)
      (RingConGen.Rel.refl 0) (RingConGen.Rel.add) 
      (Φy 𝒜 n (DirectSum.decomposeAlgEquiv 𝒜 c))
      (Φy 𝒜 n (DirectSum.decomposeAlgEquiv 𝒜 d))
      (DirectSum.decomposeAlgEquiv 𝒜 a) 
      (DirectSum.decomposeAlgEquiv 𝒜 b) 
    intro i
    apply rel_of_dfinsupp_sum_of_rel_add (RingConGen.Rel r)
      (RingConGen.Rel.refl 0) (RingConGen.Rel.add) 
      _ _ -- (Φ _) (Φ _)
      (DirectSum.decomposeAlgEquiv 𝒜 c) 
      (DirectSum.decomposeAlgEquiv 𝒜 d) 
    intro j
    dsimp only [Φ]
    by_cases hn : i + j = n
    . simp only [if_pos hn]
      apply RingConGen.Rel.mul
      exact k i
      exact k' j
    . simp only [if_neg hn]
      apply RingConGen.Rel.refl

/-- The ideal generated by a homogeneous relation is homogeneous -/
theorem _root_.IsHomogeneous_of_rel_isHomogeneous [h𝒜 : GradedAlgebra 𝒜] 
    (hr : RelIsHomogeneous 𝒜 r) : 
  Ideal.IsHomogeneous 𝒜 (Ideal.ofRel r):= by
  let r' : A → A → Prop := fun a b =>
    ∃ i, a ∈ 𝒜 i ∧ b ∈ 𝒜 i ∧ r a b
  suffices : Ideal.ofRel r = Ideal.ofRel r'
  . rw [this]
    apply IsHomogeneous_of_rel_isPureHomogeneous
    intro a b h'
    obtain ⟨i, h⟩ := h'
    exact ⟨i, h.1, h.2.1⟩
  apply le_antisymm
  . intro x hx
    refine' Submodule.span_induction hx _ _ _ _
    . rintro x ⟨a, b, h', h⟩
      rw [← h𝒜.left_inv x, ← DirectSum.sum_support_of _ (DirectSum.Decomposition.decompose' x), map_sum]
      apply Ideal.sum_mem
      intro i _
      rw [DirectSum.coeAddMonoidHom_of]
      apply Ideal.subset_span
      use h𝒜.decompose' a i
      use h𝒜.decompose' b i
      simp only [exists_prop]
      constructor
      . use i
        simp only [DirectSum.Decomposition.decompose'_eq, SetLike.coe_mem, true_and]
        simp only [RelIsHomogeneous] at hr
        exact hr h' i
      . simp only [← h, DirectSum.Decomposition.decompose'_eq, DirectSum.decompose_add, 
          DirectSum.add_apply, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
    . simp only [Submodule.zero_mem]
    . intro x y hx hy
      exact Ideal.add_mem _ hx hy
    . intro a x hx
      simp only [smul_eq_mul]
      apply Ideal.mul_mem_left _ _ hx
  . intro x hx'
    refine' Submodule.span_induction hx' _ _ _ _
    . rintro x ⟨a, b, h', h⟩
      obtain ⟨i, _, _, h'⟩ := h'
      apply Ideal.subset_span
      exact ⟨a, b, h', h⟩
    . simp only [Submodule.zero_mem]
    . intro x y hx hy
      exact Ideal.add_mem _ hx hy
    . intro a x hx
      simp only [smul_eq_mul]
      apply Ideal.mul_mem_left _ a hx


end HomogeneousRelation

section Rel

variable (rel : A → A → Prop)

/-- The graded pieces of `RingQuot rel` -/
def quotSubmodule (i : ι): Submodule R (RingQuot rel) := 
  Submodule.map (RingQuot.mkAlgHom R rel) (𝒜 i)

/-- The canonical LinearMap from the graded pieces of A to that of RingQuot rel -/
def quotCompMap (i : ι) : (𝒜 i) →ₗ[R] (quotSubmodule R 𝒜 rel i) where
  toFun u := ⟨RingQuot.mkAlgHom R rel ↑u, by
      rw [quotSubmodule, Submodule.mem_map]
      exact ⟨↑u, u.prop, rfl⟩⟩
  map_add' u v := by
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add, 
      Ideal.Quotient.mkₐ_eq_mk, AddSubmonoid.mk_add_mk]
  map_smul' r u := by
    simp only [SetLike.val_smul, map_smul, Ideal.Quotient.mkₐ_eq_mk, RingHom.id_apply]
    rfl

def quotDecompose' :
  DirectSum ι (fun i => quotSubmodule R 𝒜 rel i) →ₗ[R] RingQuot rel :=
  DirectSum.toModule R ι _
  (fun i => Submodule.subtype (quotSubmodule R 𝒜 rel i))
def foo_mul [h𝒜 : GradedAlgebra 𝒜] {a b : RingQuot rel} {i j : ι} 
    (ha : a ∈ quotSubmodule R 𝒜 rel i) (hb : b ∈ quotSubmodule R 𝒜 rel j) : 
  a * b ∈ quotSubmodule R 𝒜 rel (i + j) := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  rw [← map_mul]
  exact ⟨a * b, h𝒜.mul_mem ha hb, rfl⟩

instance SetLike.GradedMonoid_RingQuot [h𝒜 : SetLike.GradedMonoid 𝒜] :
  SetLike.GradedMonoid (fun i => (𝒜 i).map (RingQuot.mkAlgHom R rel)) where
    one_mem := by
      exact ⟨1, h𝒜.one_mem, by simp only [map_one]⟩
    mul_mem := fun i j x y => by 
      rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      use a * b
      constructor
      simp only [SetLike.mem_coe, h𝒜.mul_mem ha hb]
      simp only [map_mul]

theorem quotDecompose_left_inv'_aux : 
   (DirectSum.coeLinearMap fun i => Submodule.map (RingQuot.mkAlgHom R rel) (𝒜 i)).comp
      (DirectSum.lmap' (quotCompMap R 𝒜 rel)) =
    (RingQuot.mkAlgHom R rel).toLinearMap.comp (DirectSum.coeLinearMap 𝒜) := by
  apply DirectSum.linearMap_ext
  intro i
  ext ⟨x, hx⟩
  dsimp only [quotCompMap, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  simp only [DirectSum.lmap'_lof]
  simp only [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  rfl


theorem quotDecompose_left_inv'_aux_apply (x) : 
  (DirectSum.coeLinearMap fun i => Submodule.map (RingQuot.mkAlgHom R rel) (𝒜 i))
    (DirectSum.lmap' (quotCompMap R 𝒜 rel) x) =
  (RingQuot.mkAlgHom R rel) (DirectSum.coeLinearMap 𝒜 x) := by
  let e := quotDecompose_left_inv'_aux R 𝒜 rel
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at e 
  apply e

lemma quotDecompose'_apply (a : DirectSum ι (fun i => 𝒜 i)) : 
  (quotDecompose' R 𝒜 rel) (DirectSum.lmap' (quotCompMap R 𝒜 rel) a) =
  RingQuot.mkAlgHom R rel (DirectSum.coeLinearMap 𝒜 a) := by
  suffices : (quotDecompose' R 𝒜 rel).comp (DirectSum.lmap' (quotCompMap R 𝒜 rel)) = (RingQuot.mkAlgHom R rel).toLinearMap.comp (DirectSum.coeLinearMap 𝒜)
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  apply this
  apply DirectSum.linearMap_ext
  intro i
  ext ⟨x, hx⟩
  simp only [quotDecompose', LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  simp only [DirectSum.lmap'_lof, DirectSum.toModule_lof]
  simp only [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  simp only [quotCompMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Submodule.coeSubtype]

lemma lmap'_quotCompMap_apply [h𝒜 : GradedAlgebra 𝒜] : ∀ a,  
  RingQuot.mkAlgHom R rel ↑(((DirectSum.decompose fun i => 𝒜 i) 
    ((DirectSum.coeLinearMap fun i => 𝒜 i) a)) i) = 
  ((DirectSum.lmap' (quotCompMap R 𝒜 rel)) a) i := by 
  intro a
  simp only [DirectSum.lmap'_apply]
  congr
  exact h𝒜.right_inv a

theorem quotDecompose'_surjective [h𝒜 : GradedAlgebra 𝒜] : 
  Function.Surjective (quotDecompose' R 𝒜 rel) := by
  intro x
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective R rel x
  let e : (DirectSum.coeLinearMap 𝒜) ((DirectSum.decomposeAlgEquiv 𝒜).toLinearMap a) = a := h𝒜.left_inv a
  use (DirectSum.lmap' (quotCompMap R 𝒜 rel)) ((DirectSum.decomposeAlgEquiv 𝒜).toLinearMap a)
  conv_rhs => rw [← e]
  apply quotDecompose_left_inv'_aux_apply

lemma obvious_iff {x y : A} :
  RingQuot.mkRingHom rel x = RingQuot.mkRingHom rel y ↔ 
    RingConGen.Rel rel x y := by
  constructor
  . intro h
    suffices : ∀ x, Quot.mk (RingQuot.Rel rel) x = ((RingQuot.mkRingHom rel) x).toQuot 
    rw [← RingQuot.eqvGen_rel_eq]
    rw [← Quot.eq, this x, this y, h]
    intro x
    simp only [RingQuot.mkRingHom]
    rfl
  . intro h
    induction h with
    | of x y h => exact RingQuot.mkRingHom_rel h
    | refl x => exact rfl
    | symm _ k => exact k.symm
    | trans h h' k k' => rw [k, k']
    | add _ _ k k' => simp only [map_add, k, k']
    | mul _ _ k k' => simp only [map_mul, k, k']


theorem quotDecompose_injective [h𝒜 : GradedAlgebra 𝒜] (hrel : RelIsHomogeneous 𝒜 rel) {x y : A}
  (hxy : RingQuot.mkAlgHom R rel x = RingQuot.mkAlgHom R rel y)
  (i : ι) :
  RingQuot.mkAlgHom R rel (h𝒜.decompose' x i) = 
    RingQuot.mkAlgHom R rel (h𝒜.decompose' y i) := by 
  rw [← AlgHom.coe_toRingHom, RingQuot.mkAlgHom_coe R rel, obvious_iff] at hxy ⊢
  exact RingConGen.RelIsHomogeneous_of 𝒜 _ hrel hxy i

theorem quotDecompose_surjective2 : 
  Function.Surjective (DirectSum.lmap' (quotCompMap R 𝒜 rel)) := by
  apply DirectSum.lmap'_surjective (quotCompMap R 𝒜 rel)
  intro i 
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, rfl⟩ := hx 
  use ⟨a, ha⟩
  rfl

theorem quotDecompose'_injective [h𝒜 : GradedAlgebra 𝒜] 
    (hrel : RelIsHomogeneous 𝒜 rel) : 
  Function.Injective (quotDecompose' R 𝒜 rel) := by
  
  intro x y hxy
  obtain ⟨a, ha, rfl⟩ := quotDecompose_surjective2 R 𝒜 rel x
  obtain ⟨b, hb, rfl⟩ := quotDecompose_surjective2 R 𝒜 rel y
  simp only [quotDecompose'_apply] at hxy
  let hxy' := quotDecompose_injective R 𝒜 rel hrel hxy
  apply DFinsupp.ext
  intro i
  specialize hxy' i
  simp only [DirectSum.Decomposition.decompose'_eq] at hxy' 
  suffices : ∀ a,  RingQuot.mkAlgHom R rel ↑(((DirectSum.decompose fun i => 𝒜 i) ((DirectSum.coeLinearMap fun i => 𝒜 i) a)) i)
     = ((DirectSum.lmap' (quotCompMap R 𝒜 rel)) a) i
  simpa only [this, SetLike.coe_eq_coe] using hxy' 

  intro a
  simp only [DirectSum.lmap'_apply]
  congr
  exact h𝒜.right_inv a


theorem quotDecompose_injective' [h𝒜 : GradedAlgebra 𝒜] (hrel : RelIsHomogeneous 𝒜 rel) : 
  Function.Injective (DirectSum.coeLinearMap 
    (fun i => (𝒜 i).map (RingQuot.mkAlgHom R rel))) := by   
  have hφ : ∀ i, Function.Surjective (quotCompMap R 𝒜 rel i)
  . intro i ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ := hx 
    use ⟨a, ha⟩ ; rfl
  intro x y hxy
  obtain ⟨a, ha, rfl⟩ := DirectSum.lmap'_surjective (quotCompMap R 𝒜 rel) hφ x
  obtain ⟨b, hb, rfl⟩ := DirectSum.lmap'_surjective (quotCompMap R 𝒜 rel) hφ y
  simp only [quotDecompose_left_inv'_aux_apply] at hxy
  let hxy' := quotDecompose_injective R 𝒜 rel hrel hxy
  apply DFinsupp.ext
  intro i
  specialize hxy' i
  simp only [DirectSum.Decomposition.decompose'_eq] at hxy' 
  simpa only [lmap'_quotCompMap_apply, SetLike.coe_eq_coe] using hxy' 

lemma quotDecompose'_bijective [h𝒜 : GradedAlgebra 𝒜] 
    (hrel : RelIsHomogeneous 𝒜 rel):
  Function.Bijective (quotDecompose' R 𝒜 rel) := by
  constructor
  . exact quotDecompose_injective' R 𝒜 rel hrel
  . exact quotDecompose'_surjective R 𝒜 rel

/-- The decomposition of the quotient ring is an internal direct sum -/
lemma quotDecomposition_IsInternal [h𝒜 : GradedAlgebra 𝒜] 
    (hrel : RelIsHomogeneous 𝒜 rel) : 
  DirectSum.IsInternal (quotSubmodule R 𝒜 rel) := by
  simp only [DirectSum.IsInternal]
  exact quotDecompose'_bijective R 𝒜 rel hrel

-- We need a full decomposition with an explicit left inverse
-- (may be obtained by choice, if necessary)
def DirectSum.Decomposition_RingQuot [h𝒜 : GradedAlgebra 𝒜] 
    (hrel : RelIsHomogeneous 𝒜 rel) :
  GradedAlgebra (fun i => (𝒜 i).map (RingQuot.mkAlgHom R rel)) := {
  SetLike.GradedMonoid_RingQuot R 𝒜 rel with 
  decompose' := sorry
  left_inv := sorry
  right_inv := sorry }

/-- The canonical LinearMap from A to ⊕ (quotSubmodule R 𝒜 rel i) -/
def quotDecomposeLaux [GradedAlgebra 𝒜] :
    A →ₗ[R] DirectSum ι fun i : ι => (quotSubmodule R 𝒜 rel i) :=
  LinearMap.comp 
    (DirectSum.lmap' (quotCompMap R 𝒜 rel)) 
    (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap

/- -- WHAT TO DO WITH THIS ?
theorem quotDecomposeLaux_of_mem_eq_zero [GradedAlgebra 𝒜] 
    (hrel : RelIsHomogeneous 𝒜 rel) (x : A)
    (hx : x ∈ I) (i : ι) : ((quotDecomposeLaux R 𝒜 rel) x) i = 0 :=
  by
  rw [quotDecomposeLaux, LinearMap.comp_apply, DirectSum.lmap'_apply, quotCompMap]
  simp only [Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toLinearMap_apply, 
    DirectSum.decomposeAlgEquiv_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mk_eq_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI i hx
#align quot_decompose_laux_of_mem_eq_zero quotDecomposeLaux_of_mem_eq_zero
 -/
 

/-- The decomposition at the higher level -/
def quotDecompose [GradedAlgebra 𝒜] (hrel : RelIsHomogeneous 𝒜 rel) :
    RingQuot rel →ₗ[R] DirectSum ι fun i : ι => (quotSubmodule R 𝒜 rel i) := by
  apply @Submodule.liftQ R A _ _ _ (I.restrictScalars R) R 
    (DirectSum ι fun i => I.quotSubmodule R 𝒜 i)
    _ _ _ (RingHom.id R) (quotDecomposeLaux R 𝒜 rel)
  -- without explicit arguments, it is too slow
  -- apply submodule.liftq (I.restrict_scalars R) (quot_decompose_laux R 𝒜 I),
  apply I.quotDecomposeLaux_ker R 𝒜 hI
#align quot_decompose Ideal.quotDecompose


theorem quotDecomposeLaux_apply_mk [GradedAlgebra 𝒜]
    (hrel : RelIsHomogeneous 𝒜 rel) (a : A) :
  quotDecompose R 𝒜 rel hrel (RingQuot rel) = 
    quotDecomposeLaux R 𝒜 a := by 
  sorry


/- THIS SECTION IS A MESS
ITS GOAL IS TO TRANSFER THE GRADED ALGEBRA STRUCTURE TO
THE CASE WHERE THE QUOTIENT IS DEFINED VIA A RELATION 

ALSO : 

-/


-- variable (𝒜 : ι → Submodule R A) 
-- variable [GradedAlgebra 𝒜]

variable (r : A → A → Prop)

variable {R}

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

section Ideal

variable (I : Ideal A) (rel : A → A → Prop)

-- variables [h𝒜 : graded_algebra 𝒜] (hI: ideal.is_homogeneous 𝒜 I)
-- It seems I start understanding what I'm doing
example : SemilinearMapClass (A →+* A ⧸ I) (RingHom.id ℤ) A (A ⧸ I) :=
  { coe := fun f a => f a
    coe_injective' := fun f g hfg => RingHom.ext fun x => Function.funext_iff.mp hfg x
    map_add := map_add
    map_smulₛₗ := fun f r a => by
      simp only [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, Int.cast_id] }

example : SemilinearMapClass (A →+* RingQuot rel) (RingHom.id ℤ) A (RingQuot rel) :=
  { coe := fun f a => f a
    coe_injective' := fun f g hfg => RingHom.ext fun x => Function.funext_iff.mp hfg x
    map_add := map_add
    map_smulₛₗ := fun f r a => by
      simp only [zsmul_eq_mul, map_mul, map_intCast, eq_intCast, Int.cast_id] }

-- This will probably be useless in the end, because I "R-modulify" everything
-- ideal.quotient.mk vs ideal.quotient.mkₐ
example (r : R) (a : A) : r • Ideal.Quotient.mk I a = Ideal.Quotient.mk I (r • a) :=
  map_smul (Ideal.Quotient.mkₐ R I) r a

#check RingQuot.mkAlgHom R rel

example (r : R) (a : A) : r • (RingQuot.mkAlgHom R rel a) = RingQuot.mkAlgHom R rel (r • a) := by 
  simp only [map_smul]

/-- The graded pieces of A ⧸ I -/
def Ideal.quotSubmodule : ι → Submodule R (A ⧸ I) := fun i => Submodule.map (Ideal.Quotient.mkₐ R I) (𝒜 i)
#align quot_submodule Ideal.quotSubmodule

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
def Ideal.quotCompMap (i : ι) : ↥(𝒜 i) →ₗ[R] ↥(quotSubmodule R 𝒜 I i)
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
#align quot_comp_map Ideal.quotCompMap


-- lemma quot_comp_map_surjective (i : ι) : function.surjective (quot_comp_map R 𝒜 I i) := sorry
example : Submodule R A := I.restrictScalars R

/-- The decomposition at the higher level -/
def Ideal.quotDecomposeLaux [GradedAlgebra 𝒜] :
    A →ₗ[R] DirectSum ι fun i : ι => (I.quotSubmodule R 𝒜 i) :=
  LinearMap.comp 
    (DirectSum.lmap' (I.quotCompMap R 𝒜)) 
    (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap
#align quot_decompose_laux Ideal.quotDecomposeLaux


theorem Ideal.quotDecomposeLaux_of_mem_eq_zero [GradedAlgebra 𝒜] 
    (hI : I.IsHomogeneous 𝒜) {x : A} (hx : x ∈ I) (i : ι) : 
  ((I.quotDecomposeLaux R 𝒜) x) i = 0 := by
  rw [Ideal.quotDecomposeLaux, LinearMap.comp_apply, DirectSum.lmap'_apply, quotCompMap]
  simp only [Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toLinearMap_apply, 
    DirectSum.decomposeAlgEquiv_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mk_eq_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI i hx
#align quot_decompose_laux_of_mem_eq_zero Ideal.quotDecomposeLaux_of_mem_eq_zero


theorem Ideal.quotDecomposeLaux_ker [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    I.restrictScalars R ≤ LinearMap.ker (I.quotDecomposeLaux R 𝒜) :=
  by
  intro x hx
  simp only [Submodule.restrictScalars_mem] at hx 
  rw [LinearMap.mem_ker]
  apply DFinsupp.ext
  intro i
  simp only [DirectSum.zero_apply]
  apply I.quotDecomposeLaux_of_mem_eq_zero R 𝒜 hI hx
#align quot_decompose_laux_ker Ideal.quotDecomposeLaux_ker

/-- The decomposition at the higher level -/
def Ideal.quotDecompose [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    A ⧸ I →ₗ[R] DirectSum ι fun i : ι => (I.quotSubmodule R 𝒜 i) := by
  apply @Submodule.liftQ R A _ _ _ (I.restrictScalars R) R 
    (DirectSum ι fun i => I.quotSubmodule R 𝒜 i)
    _ _ _ (RingHom.id R) (quotDecomposeLaux R 𝒜 I)
  -- without explicit arguments, it is too slow
  -- apply submodule.liftq (I.restrict_scalars R) (quot_decompose_laux R 𝒜 I),
  apply I.quotDecomposeLaux_ker R 𝒜 hI
#align quot_decompose Ideal.quotDecompose

-- set_option trace.profiler true
theorem Ideal.quotDecomposeLaux_apply_mk [GradedAlgebra 𝒜] 
    (hI : I.IsHomogeneous 𝒜) (a : A) :
  I.quotDecompose R 𝒜 hI (Ideal.Quotient.mk I a) = 
    I.quotDecomposeLaux R 𝒜 a := by
  simp only [Ideal.quotDecompose]
  have : Ideal.Quotient.mk I a = Submodule.Quotient.mk a := rfl
  rw [this]
  -- exact Submodule.liftQ_apply (I.restrictScalars R) (quotDecomposeLaux R 𝒜 I) a
  -- apply works
  apply Submodule.liftQ_apply
#align quot_decompose_laux_apply_mk Ideal.quotDecomposeLaux_apply_mk

private theorem Ideal.quotDecomposition_left_inv'_aux [GradedAlgebra 𝒜] :
  LinearMap.comp (DirectSum.coeLinearMap (Ideal.quotSubmodule R 𝒜 I)) 
    (DirectSum.lmap' (Ideal.quotCompMap R 𝒜 I)) =
  LinearMap.comp (Submodule.mkQ (Submodule.restrictScalars R I))
    (DirectSum.coeLinearMap 𝒜) := by 
  apply DirectSum.linearMap_ext
  intro i
  ext x
  dsimp
  change _ = (Submodule.mkQ (Submodule.restrictScalars R I)) (_)
  simp only [DirectSum.lmap'_lof]
  simp only [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  simp only [Submodule.mkQ_apply]
  rfl

theorem Ideal.quotDecomposition_left_inv' [h𝒜 : GradedAlgebra 𝒜] 
    (hI : I.IsHomogeneous 𝒜) :
  Function.LeftInverse 
    (DirectSum.coeLinearMap (I.quotSubmodule R 𝒜))
    (I.quotDecompose R 𝒜 hI) := by
  intro x
  obtain ⟨(a : A), rfl⟩ := Ideal.Quotient.mk_surjective x
  conv_lhs =>
    rw [quotDecomposeLaux_apply_mk, quotDecomposeLaux, LinearMap.comp_apply]
    simp only [AlgEquiv.toLinearMap_apply] 
    simp only [← LinearMap.comp_apply]
  rw [Ideal.quotDecomposition_left_inv'_aux]
  conv_rhs => 
    change Submodule.mkQ (I.restrictScalars R) a
    rw [← h𝒜.left_inv a]
    simp only [← LinearMap.comp_apply]

theorem Ideal.quotDecomposition_left_inv [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
  Function.LeftInverse 
    (DirectSum.coeAddMonoidHom (I.quotSubmodule R 𝒜))
    (I.quotDecompose R 𝒜 hI) := by
  rw [Function.leftInverse_iff_comp]
  change (DirectSum.coeLinearMap _) ∘ _ = _
  rw [← Function.leftInverse_iff_comp]
  exact I.quotDecomposition_left_inv' R 𝒜 hI
#align quot_decomposition_left_inv Ideal.quotDecomposition_left_inv

theorem Ideal.quotDecomposition_right_inv' [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
  Function.RightInverse 
    (DirectSum.coeLinearMap (I.quotSubmodule R 𝒜))
    (I.quotDecompose R 𝒜 hI) := by
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
  rw [Ideal.quotDecomposeLaux_apply_mk]
  rw [Ideal.quotDecomposeLaux]  
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

theorem Ideal.quotDecomposition_right_inv [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (I.quotSubmodule R 𝒜))
      (I.quotDecompose R 𝒜 hI) := by
  rw [Function.rightInverse_iff_comp]
  change _ ∘ (DirectSum.coeLinearMap _) = _
  rw [← Function.rightInverse_iff_comp]
  exact I.quotDecomposition_right_inv' R 𝒜 hI
#align quot_decomposition_right_inv Ideal.quotDecomposition_right_inv

def Ideal.quotDecomposition [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (I.quotSubmodule R 𝒜)
    where
  decompose' := I.quotDecompose R 𝒜 hI
  left_inv := I.quotDecomposition_left_inv R 𝒜 hI
  right_inv := I.quotDecomposition_right_inv R 𝒜 hI
#align quot_decomposition Ideal.quotDecomposition

theorem Ideal.mem_quotSubmodule_iff (i : ι) (g : A ⧸ I) :
    g ∈ I.quotSubmodule R 𝒜 i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = g := by
  rw [Ideal.quotSubmodule, Submodule.mem_map, Ideal.Quotient.mkₐ_eq_mk]
#align mem_quot_submodule_iff Ideal.mem_quotSubmodule_iff

/-- The quotient of a graded algebra by a homogeneous ideal, as a graded algebra -/
def Ideal.gradedQuotAlg [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) : GradedAlgebra (I.quotSubmodule R 𝒜)
    where
  toDecomposition := I.quotDecomposition R 𝒜 hI
  toGradedMonoid :=
    { one_mem := by
        rw [Ideal.quotSubmodule, Submodule.mem_map]
        exact ⟨1, SetLike.one_mem_graded 𝒜, rfl⟩
      mul_mem := fun i j gi gj hgi hgj =>
        by
        rw [Ideal.mem_quotSubmodule_iff] at hgi hgj ⊢
        obtain ⟨ai, hai, rfl⟩ := hgi
        obtain ⟨aj, haj, rfl⟩ := hgj
        use ai * aj
        constructor
        simp only [SetLike.mul_mem_graded hai haj]
        simp only [_root_.map_mul] }
#align graded_quot_alg Ideal.gradedQuotAlg

end Ideal


