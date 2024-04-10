import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Ideal.QuotientOperations


open DirectSum Function

section Classes
namespace LinearMapClass

variable {R β γ : Type*} [Semiring R] [AddCommMonoid β] [Module R β] [AddCommMonoid γ] [Module R γ]

--TODO: Note that there exists LinearMapClass.instCoeToLinearMap (CoeHead)
instance coeTCToLinearMap {F : Type*} [FunLike F β γ] [LinearMapClass F R β γ] :
    CoeTC F (β →ₗ[R] γ) := ⟨fun h => ⟨h, map_smul h⟩⟩

theorem coe_coe {F : Type*} [FunLike F β γ] [LinearMapClass F R β γ] (f : F) :
    ((f : β →ₗ[R] γ) : β → γ) = f :=
  rfl

theorem coe_coe' {F : Type*} [FunLike F β γ] [LinearMapClass F R β γ] (f : F) :
    ((f : β →ₗ[R] γ) : β →+ γ) = f :=
  rfl

end LinearMapClass


namespace AlgHomClass

variable {R β γ : Type*} [CommSemiring R] [Semiring β] [Algebra R β] [Semiring γ] [Algebra R γ]

theorem toLinearMap_coe_coe {F : Type*} [FunLike F β γ] [AlgHomClass F R β γ] (h : F) :
    ((h : β →ₗ[R] γ) : β → γ) = h :=
  rfl

end AlgHomClass


section DirectSum

namespace DirectSum

variable {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R]

/-- The components of a direct sum, as add_monoid_hom -/
def component' {β : ι → Type*} [∀ i, AddCommMonoid (β i)] (i : ι) : (⨁ i, β i) →+ β i :=
  component ℕ ι β i

theorem component'_eq {β : ι → Type*} [∀ i, AddCommMonoid (β i)] (x : DirectSum ι β) (i : ι) :
    component' i x = x i := rfl

theorem ext_iff' {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    (x y : ⨁ i, β i) : x = y ↔ ∀ i, component' i x = component' i y := ext_iff ℕ


/- Four versions of a direct sum of maps
   direct_sum.map' : for add_monoid_hom
   direct_sum.lmap'  : for linear_map
   the unprimed versions are defined in terms of classes
   In principle, the latter should suffice. -/

/-- `AddMonoidHom` from a direct sum to a direct sum given by families of
  `AddMonoidHomClass` maps. -/
def map {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    {F : ∀ _ : ι, Type*} [∀ i, FunLike (F i) (β i) (γ i)]
    [∀ i, AddMonoidHomClass (F i) (β i) (γ i)] (h : ∀ i, F i) :
    (⨁ i, β i) →+ ⨁ i, γ i :=
  toAddMonoid fun i => (of γ i).comp (h i)

/-- `AddMonoidHom` from a direct sum to a direct sum given by families of `AddMonoidHom`s. -/
def map' {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    (h : ∀ i, β i →+ γ i) : (⨁ i, β i) →+ (⨁ i, γ i) :=
  toAddMonoid fun i => (of γ i).comp (h i)


/-- `LinearMap` from a direct sum to a direct sum given by families of `LinearMapClass` maps. -/
def lmap {β γ : ι → Type*}
    [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)]
    {F : ∀ _ : ι, Type*} [∀ i, FunLike (F i) (β i) (γ i)] [∀ i, LinearMapClass (F i) R (β i) (γ i)]
    (h : ∀ i, F i) : (⨁ i, β i) →ₗ[R] (⨁ i, γ i) :=
  toModule R ι (⨁ i, γ i) fun i => (lof R ι γ i).comp (h i : β i →ₗ[R] γ i)

/-- `LinearMap` from a direct sum to a direct sum given by families of `LinearMap`s. -/
def lmap' {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] (h : ∀ i, β i →ₗ[R] γ i) :
    (⨁ i, β i) →ₗ[R] (⨁ i, γ i) :=
  toModule R ι _ fun i => (lof R ι γ i).comp (h i)

theorem map'_eq_lmap'_toAddMonoidHom {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)]
    [∀ i, AddCommMonoid (γ i)] (h : ∀ i, β i →+ γ i) :
    map' h = (lmap' fun i => (h i).toNatLinearMap).toAddMonoidHom :=
  rfl

theorem lmap'_toAddMonoidHom_eq_map' {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)]
    [∀ i, Module R (β i)] [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)]
    (h : ∀ i, β i →ₗ[R] γ i) :
    (lmap' h).toAddMonoidHom = map' fun i => (h i).toAddMonoidHom :=
  rfl

-- Lemmas to help computation
theorem map_of {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    {F : ι → Type*} [∀ i, FunLike (F i) (β i) (γ i)] [∀ i, AddMonoidHomClass (F i) (β i) (γ i)]
    (h : ∀ i, F i) (i : ι) (x : β i) : map h (of β i x) = of γ i (h i x) := by
  simp only [map, toAddMonoid_of, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe]
  rfl

theorem map_apply {β γ : ι → Type*} [Π i, AddCommMonoid (β i)] [Π i, AddCommMonoid (γ i)]
    {F : Π _i, Type*} [∀ i, FunLike (F i) (β i) (γ i)] [Π i, AddMonoidHomClass (F i) (β i) (γ i)]
    (h : Π i, F i) (x : DirectSum ι β) (i : ι) : map h x i = h i (x i) := by
  let f : DirectSum ι β →+ γ i :=
  { toFun := fun x => map h x i
    map_zero' := by simp only [map_zero, zero_apply]
    map_add' := by simp only [map_add, add_apply, forall_const] }
  let g : DirectSum ι β →+ γ i :=
  { toFun := fun y => h i (y i)
    map_zero' := by simp only [zero_apply, map_zero]
    map_add' := by simp only [add_apply, map_add, forall_const] }
  change f x = g x
  suffices f = g by
    rw [this]
  apply addHom_ext
  intros j y
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_of, f, g]
  by_cases hj : j = i
  · rw [← hj]; simp only [of_eq_same]
  · simp only [of_eq_of_ne _ j i _ hj, map_zero]

theorem map'_of {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    (h : ∀ i, β i →+ γ i) (i : ι) (x : β i) :
    map' h (of β i x) = of γ i (h i x) := by
  simp only [map', toAddMonoid_of, AddMonoidHom.coe_comp]; rfl

theorem lmap'_lof {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    [∀ i, Module R (β i)] [∀ i, Module R (γ i)] (h : ∀ i, β i →ₗ[R] γ i) (i : ι) (x : β i) :
  lmap' h (lof R ι β i x) = lof R ι γ i (h i x) := by
  simp only [lmap', toModule_lof, LinearMap.coe_comp]; rfl

theorem lmap'_surjective {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    [∀ i, AddCommMonoid (γ i)] [∀ i, Module R (γ i)] (f : ∀ i, β i →ₗ[R] γ i)
    (h : ∀ i, Surjective (f i)) : Surjective (lmap' f) := by
  intro c
  induction' c using DirectSum.induction_on with i xi x y hx hy
  . exact ⟨0, map_zero _⟩
  . use of _ i (h i xi).choose
    rw [← lof_eq_of R, lmap'_lof, lof_eq_of, (h i xi).choose_spec]
  . obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

theorem lmap'_apply {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    [∀ i, Module R (β i)] [∀ i, Module R (γ i)] (h : ∀ i, β i →ₗ[R] γ i) (x : ⨁ i, β i) (i : ι) :
    lmap' h x i = h i (x i) := by
  simp only [apply_eq_component R, ← LinearMap.comp_apply]
  apply LinearMap.congr_fun
  ext j y
  simp only [LinearMap.comp_apply, lmap'_lof]
  simp only [lof_eq_of, ← apply_eq_component]
  by_cases hji : j = i
  · rw [← hji]; simp only [of_eq_same]
  · simp only [of_eq_of_ne _ j i _ hji, map_zero]

theorem toModule_comp_lmap'_eq {β γ : ι → Type*} {δ : Type*} [∀ i, AddCommMonoid (β i)]
    [∀ i, AddCommMonoid (γ i)] [AddCommMonoid δ] [∀ i, Module R (β i)] [∀ i, Module R (γ i)]
    [Module R δ] (h : ∀ i, β i →ₗ[R] γ i) (f : ∀ i, γ i →ₗ[R] δ) (x : ⨁ i, β i) :
    toModule R ι δ f (lmap' h x) = toModule R ι δ (fun i => (f i).comp (h i)) x := by
  rw [← LinearMap.comp_apply]
  apply LinearMap.congr_fun
  ext i y
  simp only [LinearMap.coe_comp, comp_apply, lmap'_lof, toModule_lof]

theorem map'_apply {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    (h : ∀ i, β i →+ γ i) (x : ⨁ i, β i) (i : ι) : map' h x i = h i (x i) := by
  let f : (⨁ i, β i) →+ γ i :=
    { toFun     := fun x => map' h x i
      map_zero' := by simp only [map_zero, zero_apply]
      map_add'  := by simp only [map_add, add_apply, eq_self_iff_true, forall_const] }
  let g : (⨁ i, β i) →+ γ i :=
    { toFun     := fun y => h i (y i)
      map_zero' := by simp only [zero_apply, map_zero]
      map_add'  := by simp only [add_apply, map_add, eq_self_iff_true, forall_const] }
  change f x = g x
  apply DFunLike.congr_fun
  ext j y
  simp only [f, g, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, comp_apply,
    map'_of]
  by_cases hj : j = i
  · rw [← hj]; simp only [of_eq_same]
  · simp only [of_eq_of_ne _ j i _ hj, map_zero]

theorem mk_apply {β : ι → Type*} [∀ i, AddCommMonoid (β i)] (s : Finset ι)
    (f : (∀ i : (↑s : Set ι), β i.1)) (i : ι) :
    mk β s f i = if h : i ∈ s then f ⟨i, h⟩ else 0 :=
  rfl

theorem mk_eq_sum' {β : ι → Type*} [∀ i, AddCommMonoid (β i)] (s : Finset ι) (f : ∀ i, β i) :
    (mk β s (fun i => f i)) = s.sum (fun i => of β i (f i)) := by
  apply DFinsupp.ext
  intro i
  convert mk_apply s _ i
  rw [DFinsupp.finset_sum_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single_of_mem i hi (fun j _ hij => of_eq_of_ne _ _ _ _ hij),
      ← lof_eq_of ℕ, lof_apply]
  · exact Finset.sum_eq_zero (fun j hj => of_eq_of_ne _ _ _ _ (ne_of_mem_of_not_mem hj hi))

-- TODO: move to right file
theorem _root_.DFinsupp.mk_eq_sum {β : ι → Type*} [∀ i, AddCommMonoid (β i)] (s : Finset ι)
    (f : ∀ i, β i) : (DFinsupp.mk s fun i => f i) = s.sum fun i => of β i (f i) := by
  ext i
  simp only [DFinsupp.mk_apply, DFinsupp.finset_sum_apply]
  split_ifs with hi
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single_of_mem i hi
      (fun j _ hij =>  of_eq_of_ne _ _ _ _ hij), of_eq_same]
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_zero
      (fun j hj => of_eq_of_ne _ _ _ _ (ne_of_mem_of_not_mem hj hi))]

theorem mk_eq_sum {β : ι → Type*} [∀ i, AddCommMonoid (β i)] (s : Finset ι) (x : ∀ i : s, β i) :
  mk β s x = s.sum fun i => of β i (if h : i ∈ s then x ⟨i, h⟩ else 0) := by
  apply DFinsupp.ext
  intro i
  rw [mk_apply]
  split_ifs with hi
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single i (fun j _ hji => of_eq_of_ne _ _ _ _ hji),
      of_eq_same, dif_pos hi]
    · intro his
      rw [of_eq_same, dif_neg his]
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_zero
      (fun j hj => of_eq_of_ne _ _ _ _ (ne_of_mem_of_not_mem hj hi))]

theorem toAddMonoid_mk {β : ι → Type*} [∀ i, AddCommMonoid (β i)] {γ : Type*} [AddCommMonoid γ]
    (ψ : ∀ i, β i →+ γ) (s : Finset ι) (x : ∀ i : s, β i) :
    toAddMonoid ψ (mk β s x) =
      s.sum fun i => ψ i (if h : i ∈ s then x ⟨i, h⟩ else 0) := by
  rw [mk_eq_sum, map_sum, Finset.sum_congr rfl (fun i _ => toAddMonoid_of _ _ _)]

theorem map_apply' {β γ : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (γ i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]  {F : ∀ _, Type*} [∀ i, FunLike (F i) (β i) (γ i)]
    [∀ i, AddMonoidHomClass (F i) (β i) (γ i)] (h : ∀ i, F i) (x : ⨁ i, β i) :
    map h x = mk γ x.support (fun i => (h i) (x i)) := by
  conv_lhs => rw [← sum_support_of β x]
  simp_rw [map_sum, map_of]
  rw [eq_comm]
  convert mk_eq_sum x.support fun i => (h i) (x i)
  rwa [dif_pos]

end DirectSum

end DirectSum

section GradedQuot

section Semiring

variable (R : Type*) [CommSemiring R] {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
   {A : Type*} [CommSemiring A] [DecidableEq A] [Algebra R A] (𝒜 : ι → Submodule R A)

section HomogeneousRelation

variable {R}

variable (rel : A → A → Prop)

-- Maybe add that `r` is reflexive

lemma DirectSum.decomposeAlgEquiv_coe [GradedAlgebra 𝒜] (a : A) :
    decomposeAlgEquiv 𝒜 a = decompose 𝒜 a := by rfl

namespace Rel
/-- A relation `r` is `PureHomogeneous` iff `r a b` implies that `a` and `b`
are homogeneous of the same degree -/
def IsPureHomogeneous :=
  ∀ {a b : A} (_ : rel a b), ∃ i, a ∈ 𝒜 i ∧ b ∈ 𝒜 i

/-- A relation is `Homogeneous` iff `r a b` implies that
  the components of `a` and `b` are related by `r`. -/
def IsHomogeneous [GradedAlgebra 𝒜] : Prop :=
  ∀ {a b : A} (_ : rel a b), ∀ i,
    rel ((decomposeAlgEquiv 𝒜).toLinearMap a i) ((decomposeAlgEquiv 𝒜).toLinearMap b i)

variable {𝒜 rel}

lemma IsHomogeneous_of_isPureHomogeneous [GradedAlgebra 𝒜] (hrel : IsPureHomogeneous 𝒜 rel)
    (hrel0 : rel 0 0) : IsHomogeneous 𝒜 rel := by
  intro a b h i
  obtain ⟨j, ha, hb⟩ := hrel h
  by_cases hij : j = i
  . rw [← hij]
    simp only [AlgEquiv.toLinearMap_apply, decomposeAlgEquiv_coe, decompose_of_mem_same, ha, hb, h]
  . simp only [AlgEquiv.toLinearMap_apply, decomposeAlgEquiv_coe, decompose_of_mem_ne _ ha hij,
      decompose_of_mem_ne _ hb hij]
    -- needs that rel is reflexive
    exact hrel0

end Rel

/--  TODO: Fix comment and move.
  The ring relation generated by a homogeneous relation is homogeneous -/
lemma _root_.RingConGen.Rel.sum {α : Type*} [Ring α] (r : RingCon α) {ι : Type*} [DecidableEq ι]
    {a b : ι → α} (s : Finset ι) (hs : ∀ i ∈ s, r (a i) (b i)) :
    RingConGen.Rel r (s.sum a) (s.sum b) := by
  revert hs
  induction' s using Finset.induction_on with j t hj ht hjt
  . exact fun _ =>  RingConGen.Rel.refl _
  . intro hs
    simp only [Finset.sum_insert hj]
    apply RingConGen.Rel.add
    . exact RingConGen.Rel.of _ _ (hs j (Finset.mem_insert_self j t))
    . exact ht (fun i hi =>  hs i (Finset.mem_insert_of_mem hi))

/-- TODO: Move-/
theorem DFinsupp.sum_of_support_le {M : Type*} [AddCommMonoid M] {ι : Type*}
    [dec_ι : DecidableEq ι] {β : ι → Type*} [inst : (i : ι) → AddCommMonoid (β i)]
    [inst : (i : ι) → (x : β i) → Decidable (x ≠ 0)] {h : (i : ι) → (β i →+ M)}
    {x : DFinsupp β} {s : Finset ι} (hs : DFinsupp.support x ⊆ s) :
    x.sum (fun i y => h i y) = s.sum (fun i => h i (x i)) := by
  simp only [DFinsupp.sum]
  apply Finset.sum_subset hs
  . intro i _ hi'
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
    rw [hi', map_zero]

theorem DirectSum.sum_of_support_le {ι : Type*} [dec_ι : DecidableEq ι] (β : ι → Type*)
    [inst : (i : ι) → AddCommMonoid (β i)] [inst : (i : ι) → (x : β i) → Decidable (x ≠ 0)]
    {x : ⨁ (i : ι), β i} {s : Finset ι} (hs : DFinsupp.support x ⊆ s) :
    s.sum (fun i => (of β i) (x i)) = x := by
  conv_rhs => rw [← sum_support_of β x]
  rw [eq_comm]
  apply Finset.sum_subset hs
  . intro i _ hi'
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi'
    rw [hi', map_zero]

theorem DirectSum.finsupp_sum_support_decompose'
    {ι : Type u_3} {M : Type u_1} {σ : Type u_2} [inst : DecidableEq ι] [inst : AddCommMonoid M] [inst : SetLike σ M]
    [inst : AddSubmonoidClass σ M]
    (ℳ : ι → σ) [inst : Decomposition ℳ]
    [inst : (i : ι) → (x : { x // x ∈ ℳ i }) → Decidable (x ≠ 0)]
    (r : M) :
    r = ((decompose ℳ) r).sum (fun i x => ↑x) := by
  conv_lhs => rw [← sum_support_decompose ℳ r]

theorem EqvGenIsHomogeneous_of [GradedAlgebra 𝒜] (hr : Rel.IsHomogeneous 𝒜 rel) :
    Rel.IsHomogeneous 𝒜 (EqvGen rel) := by
  intro a b h
  induction h with
  | rel a b h => exact fun i => EqvGen.rel _ _ (hr h i)
  | refl a => exact fun i => EqvGen.refl _
  | symm a b _ k => exact fun i => EqvGen.symm _ _ (k i)
  | trans a b c _ _ k k' => exact fun i => EqvGen.trans _ _ _ (k i) (k' i)

lemma rel_of_sum_of_rel_add {A : Type*} [AddCommMonoid A] {r : A → A → Prop} (hr_zero : r 0 0)
    (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d)) {ι : Type*} [DecidableEq ι]
    {f g : ι → A} {s : Finset ι} (H : ∀ i ∈ s, r (f i) (g i)) : r (s.sum f) (s.sum g) := by
  revert H
  induction s using Finset.induction_on with
  | empty => exact fun _ =>  hr_zero
  | @insert i s hi hs =>
    intro H
    simp only [Finset.sum_insert hi]
    exact hr_add (H _ (Finset.mem_insert_self _ _))
      (hs (fun _ hi => H _ (Finset.mem_insert_of_mem hi)))

lemma rel_of_finsupp_sum_of_rel_add {A : Type*} [AddCommMonoid A] {r : A → A → Prop}
    (hr_zero : r 0 0) (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d))
    {ι : Type*} [DecidableEq ι] {f g : ι →₀ A} (H : ∀ i, r (f i) (g i)) :
    r (f.sum fun _ x => x) (g.sum fun _ x => x) := by
  rw [Finsupp.sum_of_support_subset f (Finset.subset_union_left _ g.support),
    Finsupp.sum_of_support_subset g (Finset.subset_union_right f.support _)]
  exact rel_of_sum_of_rel_add hr_zero hr_add (fun i _ =>  H i)
  all_goals { intro _ _ ; rfl }

lemma rel_of_dsum_of_rel_add {A : Type*} [AddCommMonoid A] {r : A → A → Prop} (hr_zero : r 0 0)
    (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d)) {ι : Type*} [DecidableEq ι]
    {β : ι → Type*} [∀ i, AddCommMonoid (β i)] {f g : (i : ι) → β i} (h : (i : ι) → (β i →+ A))
    {s : Finset ι} (H : ∀ i ∈ s, r (h i (f i)) (h i (g i))) :
  r (s.sum (fun i => h i (f i))) (s.sum (fun i => h i (g i))) := by
  revert H
  induction s using Finset.induction_on with
  | empty => exact fun _ => hr_zero
  | @insert i s hi hs =>
    intro H
    simp only [Finset.sum_insert hi]
    exact hr_add (H _ (Finset.mem_insert_self _ _))
      (hs (fun _ hi => H _ (Finset.mem_insert_of_mem hi)))

lemma rel_of_dfinsupp_sum_of_rel_add {A : Type*} [AddCommMonoid A] {r : A → A → Prop}
    (hr_zero : r 0 0) (hr_add : ∀ {a b c d} (_ : r a c) (_ : r b d), r (a + b) (c + d))
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    [∀ i (y : β i), Decidable (y ≠ 0)] (h : (i : ι) → (β i →+ A)) (h' : (i : ι) → (β i →+ A))
    {f g : DFinsupp β} (H : ∀ i, r (h i (f i)) (h' i (g i))) :
    r (f.sum fun i y => h i y) (g.sum fun i y => h' i y) := by
  rw [DFinsupp.sum_of_support_le (Finset.subset_union_left f.support g.support),
    DFinsupp.sum_of_support_le (Finset.subset_union_right f.support g.support)]
  exact rel_of_sum_of_rel_add hr_zero hr_add (fun i _ => H i)

def Φ (n i j : ι) : 𝒜 i →+ 𝒜 j →+ A := {
  toFun   := fun x => {
    toFun     := fun y => if i + j = n then x * y else (0 : A)
    map_add'  := fun a a' => by
      split_ifs <;>
      simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, mul_add, add_zero]
    map_zero' := by simp only [ZeroMemClass.coe_zero, mul_zero, ite_self] }
  map_add' := fun b b' => by
    ext a
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AddMonoidHom.add_apply]
    split_ifs <;> simp only [add_mul, add_zero]
  map_zero' := by simp only [ZeroMemClass.coe_zero, zero_mul, ite_self]; rfl }

def Φy (n : ι) (y : DirectSum ι (fun i => 𝒜 i)) (i : ι) : (𝒜 i) →+ A := {
    toFun    := fun a => y.sum (fun j b => Φ 𝒜 n i j a b)
    map_add' := fun a a' => by simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddMonoidHom.add_apply, DFinsupp.sum_add]
    map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply, DFinsupp.sum_zero] }

/-- The equivalence ring relation generated by a homogeneous relation is homogeneous -/
theorem RingConGen.RelIsHomogeneous_of [GradedAlgebra 𝒜] (hr : Rel.IsHomogeneous 𝒜 rel) :
    Rel.IsHomogeneous 𝒜 (RingConGen.Rel rel) := by
  intro a b h
  induction h with
  | of x y h => exact fun i =>  RingConGen.Rel.of _ _ (hr h i)
  | refl x => exact fun _ => RingConGen.Rel.refl _
  | symm _ h' => exact fun i => RingConGen.Rel.symm (h' i)
  | trans _ _ k k' => exact fun i => RingConGen.Rel.trans (k i) (k' i)
  | add _ _  k k' =>
    intro i
    simp only [map_add]
    exact RingConGen.Rel.add (k i) (k' i)
  | @mul a b c d _ _ k k' =>
    intro n
    simp only [AlgEquiv.toLinearMap_apply, map_mul, coe_mul_apply_eq_dfinsupp_sum]
    apply rel_of_dfinsupp_sum_of_rel_add (RingConGen.Rel.refl 0) (RingConGen.Rel.add)
      (Φy 𝒜 n (decomposeAlgEquiv 𝒜 c)) (Φy 𝒜 n (decomposeAlgEquiv 𝒜 d))
    intro i
    apply rel_of_dfinsupp_sum_of_rel_add (RingConGen.Rel.refl 0) (RingConGen.Rel.add)
    intro j
    dsimp only [Φ]
    by_cases hn : i + j = n
    . simp only [if_pos hn]
      exact RingConGen.Rel.mul (k i) (k' j)
    . simp only [if_neg hn]
      exact RingConGen.Rel.refl _

section Ring

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] {A : Type*}
  [CommRing A] [DecidableEq A] [Algebra R A] (𝒜 : ι → Submodule R A) (r : A → A → Prop)

/-- The ideal generated by a pure homogeneous relation is homogeneous -/
theorem _root_.Ideal.IsHomogeneous_of_rel_isPureHomogeneous [GradedAlgebra 𝒜]
    (hr : Rel.IsPureHomogeneous 𝒜 r) : Ideal.IsHomogeneous 𝒜 (Ideal.ofRel r):= by
  apply Ideal.homogeneous_span
  rintro x  ⟨a, b, ⟨h, heq⟩⟩
  obtain ⟨i, hi⟩ := hr h
  use i
  rw [(eq_sub_iff_add_eq).mpr heq]
  exact Submodule.sub_mem _ hi.1 hi.2

/-- The ideal generated by a homogeneous relation is homogeneous -/
theorem _root_.Ideal.IsHomogeneous_of_rel_isHomogeneous [h𝒜 : GradedAlgebra 𝒜]
    (hr : Rel.IsHomogeneous 𝒜 r) : Ideal.IsHomogeneous 𝒜 (Ideal.ofRel r):= by
  let r' : A → A → Prop := fun a b => ∃ i, a ∈ 𝒜 i ∧ b ∈ 𝒜 i ∧ r a b
  suffices Ideal.ofRel r = Ideal.ofRel r' by
    rw [this]
    apply Ideal.IsHomogeneous_of_rel_isPureHomogeneous
    rintro a b ⟨i, h⟩
    exact ⟨i, h.1, h.2.1⟩
  apply le_antisymm
  . intro x hx
    refine' Submodule.span_induction hx _ _ _ _
    . rintro x ⟨a, b, h', h⟩
      rw [← h𝒜.left_inv x, ← sum_support_of _ (Decomposition.decompose' x),
        map_sum]
      apply Ideal.sum_mem
      intro i _
      rw [coeAddMonoidHom_of]
      apply Ideal.subset_span
      use h𝒜.decompose' a i
      use h𝒜.decompose' b i
      simp only [exists_prop]
      constructor
      . use i
        simp only [Decomposition.decompose'_eq, SetLike.coe_mem, true_and]
        simp only [Rel.IsHomogeneous] at hr
        exact hr h' i
      . simp only [← h, Decomposition.decompose'_eq, decompose_add,
          add_apply, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid]
    . simp only [Submodule.zero_mem]
    . intro x y hx hy
      exact Ideal.add_mem _ hx hy
    . intro a x hx
      simp only [smul_eq_mul]
      apply Ideal.mul_mem_left _ _ hx
  . intro x hx'
    refine' Submodule.span_induction hx' _ (Submodule.zero_mem _)
      (fun _ _ hx hy => Ideal.add_mem _ hx hy) (fun a _ hx => Ideal.mul_mem_left _ a hx)
    . rintro x ⟨a, b, ⟨i, _, _, h'⟩, h⟩
      exact Ideal.subset_span  ⟨a, b, h', h⟩

end Ring

end HomogeneousRelation

section Rel

open DirectSum Function

variable (rel : A → A → Prop)

/-- The graded pieces of `RingQuot rel` -/
def quotSubmodule (i : ι) : Submodule R (RingQuot rel) :=
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
    simp only [SetLike.val_smul, map_smul, Ideal.Quotient.mkₐ_eq_mk, RingHom.id_apply]; rfl

def quotDecompose' : DirectSum ι (fun i => quotSubmodule R 𝒜 rel i) →ₗ[R] RingQuot rel :=
  toModule R ι _ (fun i => Submodule.subtype (quotSubmodule R 𝒜 rel i))

--NOTE : We don't use this, do we really need it?
lemma foo_mul [h𝒜 : GradedAlgebra 𝒜] {a b : RingQuot rel} {i j : ι}
    (ha : a ∈ quotSubmodule R 𝒜 rel i) (hb : b ∈ quotSubmodule R 𝒜 rel j) :
    a * b ∈ quotSubmodule R 𝒜 rel (i + j) := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  rw [← map_mul]
  exact ⟨a * b, h𝒜.mul_mem ha hb, rfl⟩

instance SetLike.GradedMonoid_RingQuot [h𝒜 : SetLike.GradedMonoid 𝒜] :
  SetLike.GradedMonoid (fun i => (𝒜 i).map (RingQuot.mkAlgHom R rel)) where
    one_mem :=  ⟨1, h𝒜.one_mem, by simp only [map_one]⟩
    mul_mem := fun i j x y => by
      rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a*b, ⟨h𝒜.mul_mem ha hb, map_mul _ _ _⟩⟩

theorem quotDecompose_left_inv'_aux :
    (coeLinearMap fun i => Submodule.map (RingQuot.mkAlgHom R rel) (𝒜 i)).comp
      (lmap' (quotCompMap R 𝒜 rel)) =
    (RingQuot.mkAlgHom R rel).toLinearMap.comp (coeLinearMap 𝒜) := by
  apply linearMap_ext
  intro i
  ext ⟨x, hx⟩
  simp only [quotCompMap, LinearMap.coe_comp, comp_apply, AlgHom.toLinearMap_apply, lmap'_lof]
  simp only [lof_eq_of, coeLinearMap_of]
  rfl

theorem quotDecompose_left_inv'_aux_apply (x) :
    (coeLinearMap fun i => Submodule.map (RingQuot.mkAlgHom R rel) (𝒜 i))
      (lmap' (quotCompMap R 𝒜 rel) x) =
    (RingQuot.mkAlgHom R rel) (coeLinearMap 𝒜 x) := by
  let e := quotDecompose_left_inv'_aux R 𝒜 rel
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at e
  apply e

lemma quotDecompose'_apply (a : DirectSum ι (fun i => 𝒜 i)) :
    (quotDecompose' R 𝒜 rel) (lmap' (quotCompMap R 𝒜 rel) a) =
      RingQuot.mkAlgHom R rel (coeLinearMap 𝒜 a) := by
  suffices (quotDecompose' R 𝒜 rel).comp (lmap' (quotCompMap R 𝒜 rel)) =
      (RingQuot.mkAlgHom R rel).toLinearMap.comp (coeLinearMap 𝒜) by
    simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    apply this
  apply linearMap_ext
  intro i
  ext ⟨x, hx⟩
  simp only [quotDecompose', LinearMap.coe_comp, comp_apply, AlgHom.toLinearMap_apply,
    lmap'_lof, toModule_lof]
  simp only [lof_eq_of, coeLinearMap_of, quotCompMap, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.coeSubtype]

lemma lmap'_quotCompMap_apply [h𝒜 : GradedAlgebra 𝒜] (i : ι) (a : DirectSum ι fun i ↦ ↥(𝒜 i)) :
    RingQuot.mkAlgHom R rel ↑(((decompose fun i => 𝒜 i) ((coeLinearMap fun i => 𝒜 i) a)) i) =
      ((lmap' (quotCompMap R 𝒜 rel)) a) i := by
  simp only [lmap'_apply]
  congr
  exact h𝒜.right_inv a

theorem quotDecompose'_surjective [h𝒜 : GradedAlgebra 𝒜] :
    Surjective (quotDecompose' R 𝒜 rel) := by
  intro x
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective R rel x
  let e : (coeLinearMap 𝒜) ((decomposeAlgEquiv 𝒜).toLinearMap a) = a :=
    h𝒜.left_inv a
  use (lmap' (quotCompMap R 𝒜 rel)) ((decomposeAlgEquiv 𝒜).toLinearMap a)
  conv_rhs => rw [← e]
  apply quotDecompose_left_inv'_aux_apply

lemma obvious_iff {x y : A} :
    RingQuot.mkRingHom rel x = RingQuot.mkRingHom rel y ↔ RingConGen.Rel rel x y := by
  constructor
  . intro h
    suffices ∀ x, Quot.mk (RingQuot.Rel rel) x = ((RingQuot.mkRingHom rel) x).toQuot by
      rw [← RingQuot.eqvGen_rel_eq, ← Quot.eq, this x, this y, h]
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

theorem quotDecompose_injective [h𝒜 : GradedAlgebra 𝒜] (hrel : Rel.IsHomogeneous 𝒜 rel) {x y : A}
    (hxy : RingQuot.mkAlgHom R rel x = RingQuot.mkAlgHom R rel y) (i : ι) :
    RingQuot.mkAlgHom R rel (h𝒜.decompose' x i) = RingQuot.mkAlgHom R rel (h𝒜.decompose' y i) := by
  rw [← AlgHom.coe_toRingHom, RingQuot.mkAlgHom_coe R rel, obvious_iff] at hxy ⊢
  exact RingConGen.RelIsHomogeneous_of 𝒜 _ hrel hxy i

theorem quotDecompose_surjective2 : Surjective (lmap' (quotCompMap R 𝒜 rel)) := by
  apply lmap'_surjective (quotCompMap R 𝒜 rel)
  rintro i ⟨x, ⟨a, ha, rfl⟩⟩
  exact ⟨⟨a, ha⟩, rfl⟩

theorem quotDecompose'_injective [h𝒜 : GradedAlgebra 𝒜] (hrel : Rel.IsHomogeneous 𝒜 rel) :
    Injective (quotDecompose' R 𝒜 rel) := by
  intro x y hxy
  obtain ⟨a, ha, rfl⟩ := quotDecompose_surjective2 R 𝒜 rel x
  obtain ⟨b, hb, rfl⟩ := quotDecompose_surjective2 R 𝒜 rel y
  simp only [quotDecompose'_apply] at hxy
  let hxy' := quotDecompose_injective R 𝒜 rel hrel hxy
  apply DFinsupp.ext
  intro i
  specialize hxy' i
  simp only [Decomposition.decompose'_eq] at hxy'
  suffices ∀ a, RingQuot.mkAlgHom R rel ↑(((decompose fun i => 𝒜 i)
      ((coeLinearMap fun i => 𝒜 i) a)) i) = ((lmap' (quotCompMap R 𝒜 rel)) a) i by
    simpa only [this, SetLike.coe_eq_coe] using hxy'
  intro a
  simp only [lmap'_apply]
  congr
  exact h𝒜.right_inv a


theorem quotDecompose_injective' [h𝒜 : GradedAlgebra 𝒜] (hrel : Rel.IsHomogeneous 𝒜 rel) :
    Injective (coeLinearMap (fun i => (𝒜 i).map (RingQuot.mkAlgHom R rel))) := by
  have hφ : ∀ i, Surjective (quotCompMap R 𝒜 rel i) := by
    rintro i ⟨x, ⟨a, ha, rfl⟩ ⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  intro x y hxy
  obtain ⟨a, ha, rfl⟩ := lmap'_surjective (quotCompMap R 𝒜 rel) hφ x
  obtain ⟨b, hb, rfl⟩ := lmap'_surjective (quotCompMap R 𝒜 rel) hφ y
  simp only [quotDecompose_left_inv'_aux_apply] at hxy
  let hxy' := quotDecompose_injective R 𝒜 rel hrel hxy
  apply DFinsupp.ext
  intro i
  specialize hxy' i
  simp only [Decomposition.decompose'_eq] at hxy'
  simpa only [lmap'_quotCompMap_apply, SetLike.coe_eq_coe] using hxy'

lemma quotDecompose'_bijective [GradedAlgebra 𝒜] (hrel : Rel.IsHomogeneous 𝒜 rel) :
    Bijective (quotDecompose' R 𝒜 rel) :=
  ⟨quotDecompose_injective' R 𝒜 rel hrel, quotDecompose'_surjective R 𝒜 rel⟩

/-- The decomposition of the quotient ring is an internal direct sum -/
lemma quotDecomposition_IsInternal [GradedAlgebra 𝒜] (hrel : Rel.IsHomogeneous 𝒜 rel) :
    IsInternal (quotSubmodule R 𝒜 rel) :=
  quotDecompose'_bijective R 𝒜 rel hrel

-- We need a full decomposition with an explicit left inverse
-- (here, it is obtained by `invFun`)
noncomputable def quotDecomposition [GradedAlgebra 𝒜] (hrel : Rel.IsHomogeneous 𝒜 rel) :
  Decomposition (quotSubmodule R 𝒜 rel) := {
  decompose' := invFun (quotDecompose' R 𝒜 rel)
  left_inv   := rightInverse_invFun (quotDecompose'_surjective R 𝒜 rel)
  right_inv  := leftInverse_invFun (quotDecompose_injective' R 𝒜 rel hrel) }

noncomputable def DirectSum.Decomposition_RingQuot [GradedAlgebra 𝒜]
    (hrel : Rel.IsHomogeneous 𝒜 rel) :
    GradedAlgebra (quotSubmodule R 𝒜 rel) := {
  toGradedMonoid  := SetLike.GradedMonoid_RingQuot R 𝒜 rel
  toDecomposition := quotDecomposition R 𝒜 rel hrel }

end Rel

end Semiring

section Ideal

variable (R : Type*) [CommRing R] {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] {A : Type*}
  [CommRing A] [DecidableEq A] [Algebra R A] (𝒜 : ι → Submodule R A) (I : Ideal A)
  (rel : A → A → Prop)

/-- The graded pieces of A ⧸ I -/
def Ideal.quotSubmodule : ι → Submodule R (A ⧸ I) :=
  fun i => Submodule.map (Ideal.Quotient.mkₐ R I) (𝒜 i)

def Ideal.quotCompMap (i : ι) : ↥(𝒜 i) →ₗ[R] ↥(quotSubmodule R 𝒜 I i) := {
  toFun := fun u ↦ ⟨Ideal.Quotient.mkₐ R I ↑u, by
      rw [quotSubmodule, Submodule.mem_map]; exact ⟨↑u, u.prop, rfl⟩⟩
  map_add' := fun u v ↦ by
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add,
      Ideal.Quotient.mkₐ_eq_mk, AddSubmonoid.mk_add_mk]
  map_smul' := fun r u ↦ by
    simp only [SetLike.val_smul, map_smul, Ideal.Quotient.mkₐ_eq_mk, RingHom.id_apply]; rfl }

/-- The decomposition at the higher level -/
def Ideal.quotDecomposeLaux [GradedAlgebra 𝒜] :
    A →ₗ[R] DirectSum ι fun i : ι => (I.quotSubmodule R 𝒜 i) :=
  LinearMap.comp (lmap' (I.quotCompMap R 𝒜)) (decomposeAlgEquiv 𝒜).toLinearMap


variable {I}

theorem Ideal.quotDecomposeLaux_of_mem_eq_zero [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) {x : A}
    (hx : x ∈ I) (i : ι) : ((I.quotDecomposeLaux R 𝒜) x) i = 0 := by
  rw [Ideal.quotDecomposeLaux, LinearMap.comp_apply, lmap'_apply, quotCompMap]
  simp only [Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.toLinearMap_apply, decomposeAlgEquiv_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.mk_eq_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI i hx


theorem Ideal.quotDecomposeLaux_ker [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    I.restrictScalars R ≤ LinearMap.ker (I.quotDecomposeLaux R 𝒜) :=
  fun _ hx =>  LinearMap.mem_ker.mpr (DFinsupp.ext (I.quotDecomposeLaux_of_mem_eq_zero R 𝒜 hI hx))

/-- The decomposition at the higher level -/
def Ideal.quotDecompose [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    A ⧸ I →ₗ[R] DirectSum ι fun i : ι => (I.quotSubmodule R 𝒜 i) := by
  apply @Submodule.liftQ R A _ _ _ (I.restrictScalars R) R
    (DirectSum ι fun i => I.quotSubmodule R 𝒜 i)
    _ _ _ (RingHom.id R) (quotDecomposeLaux R 𝒜 I)
  -- without explicit arguments, it is too slow
  -- apply submodule.liftq (I.restrict_scalars R) (quot_decompose_laux R 𝒜 I),
  apply I.quotDecomposeLaux_ker R 𝒜 hI

-- set_option trace.profiler true
theorem Ideal.quotDecomposeLaux_apply_mk [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) (a : A) :
    I.quotDecompose R 𝒜 hI (Ideal.Quotient.mk I a) = I.quotDecomposeLaux R 𝒜 a :=
  Submodule.liftQ_apply (I.restrictScalars R) (quotDecomposeLaux R 𝒜 I) a

private theorem Ideal.quotDecomposition_left_inv'_aux [GradedAlgebra 𝒜] :
  LinearMap.comp (coeLinearMap (Ideal.quotSubmodule R 𝒜 I)) (lmap' (Ideal.quotCompMap R 𝒜 I)) =
    LinearMap.comp (Submodule.mkQ (Submodule.restrictScalars R I)) (coeLinearMap 𝒜) := by
  apply linearMap_ext
  intro i
  ext x
  dsimp only [LinearMap.coe_comp, comp_apply]
  change _ = (Submodule.mkQ (Submodule.restrictScalars R I)) (_)
  rw [lmap'_lof]
  simp only [lof_eq_of, coeLinearMap_of, Submodule.mkQ_apply]
  rfl

theorem Ideal.quotDecomposition_left_inv' [h𝒜 : GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    LeftInverse (coeLinearMap (I.quotSubmodule R 𝒜)) (I.quotDecompose R 𝒜 hI) := by
  intro x
  obtain ⟨(a : A), rfl⟩ := Ideal.Quotient.mk_surjective x
  conv_lhs =>
    rw [quotDecomposeLaux_apply_mk, quotDecomposeLaux, LinearMap.comp_apply]
    simp only [AlgEquiv.toLinearMap_apply, ← LinearMap.comp_apply]
  rw [Ideal.quotDecomposition_left_inv'_aux]
  conv_rhs =>
    rw [← h𝒜.left_inv a]
    simp only [← LinearMap.comp_apply]

theorem Ideal.quotDecomposition_left_inv [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    LeftInverse (DirectSum.coeAddMonoidHom (I.quotSubmodule R 𝒜)) (I.quotDecompose R 𝒜 hI) :=
  I.quotDecomposition_left_inv' R 𝒜 hI

theorem Ideal.quotDecomposition_right_inv' [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    RightInverse (coeLinearMap (I.quotSubmodule R 𝒜)) (I.quotDecompose R 𝒜 hI) := by
  rw [rightInverse_iff_comp, ← LinearMap.coe_comp, ← @LinearMap.id_coe R]
  apply congr_arg
  apply linearMap_ext
  intro i
  ext y
  obtain ⟨x, hx, hxy⟩ := y.prop
  simp only [LinearMap.coe_comp, comp_apply, LinearMap.id_comp, lof_eq_of, coeLinearMap_of]
  rw [← hxy, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotDecomposeLaux_apply_mk, Ideal.quotDecomposeLaux]
  simp only [LinearMap.coe_comp, comp_apply]
  change lmap' _ (decompose 𝒜 x) = _
  suffices decompose 𝒜 x = lof R ι (fun i => 𝒜 i) i (⟨x, hx⟩ : 𝒜 i) by
    rw [this, lmap'_lof, lof_eq_of]
    apply congr_arg₂ _ rfl
    rw [quotCompMap]
    simp only [Ideal.Quotient.mkₐ_eq_mk, Submodule.coe_mk, LinearMap.coe_mk]
    rw [← Subtype.coe_inj, Subtype.coe_mk, ← hxy]
    simp only [Ideal.Quotient.mkₐ_eq_mk]
    rfl
  conv_lhs => rw [← Subtype.coe_mk x hx]
  rw [decompose_coe, lof_eq_of]

theorem Ideal.quotDecomposition_right_inv [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    RightInverse (DirectSum.coeAddMonoidHom (I.quotSubmodule R 𝒜)) (I.quotDecompose R 𝒜 hI) :=
  I.quotDecomposition_right_inv' R 𝒜 hI

def Ideal.quotDecomposition [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
    Decomposition (I.quotSubmodule R 𝒜) := {
  decompose' := I.quotDecompose R 𝒜 hI
  left_inv   := I.quotDecomposition_left_inv R 𝒜 hI
  right_inv  := I.quotDecomposition_right_inv R 𝒜 hI }

theorem Ideal.mem_quotSubmodule_iff (i : ι) (g : A ⧸ I) :
    g ∈ I.quotSubmodule R 𝒜 i ↔ ∃ a ∈ 𝒜 i, Ideal.Quotient.mk I a = g := by
  rw [Ideal.quotSubmodule, Submodule.mem_map, Ideal.Quotient.mkₐ_eq_mk]

/-- The quotient of a graded algebra by a homogeneous ideal, as a graded algebra -/
def Ideal.gradedQuotAlg [GradedAlgebra 𝒜] (hI : I.IsHomogeneous 𝒜) :
  GradedAlgebra (I.quotSubmodule R 𝒜) := {
  toDecomposition := I.quotDecomposition R 𝒜 hI
  toGradedMonoid :=
    { one_mem := by
        rw [Ideal.quotSubmodule, Submodule.mem_map]
        exact ⟨1, SetLike.one_mem_graded 𝒜, rfl⟩
      mul_mem := fun i j gi gj hgi hgj => by
        obtain ⟨ai, hai, rfl⟩ := hgi
        obtain ⟨aj, haj, rfl⟩ := hgj
        exact ⟨ai * aj, ⟨SetLike.mul_mem_graded hai haj, _root_.map_mul _ _ _⟩⟩ }}

end Ideal

end GradedQuot
