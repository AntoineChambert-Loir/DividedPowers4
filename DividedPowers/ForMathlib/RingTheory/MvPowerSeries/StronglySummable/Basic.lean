--import Mathlib.Data.Finsupp.Union
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Order.Basic

open Finset Filter Set

instance ENat.topology : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

namespace Function

open scoped Pointwise

variable {α : Type _} {ι : Type _}

/-- If a function `f` to an additive commutative monoid with the discrete topology tends to zero
  along the cofinite filter, then `f` has finite support. -/
theorem finite_support_of_tendsto_zero [AddCommMonoid α] [TopologicalSpace α] [DiscreteTopology α]
    {f : ι → α} (hf : Tendsto f cofinite (nhds 0)) : f.support.Finite := by
  rw [nhds_discrete, tendsto_pure] at hf
  obtain ⟨s, H, p⟩ := Eventually.exists_mem hf
  apply Finite.subset H
  intro x hx
  rw [mem_compl_iff]
  by_contra hxs
  exact hx (p x hxs)

/-- If a function `f` to a discrete topological commutative additive group is summable, then it has
  finite support. -/
theorem finite_support_of_summable [AddCommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    [IsTopologicalAddGroup α] {f : ι → α} (hf : Summable f) : f.support.Finite :=
  finite_support_of_tendsto_zero hf.tendsto_cofinite_zero

/-- If a function `f` to a topological commutative additive group is summable, then it tends to zero
  along the cofinite filter. -/
theorem tendsto_zero_of_summable [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α]
    {f : ι → α} (hf : Summable f) : Tendsto f cofinite (nhds 0) := by
  classical
  obtain ⟨a, ha⟩ := hf
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_atTop_nhds] at ha
  rw [tendsto_nhds]
  intro U₀ hU₀ memU₀
  suffices hU₁ : ∃ U₁ : Set α, IsOpen U₁ ∧ (0 : α) ∈ U₁ ∧ U₁ - U₁ ≤ U₀ by
    obtain ⟨U₁, hU₁, memU₁, addU₁_subset⟩ := hU₁
    obtain ⟨S, hS⟩ :=
      ha ((fun x => x - a) ⁻¹' U₁) (by simp only [memU₁, Set.mem_preimage, sub_self])
        (IsOpen.preimage (continuous_sub_right a) hU₁)
    apply S.finite_toSet.subset
    intro i hi
    by_contra his
    apply hi
    apply addU₁_subset
    use (insert i S).sum f - a,
      hS (insert i S) (subset_insert i S),
      S.sum f - a,
      hS S le_rfl
    simp only [sum_insert his, sub_sub_sub_cancel_right, add_sub_cancel_right]
  · suffices h_open : IsOpen ((fun xy : α × α => xy.fst - xy.snd) ⁻¹' U₀) by
      rw [isOpen_prod_iff] at h_open
      obtain ⟨u, v, hu, hv, mem_u, mem_v, H⟩ :=
        h_open 0 0 (by simp only [Set.mem_preimage, sub_self, memU₀])
      use u ∩ v, IsOpen.inter hu hv, ⟨mem_u, mem_v⟩
      apply subset_trans _ (Set.image_subset_iff.mpr H)
      rw [image_prod]
      rintro z ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, mem_of_mem_inter_left hx, y, mem_of_mem_inter_right hy, rfl⟩
    · exact IsOpen.preimage continuous_sub hU₀

end Function

namespace MvPowerSeries

open Function

variable {σ α : Type*} --[DecidableEq σ]

section StronglySummable

variable {ι : Type _}

section Semiring

variable [Semiring α]

/-- A family of power series is `strongly summable` if for every finitely supported function
  `(d : σ →₀ ℕ)`, the function `λ i, coeff d (f i)` is finitely supported. -/
def StronglySummable (f : ι → MvPowerSeries σ α) : Prop :=
  ∀ d : σ →₀ ℕ, (fun i => coeff d (f i)).support.Finite

namespace StronglySummable

theorem congr {f g : ι → MvPowerSeries σ α} (h : f = g) : StronglySummable f ↔ StronglySummable g :=
  by rw [h]

section Order

open Finsupp

-- Bourbaki, *Algèbre*, chap. 4, §4, page IV.25, exemple c)
/-- A family of power series is strongly summable if their weighted orders tend to infinity. -/
theorem of_weightedOrder_tendsto_top (w : σ → ℕ) (f : ι → MvPowerSeries σ α)
    (hf : Tendsto (fun i => weightedOrder w (f i)) cofinite (nhds ⊤)) : StronglySummable f := by
  intro d
  rw [HasBasis.tendsto_right_iff nhds_top_basis] at hf
  exact (hf (weight w d : ℕ∞) (WithTop.coe_lt_top _)).subset
    (fun _ h' h ↦ h' (coeff_eq_zero_of_lt_weightedOrder w h))


theorem of_order_tendsto_top (f : ι → MvPowerSeries σ α)
    (hf : Tendsto (fun i => order (f i)) cofinite (nhds ⊤)) : StronglySummable f :=
  of_weightedOrder_tendsto_top _ f hf


/-- When σ is finite, a family of power series is strongly summable
  iff their weighted orders tend to infinity. -/
theorem weightedOrder_tendsto_top_iff [Finite σ] {ι : Type _} {w : σ → ℕ} (hw : ∀ x, w x ≠ 0)
    (f : ι → MvPowerSeries σ α) :
    StronglySummable f ↔ Tendsto (fun i => weightedOrder w (f i)) cofinite (nhds ⊤) := by
  refine' ⟨fun hf => _, of_weightedOrder_tendsto_top w f⟩
  · rw [HasBasis.tendsto_right_iff nhds_top_basis]
    intro n hn
    induction n
    · exfalso; exact lt_irrefl ⊤ hn
    · rename_i n
      simp only [Set.mem_Ioi, eventually_cofinite, not_lt]
      let s := {d : σ →₀ ℕ | (weight w d) ≤ n}
      apply ((finite_of_nat_weight_le w hw n).biUnion fun d _ => hf d).subset
      intro i hi
      simp only [mem_setOf_eq] at hi
      simp only [mem_setOf_eq, mem_iUnion, mem_setOf_eq, exists_prop]
      have heq : (ENat.toNat (weightedOrder w (f i))) = weightedOrder w (f i) := by
        rw [ENat.coe_toNat_eq_self]
        exact ne_of_lt (lt_of_le_of_lt hi hn)
      obtain ⟨d, hd⟩ :=  MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder w heq
      refine ⟨d, ?_, hd.1⟩
      simpa [← hd.2, WithTop.some_eq_coe, Nat.cast_le] using hi

/-- When σ is finite, a family of power series is strongly summable
  iff their orders tend to infinity. -/
theorem order_tendsto_top_iff [Finite σ] (f : ι → MvPowerSeries σ α) :
    StronglySummable f ↔ Tendsto (fun i => order (f i)) cofinite (nhds ⊤) :=
  weightedOrder_tendsto_top_iff (by simp) f

end Order

instance : LocallyFiniteOrderBot (σ →₀ ℕ) := sorry

/-- The union of the supports of the functions `λ i, coeff e (f i)`, where `e` runs over
  the coefficients bounded by `d`. -/
noncomputable def unionOfSupportOfCoeffLe [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) : Finset ι :=
  Finset.biUnion (Finset.Iic d) fun e => (hf e).toFinset

/-- A term `i : ι` does not belong to the union of the supports of the functions
  `λ i, coeff e (f i)`, where `e` runs over the coefficients bounded by `d` if and only if
  `∀ e ≤ d, coeff e (f i) = 0`. -/
theorem not_mem_unionOfSupportOfCoeffLe_iff [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) (i : ι) :
    i ∉ hf.unionOfSupportOfCoeffLe d ↔ ∀ (e) (_ : e ≤ d), coeff e (f i) = 0 := by
  simp only [unionOfSupportOfCoeffLe, Finset.mem_biUnion, Finset.mem_Iic, Finite.mem_toFinset,
    mem_support, not_exists, ne_eq, not_and, not_not]

/- lemma union_of_coeff_support_finite {f : ι → mv_power_series σ α}
  (hf : strongly_summable f) (d : σ →₀ ℕ) :
  (⋃ e (H : e ≤ d), (λ i, coeff e (f i)).support).finite :=
(set.Iic d).to_finite.bUnion (λ d H, hf d) -/

-- TODO: ask
/-- If `f` is strongly summable, then the union of the supports of the functions
  `λ i, coeff e (f i)`, where `e` runs over the coefficients bounded by `d`, contains
  finitely many finite sets. -/
theorem of_subset_unionOfSupportOfCoeffLe_finite [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) :
    {I : Finset ι | I ⊆ hf.unionOfSupportOfCoeffLe d}.Finite := by
  suffices {I : Finset ι | I ⊆ hf.unionOfSupportOfCoeffLe  d} =
    (hf.unionOfSupportOfCoeffLe  d).powerset by
    rw [this]; apply finite_toSet
  ext I
  simp only [mem_setOf_eq, coe_powerset, Set.mem_preimage, mem_powerset_iff, Finset.coe_subset]

/-- If `f` and `g` are strongly summable, then for all `d : σ →₀ ℕ`, the support of the function
  `λ i, coeff d ((f + g) i)` is contained in the union of the supports of `λ i, coeff d (f i)`
  and `λ i, coeff d (g i)`-/
theorem support_add [DecidableEq ι] {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (hg : StronglySummable g) :
    ∀ d : σ →₀ ℕ, (fun i => coeff d ((f + g) i)).support ⊆
      ((hf d).toFinset ∪ (hg d).toFinset : Finset ι) := by
  intro d i
  simp only [Pi.add_apply, map_add, Function.mem_support, ne_eq, coe_union, Finite.coe_toFinset,
    Set.mem_union]
  intro h
  by_cases h₁ : coeff d (f i) = 0
  · right; simpa [h₁] using h
  · left; exact h₁

/-- If `f` and `g` are strongly summable, then so is `f + g`.  -/
theorem add {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable (f + g) := by
  classical exact fun d => Finite.subset (finite_toSet _) (support_add hf hg d)

/-- If `f` is strongly summable, then for every `a : ι → α`, `a • f` is strongly summable. -/
theorem smul {f : ι → MvPowerSeries σ α} (a : ι → α) (hf : StronglySummable f) :
    StronglySummable (a • f) := by
  intro d
  apply Finite.subset (hf d)
  intro i
  simp only [Pi.smul_apply', Function.mem_support, ne_eq]
  intro h h'
  apply h
  rw [coeff_smul, h', MulZeroClass.mul_zero]

/-- If `f` and `g` are strongly summable, then for all `d : σ →₀ ℕ`, the support of the function
  `λ i, coeff d (f i.fst * g i.snd)` is contained in the finite set
  `d.antidiagonal.biUnion fun b => (hf b.fst).toFinset).product
          (d.antidiagonal.biUnion fun b => (hg b.snd).toFinset)`. -/
theorem support_mul [DecidableEq ι] [DecidableEq σ] {f : ι → MvPowerSeries σ α} {κ : Type _}
    [DecidableEq κ] {g : κ → MvPowerSeries σ α} (hf : StronglySummable f)
    (hg : StronglySummable g) :
    ∀ d : σ →₀ ℕ,
      (fun i : ι × κ => coeff d (f i.fst * g i.snd)).support ⊆
        ((antidiagonal d).biUnion fun b => (hf b.fst).toFinset).product
          ((antidiagonal d).biUnion fun b => (hg b.snd).toFinset) := by
  rintro d ⟨i, j⟩ h
  -- dsimp only [Function.mem_support, coeff_mul] at h
  suffices ∃ p ∈ antidiagonal d, coeff (p.fst : σ →₀ ℕ) (f i) * (coeff p.snd) (g j) ≠ 0 by
    obtain ⟨⟨b, c⟩, hbc, h'⟩ := this
    simp only [mem_antidiagonal] at hbc
    erw [Finset.mem_product]
    simp only [Finset.mem_biUnion, mem_antidiagonal, Finite.mem_toFinset, mem_support,
      ne_eq, Prod.exists]
    constructor
    . use b, c, hbc
      intro h₁
      apply h'
      rw [h₁, MulZeroClass.zero_mul]
    . use b, c, hbc
      intro h₂
      apply h'
      rw [h₂, MulZeroClass.mul_zero]
  · by_contra h'
    refine' h (sum_eq_zero _)
    push_neg at h'
    -- why is it necessary?
    simp only [mem_antidiagonal] at h' ⊢
    exact h'

/-- If `f` and `g` are strongly summable, then `λ i, coeff d (f i.fst * g i.snd)` is strongly
  summable. -/
theorem mul {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable fun i : ι × κ => f i.fst * g i.snd := by
  classical exact fun d => Finite.subset (finite_toSet _) (support_mul hf hg d)

/-- The sum of a strongly summable family of power series. -/
noncomputable def sum {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) : MvPowerSeries σ α :=
  fun d => (hf d).toFinset.sum fun i => coeff d (f i)

theorem coeff_sum_def {f : ι → MvPowerSeries σ α} {hf : StronglySummable f} (d : σ →₀ ℕ) :
    coeff d hf.sum = (hf d).toFinset.sum fun i => coeff d (f i) :=
  rfl

/-- If `f` is strongly summable, then for any `d : σ →₀ ℕ)` and any finite set `s` containing the
  support of `λ i, coeff d (f i)`, the coefficient `coeff d hf.sum` is equal to the sum
  of the coefficients `coeff d (f i)`, where `i` runs over `s`. -/
theorem coeff_sum {f : ι → MvPowerSeries σ α} {hf : StronglySummable f} (d : σ →₀ ℕ) {s : Finset ι}
    (hs : (fun i => coeff d (f i)).support ⊆ s) :
    coeff d hf.sum = s.sum fun i => coeff d (f i) := by
  rw [coeff_sum_def, sum_subset (Finite.toFinset_subset.mpr hs)]
  intro i _ hi'
  simpa only [Finite.mem_toFinset, Function.mem_support, Classical.not_not] using hi'

/-- If `f` and `g` are strongly summable and equal, then their sums agree. -/
theorem sum_congr {f g : ι → MvPowerSeries σ α} {hf : StronglySummable f} {hg : StronglySummable g}
    (h : f = g) : hf.sum = hg.sum := by
  ext d
  simp only [coeff_sum_def]
  refine' Finset.sum_congr _ fun i _ => by rw [h]
  ext i
  simp only [Finite.mem_toFinset, mem_support, ne_eq, h]

--ADDED
/-- If `f` and `g` are strongly summable, then the sum of `f + g` is equal to the sum of `f`
  plus the sum of `g`. -/
theorem sum_add {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g) :
  (add hf hg).sum = hf.sum + hg.sum := by
  classical
  ext d
  simp only [map_add]
  rw [coeff_sum d (support_add hf hg d), coeff_sum d, coeff_sum d]
  simp only [Pi.add_apply, map_add]
  rw [sum_add_distrib]
  all_goals
    simp only [coe_union, Finite.coe_toFinset, Set.subset_union_right, Set.subset_union_left]

--TODO: remove?
theorem sum_add' {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g)
    (hh : StronglySummable (f + g)) : hh.sum = hf.sum + hg.sum := by
  classical
  ext d
  simp only [map_add]
  rw [coeff_sum d (support_add hf hg d), coeff_sum d, coeff_sum d]
  simp only [Pi.add_apply, map_add]
  rw [sum_add_distrib]
  all_goals
    simp only [coe_union, Finite.coe_toFinset, Set.subset_union_right, Set.subset_union_left]

/-- If `f` and `g` are strongly summable, then the sum of `λ i, coeff d (f i.fst * g i.snd)`
  is equal to the sum of `f` times the sum of `g`. -/
theorem sum_mul {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    (mul hf hg).sum = hf.sum * hg.sum := by
  classical
  ext d
  simp_rw [coeff_sum d (support_mul hf hg d), coeff_mul]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  rintro bc hbc
  erw [Finset.sum_product]
  rw [coeff_sum _, coeff_sum _, sum_mul_sum]
  all_goals
    intro x hx
    apply @Finset.subset_biUnion_of_mem _ _ _ _ _ bc hbc
    exact (Finite.mem_toFinset _).mpr hx

--TODO: remove?
theorem sum_mul' {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g)
    (hh : StronglySummable fun i : ι × κ => f i.fst * g i.snd) :
    hh.sum = hf.sum * hg.sum := by
  rw [← sum_mul]

/-- If `f` is strongly summable and `s : Set ι` is any set, then `λ i, s.indicator f i` is
  strongly summable.-/
theorem of_indicator {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    StronglySummable fun i => s.indicator f i := by
  intro d
  apply (hf d).subset
  intro i
  simp only [mem_support, ne_eq, not_imp_not]
  intro hi
  rcases s.indicator_eq_zero_or_self f i with h | h <;>
  simp only [h, hi, map_zero]


/-- If `f` is strongly summable and `s : Set ι` is any set, then the sum of `f` equals the sum of
  `f` over `s` plus the sum of `f` over the complement of `s`. -/
theorem add_compl {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    hf.sum = (hf.of_indicator s).sum + (hf.of_indicator (sᶜ)).sum := by
  rw [← sum_add (hf.of_indicator s) (hf.of_indicator (sᶜ))]
  exact sum_congr (s.indicator_self_add_compl f).symm

/-- If `f` is strongly summable and `s : Set ι` is any set, then
  `f ∘ (↑) : ↥s → MvPowerSeries σ α` is strongly summable. -/
theorem on_subtype  {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    StronglySummable (f ∘ (↑) : ↥s → MvPowerSeries σ α) := by
  intro d
  apply Finite.of_finite_image _ (injOn_of_injective Subtype.coe_injective)
  apply (hf d).subset
  rintro i ⟨j, hj, rfl⟩
  simp only [comp_apply, mem_support, ne_eq] at hj ⊢
  exact hj

/-- If `f` is strongly summable and `d : σ →₀ ℕ`, then the infinite sum of
  `λ i, coeff d (f i)` is equal to `coeff d hf.sum`. -/
theorem hasSum_coeff [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (d : σ →₀ ℕ) : HasSum (fun i => coeff d (f i)) (coeff d hf.sum) := by
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  rw [Finite.mem_toFinset, Function.mem_support, Classical.not_not] at hb
  exact hb

/-- If `f` is strongly summable and `d : σ →₀ ℕ`, then `λ i, coeff d (f i)` is summable. -/
theorem summable_coeff [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (d : σ →₀ ℕ) : Summable fun i => coeff d (f i) :=
  ⟨coeff d hf.sum, hf.hasSum_coeff d⟩

end StronglySummable

open Finsupp

/-- Given `w : σ → ℕ` and `f : MvPowerSeries σ α`, the family `λ p, homogeneousComponent w p f`
  is strongly summable. -/
theorem homogeneous_components_self_stronglySummable (w : σ → ℕ) (f : MvPowerSeries σ α) :
    StronglySummable fun p => weightedHomogeneousComponent w p f := by
  intro d
  apply (finite_toSet {weight w d}).subset
  intro p
  rw [Function.mem_support, ne_eq, mem_coe, coeff_weightedHomogeneousComponent, Finset.mem_singleton,
    ite_eq_right_iff, not_forall, exists_prop, and_imp]
  intro h _
  exact h.symm

/-- Given `w : σ → ℕ` and `f : MvPowerSeries σ α`, then `f` is equal to the sum of its
  homogeneous components. -/
theorem as_sum_of_homogeneous_components (w : σ → ℕ) (f : MvPowerSeries σ α) :
    f = (homogeneous_components_self_stronglySummable w f).sum := by
  ext d
  simp_rw [coeff_apply, StronglySummable.sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · simp only [if_true]
    rfl
  · intro b _ h'
    rw [if_neg (Ne.symm h')]
  · simp only [Finite.mem_toFinset, Function.mem_support, Classical.not_not, imp_self]

-- TODO: remove?
theorem as_sum_of_homogeneous_components' (w : σ → ℕ) (f : MvPowerSeries σ α) :
    ∀ hf : StronglySummable fun p => weightedHomogeneousComponent w p f, f = hf.sum := by
  intro hf
  ext d
  simp_rw [coeff_apply, StronglySummable.sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · simp only [if_true]
    rfl
  · intro b _ h'
    rw [if_neg (Ne.symm h')]
  · simp only [Finite.mem_toFinset, Function.mem_support, Classical.not_not, imp_self]

end Semiring

end StronglySummable

section StronglyMultipliable

variable [CommRing α] {ι : Type _} (f : ι → MvPowerSeries σ α)

/-- The map sending `(I : finset ι)` to the finite product `I.prod (λ i, f i)`. -/
noncomputable def partialProduct : Finset ι → MvPowerSeries σ α := fun I => I.prod fun i => f i

/-- If `f` is strongly summable, the support of `λ I, coeff d (partialProduct f I)` is contained
  in the powerset of `hf.unionOfSupportOfCoeffLe d`. -/
theorem support_partialProduct_subset [DecidableEq ι] [DecidableEq σ]
    (hf : StronglySummable f) (d : σ →₀ ℕ) :
    (support fun I => coeff d (partialProduct f I)) ⊆
      (hf.unionOfSupportOfCoeffLe d).powerset := by
  intro I
  simp only [mem_support, ne_eq, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset, not_imp_comm, Finset.not_subset]
  rintro ⟨i, hi, h⟩
  rw [StronglySummable.not_mem_unionOfSupportOfCoeffLe_iff] at h
  simp only [partialProduct, prod_eq_mul_prod_diff_singleton hi, coeff_mul]
  apply sum_eq_zero
  rintro ⟨x, y⟩
  rw [mem_antidiagonal]
  intro hxy
  rw [h x _, MulZeroClass.zero_mul]
  simp only [← hxy, le_self_add]



/- TODO : give a more general (and easier) definition
 A family `f` is strongly multipliable if for each `d`,
 the coefficients `coeff d (s.prod f)` of the finite products are eventually constant
 and rewrite the case of sums in the same spirit
 But beware of subfamilies when `∃ i, f i = 0` -/
/-- The family `f` is strongly multipliable if the family `F` on `{ I : Set ι | I.Finite}`
  formed by all finite products `I.prod (λ i, f i)` is strongly_summable -/
def StronglyMultipliable : Prop :=
  StronglySummable (partialProduct f)

variable {f}

namespace StronglyMultipliable

/-- The product of the family of `(1 + f ι)`, when `f` is strongly_multipliable  -/
noncomputable def prod (hf : StronglyMultipliable f) : MvPowerSeries σ α := hf.sum

/-- If `f` is strongly_multipliable, the product of the family of `(1 + f ι)` is equal to the
  sum of `partialProduct f`.   -/
theorem prod_eq (hf : StronglyMultipliable f) : hf.prod = hf.sum :=
  rfl

end StronglyMultipliable
namespace StronglySummable

--NOTE: renamed so that we can use dot notation
/-- If `f = Σ f i` is strongly summable, then `Π (1 + f i)` is strongly multipliable -/
theorem toStronglyMultipliable (hf : StronglySummable f) :
    StronglyMultipliable f := by
  classical
  exact fun d => Finite.subset (finite_toSet _) (support_partialProduct_subset f hf d)

end StronglySummable
namespace StronglyMultipliable

/-- If `f` is strongly_multipliable and `s : Finset ι`, the product of `λ i, (1 + f ι)` over `s`
  is equal to the sum of `hf.of_indicator {I : Finset ι | I ⊆ s}`.   -/
theorem finset_prod_eq [DecidableEq ι] (s : Finset ι) (hf : StronglyMultipliable f) :
    (s.prod fun i => 1 + f i)
      = (hf.of_indicator {I : Finset ι | I ⊆ s}).sum := by
  rw [Finset.prod_one_add]
  ext d
  rw [map_sum, StronglySummable.coeff_sum d]
  · apply sum_congr rfl
    intro t ht
    apply congr_arg
    rw [indicator, if_pos]; rfl
    · exact Finset.mem_powerset.mp ht
  · intro t
    rw [mem_support, ne_eq, mem_coe, Finset.mem_powerset, not_imp_comm]
    intro ht'
    rw [indicator, if_neg, map_zero]
    exact ht'

/-- If `f` is strongly_multipliable and `s : Set ι`, the product of the family `(1 + f ι)`
  is equal to the sum `(hf.of_indicator {I : Finset ι | ↑I ⊆ s}).sum +
      (hf.of_indicator ({I : Finset ι | ↑I ⊆ s}ᶜ)).sum`.   -/
theorem prod_eq_sum_add_sum (hf : StronglyMultipliable f) (s : Set ι) :
    hf.prod = (hf.of_indicator {I : Finset ι | ↑I ⊆ s}).sum +
      (hf.of_indicator ({I : Finset ι | ↑I ⊆ s}ᶜ)).sum :=
  by rw [hf.prod_eq, ← hf.add_compl]

/-- A version of `prod_eq_sum_add_sum` for `s : Finset ι`. -/
theorem prod_eq_finset_prod_add [DecidableEq ι] (hf : StronglyMultipliable f) (s : Finset ι) :
    hf.prod = (s.prod fun i => 1 + f i) + (hf.of_indicator ({I : Finset ι | I ⊆ s}ᶜ)).sum := by
  rw [hf.prod_eq_sum_add_sum s, hf.finset_prod_eq s]

/-- If `f` is strongly summable, `d : σ →₀ ℕ`, and `J` is a finite set containing
  `hf.unionOfSupportOfCoeffLe d`, then the `d`th coefficients of the product of the strongly
  multipliable family `1 + f i` agrees with the one of `J.prod fun i => 1 + f i`. -/
theorem coeff_prod_apply_eq_finset_prod [DecidableEq ι] [DecidableEq σ]
    (hf : StronglySummable f) {d : σ →₀ ℕ} {J : Finset ι} (hJ : hf.unionOfSupportOfCoeffLe d ⊆ J) :
    (coeff d) hf.toStronglyMultipliable.prod = (coeff d) (J.prod fun i => 1 + f i) := by
  rw [hf.toStronglyMultipliable.prod_eq_finset_prod_add J, map_add, add_eq_left,
    StronglySummable.coeff_sum_def]
  apply sum_eq_zero
  intro t _
  simp only [indicator, mem_compl_iff, mem_setOf_eq]
  split_ifs with h
  · rw [map_zero]
  . simp only [Finset.not_subset] at h
    obtain ⟨i, hit, hiJ⟩ := h
    simp only [partialProduct, prod_eq_mul_prod_diff_singleton hit, coeff_mul]
    apply sum_eq_zero
    rintro ⟨x, y⟩ hxy
    rw [mem_antidiagonal] at hxy
    rw [(hf.not_mem_unionOfSupportOfCoeffLe_iff d i).mp (fun hi => hiJ (hJ hi)) x _,
      MulZeroClass.zero_mul]
    simp only [← hxy, le_self_add]

end StronglyMultipliable

end StronglyMultipliable

end MvPowerSeries
