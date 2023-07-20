import Mathbin.RingTheory.PowerSeries.Basic
import Oneshot.MvPowerSeries.Order
import Oneshot.InfiniteSum.Basic
import Mathbin.Topology.Order.Basic

open Finset Filter Set

instance ENat.topology : _ :=
  Preorder.topology ℕ∞
#align enat.topology ENat.topology

instance : OrderTopology ℕ∞ :=
  ⟨rfl⟩

namespace Function

open scoped Pointwise

variable {α : Type _} {ι : Type _}

/-- If a function `f` to an additive commutative monoid with the discrete topology tends to zero
along the cofinite filter, then `f` has finite support. -/
theorem finite_support_of_tendsto_zero [AddCommMonoid α] [TopologicalSpace α] [DiscreteTopology α]
    {f : ι → α} (hf : Tendsto f cofinite (nhds 0)) : f.support.Finite :=
  by
  rw [nhds_discrete, tendsto_pure] at hf 
  obtain ⟨s, H, p⟩ := eventually.exists_mem hf
  apply finite.subset H
  intro x hx
  rw [mem_compl_iff]
  by_contra hxs
  exact hx (p x hxs)
#align function.finite_support_of_tendsto_zero Function.finite_support_of_tendsto_zero

/-- If a function `f` to a discrete topological commutative additive group is summable, then it has
finite support. -/
theorem finite_support_of_summable [AddCommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    [TopologicalAddGroup α] {f : ι → α} (hf : Summable f) : f.support.Finite :=
  finite_support_of_tendsto_zero hf.tendsto_cofinite_zero
#align function.finite_support_of_summable Function.finite_support_of_summable

/-- If a function `f` to a topological commutative additive group is summable, then it tends to zero
along the cofinite filter. -/
theorem tendsto_zero_of_summable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
    {f : ι → α} (hf : Summable f) : Tendsto f cofinite (nhds 0) := by
  classical
  obtain ⟨a, ha⟩ := hf
  rw [HasSum, tendsto_atTop_nhds] at ha 
  rw [tendsto_nhds]
  intro U₀ hU₀ memU₀
  suffices hU₁ : ∃ U₁ : Set α, IsOpen U₁ ∧ (0 : α) ∈ U₁ ∧ U₁ - U₁ ≤ U₀
  · obtain ⟨U₁, hU₁, memU₁, addU₁_subset⟩ := hU₁
    obtain ⟨S, hS⟩ :=
      ha ((fun x => x - a) ⁻¹' U₁) (by simp only [memU₁, Set.mem_preimage, sub_self])
        (IsOpen.preimage (continuous_sub_right a) hU₁)
    apply S.finite_to_set.Subset
    intro i hi
    by_contra his
    apply hi
    apply addU₁_subset
    use (insert i S).Sum f - a, S.sum f - a, hS (insert i S) (subset_insert i S), hS S le_rfl
    rw [sum_insert his, sub_sub_sub_cancel_right, add_sub_cancel]
  · suffices h_open : IsOpen ((fun xy : α × α => xy.fst - xy.snd) ⁻¹' U₀)
    · rw [isOpen_prod_iff] at h_open 
      obtain ⟨u, v, hu, hv, mem_u, mem_v, H⟩ :=
        h_open 0 0 (by simp only [Set.mem_preimage, sub_self, memU₀])
      use u ∩ v, IsOpen.inter hu hv, ⟨mem_u, mem_v⟩
      apply subset_trans _ (set.image_subset_iff.mpr H)
      rw [image_prod, image2_sub]
      rintro z ⟨x, y, hx, hy, rfl⟩
      exact ⟨x, y, mem_of_mem_inter_left hx, mem_of_mem_inter_right hy, rfl⟩
    · exact IsOpen.preimage continuous_sub hU₀
#align function.tendsto_zero_of_summable Function.tendsto_zero_of_summable

end Function

namespace MvPowerSeries

open Function

variable {σ α : Type _}

section StronglySummable

variable {ι : Type _}

section Semiring

variable [Semiring α]

/-- A family of power series is `strongly summable` if for every finitely supported function
`(d : σ →₀ ℕ)`, the function `λ i, coeff α d (f i)` is finitely supported. -/
def StronglySummable (f : ι → MvPowerSeries σ α) : Prop :=
  ∀ d : σ →₀ ℕ, (fun i => coeff α d (f i)).support.Finite
#align mv_power_series.strongly_summable MvPowerSeries.StronglySummable

namespace StronglySummable

theorem congr {f g : ι → MvPowerSeries σ α} (h : f = g) : StronglySummable f ↔ StronglySummable g :=
  by rw [h]
#align mv_power_series.strongly_summable.congr MvPowerSeries.StronglySummable.congr

section Order

-- Bourbaki, *Algèbre*, chap. 4, §4, page IV.25, exemple c)
/-- A family of power series is strongly summable if their weighted orders tend to infinity. -/
theorem of_weightedOrder_tendsto_top (w : σ → ℕ) (f : ι → MvPowerSeries σ α)
    (hf : Tendsto (fun i => weightedOrder w (f i)) cofinite (nhds ⊤)) : StronglySummable f :=
  by
  intro d
  rw [has_basis.tendsto_right_iff nhds_top_basis] at hf 
  specialize hf (weight w d : ℕ∞) (WithTop.coe_lt_top _)
  refine' hf.subset _
  intro i
  simp only [mem_support, Ne.def, mem_set_of_eq]
  intro h' h
  apply h'
  exact coeff_of_lt_weighted_order w _ h
  · infer_instance
  · infer_instance
#align mv_power_series.strongly_summable.of_weighted_order_tendsto_top MvPowerSeries.StronglySummable.of_weightedOrder_tendsto_top

theorem of_order_tendsto_top (f : ι → MvPowerSeries σ α)
    (hf : Tendsto (fun i => order (f i)) cofinite (nhds ⊤)) : StronglySummable f :=
  of_weightedOrder_tendsto_top _ f hf
#align mv_power_series.strongly_summable.of_order_tendsto_top MvPowerSeries.StronglySummable.of_order_tendsto_top

-- Réciproques quand σ est fini !
/-- When σ is finite, a family of power series is strongly summable 
iff their weighted orders tend to infinity. -/
theorem weightedOrder_tendsto_top_iff [Finite σ] {ι : Type _} {w : σ → ℕ} (hw : ∀ x, w x ≠ 0)
    (f : ι → MvPowerSeries σ α) :
    StronglySummable f ↔ Tendsto (fun i => weightedOrder w (f i)) cofinite (nhds ⊤) :=
  by
  refine' ⟨fun hf => _, of_weighted_order_tendsto_top w f⟩
  · rw [has_basis.tendsto_right_iff nhds_top_basis]
    intro n hn
    induction n
    · exfalso; exact lt_irrefl ⊤ hn
    · simp only [Set.mem_Ioi, eventually_cofinite, not_lt]
      let s := {d : σ →₀ ℕ | ↑(weight w d) ≤ n}
      suffices h_ss :
        {i | (f i).weightedOrder w ≤ some n} ⊆ ⋃ (d : σ →₀ ℕ) (H : d ∈ s), {i | coeff α d (f i) ≠ 0}
      · exact ((finite_of_weight_le w hw n).biUnion fun d hd => hf d).Subset h_ss
      · intro i hi
        simp only [mem_set_of_eq, Nat.cast_id, Ne.def, mem_Union, exists_prop]
        obtain ⟨d, hd⟩ := exists_coeff_ne_zero_of_weighted_order w (f i) _
        refine' ⟨d, _, hd.2⟩
        simpa [← hd.1, WithTop.some_eq_coe, Nat.cast_le] using hi
        rw [ENat.coe_toNat_eq_self]
        · intro hi'
          rw [mem_set_of_eq, hi', top_le_iff] at hi 
          exact WithTop.coe_ne_top hi
    · infer_instance
    · infer_instance
#align mv_power_series.strongly_summable.weighted_order_tendsto_top_iff MvPowerSeries.StronglySummable.weightedOrder_tendsto_top_iff

/-- When σ is finite, a family of power series is strongly summable 
iff their orders tend to infinity. -/
theorem order_tendsto_top_iff [Finite σ] (f : ι → MvPowerSeries σ α) :
    StronglySummable f ↔ Tendsto (fun i => order (f i)) cofinite (nhds ⊤) :=
  weightedOrder_tendsto_top_iff (by simp) f
#align mv_power_series.strongly_summable.order_tendsto_top_iff MvPowerSeries.StronglySummable.order_tendsto_top_iff

end Order

/-- The union of the supports of the functions `λ i, coeff α e (f i)`, where `e` runs over
the coefficients bounded by `d`. -/
noncomputable def unionOfSupportOfCoeffLe [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) : Finset ι :=
  Finset.biUnion (Iic d) fun e => (hf e).toFinset
#align mv_power_series.strongly_summable.union_of_support_of_coeff_le MvPowerSeries.StronglySummable.unionOfSupportOfCoeffLe

theorem not_mem_unionOfSupportOfCoeffLe_iff [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) (i : ι) :
    i ∉ hf.unionOfSupportOfCoeffLe d ↔ ∀ (e) (he : e ≤ d), coeff α e (f i) = 0 := by
  simp only [union_of_support_of_coeff_le, Finset.mem_biUnion, Finset.mem_Iic, finite.mem_to_finset,
    mem_support, not_exists, Classical.not_not]
#align mv_power_series.strongly_summable.not_mem_union_of_support_of_coeff_le_iff MvPowerSeries.StronglySummable.not_mem_unionOfSupportOfCoeffLe_iff

/- lemma union_of_coeff_support_finite {f : ι → mv_power_series σ α} 
  (hf : strongly_summable f) (d : σ →₀ ℕ) : 
  (⋃ e (H : e ≤ d), (λ i, coeff α e (f i)).support).finite := 
(set.Iic d).to_finite.bUnion (λ d H, hf d) -/
theorem of_subset_union_of_coeff_support_finite [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) :
    {I : Finset ι | I ⊆ hf.unionOfSupportOfCoeffLe d}.Finite :=
  by
  suffices
    {I : Finset ι | I ⊆ hf.union_of_support_of_coeff_le d} =
      (hf.union_of_support_of_coeff_le d).powerset
    by rw [this]; apply finite_to_set
  ext I
  simp only [mem_set_of_eq, coe_powerset, Set.mem_preimage, mem_powerset_iff, coe_subset]
#align mv_power_series.strongly_summable.of_subset_union_of_coeff_support_finite MvPowerSeries.StronglySummable.of_subset_union_of_coeff_support_finite

theorem support_add [DecidableEq ι] {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (hg : StronglySummable g) :
    ∀ d : σ →₀ ℕ,
      (fun i => coeff α d ((f + g) i)).support ⊆ ((hf d).toFinset ∪ (hg d).toFinset : Finset ι) :=
  by
  intro d i
  simp only [Pi.add_apply, map_add, Function.mem_support, Ne.def, coe_union, finite.coe_to_finset,
    Set.mem_union]
  intro h
  by_cases h₁ : coeff α d (f i) = 0
  · right; simpa [h₁] using h
  · left; exact h₁
#align mv_power_series.strongly_summable.support_add MvPowerSeries.StronglySummable.support_add

theorem add {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable (f + g) := by
  classical exact fun d => finite.subset (finite_to_set _) (support_add hf hg d)
#align mv_power_series.strongly_summable.add MvPowerSeries.StronglySummable.add

theorem smul {f : ι → MvPowerSeries σ α} (a : ι → α) (hf : StronglySummable f) :
    StronglySummable (a • f) := by
  intro d
  apply finite.subset (hf d)
  intro i
  simp only [Pi.smul_apply', Pi.smul_apply, Function.mem_support, Ne.def]
  intro h h'
  apply h
  rw [coeff_smul, h', MulZeroClass.mul_zero]
#align mv_power_series.strongly_summable.smul MvPowerSeries.StronglySummable.smul

theorem support_mul [DecidableEq ι] {f : ι → MvPowerSeries σ α} {κ : Type _} [DecidableEq κ]
    {g : κ → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g) :
    ∀ d : σ →₀ ℕ,
      (fun i : ι × κ => coeff α d (f i.fst * g i.snd)).support ⊆
        (d.antidiagonal.biUnion fun b => (hf b.fst).toFinset).product
          (d.antidiagonal.biUnion fun b => (hg b.snd).toFinset) :=
  by
  rintro d ⟨i, j⟩ h
  dsimp only [Function.mem_support, coeff_mul] at h 
  suffices ∃ p ∈ d.antidiagonal, coeff α (p.fst : σ →₀ ℕ) (f i) * (coeff α p.snd) (g j) ≠ 0
    by
    obtain ⟨⟨b, c⟩, hbc, h'⟩ := this
    rw [Finsupp.mem_antidiagonal] at hbc 
    simp only [coe_product, coe_bUnion, mem_coe, Finsupp.mem_antidiagonal, finite.coe_to_finset,
      prod_mk_mem_set_prod_eq, mem_Union, Function.mem_support, Ne.def, exists_prop, Prod.exists]
    constructor
    use b; use c; apply And.intro hbc; intro h₁; apply h'; rw [h₁]; rw [MulZeroClass.zero_mul]
    use b; use c; apply And.intro hbc; intro h₂; apply h'; rw [h₂]; rw [MulZeroClass.mul_zero]
  · by_contra' h'
    exact h (sum_eq_zero h')
#align mv_power_series.strongly_summable.support_mul MvPowerSeries.StronglySummable.support_mul

theorem mul {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable fun i : ι × κ => f i.fst * g i.snd := by
  classical exact fun d => finite.subset (finite_to_set _) (support_mul hf hg d)
#align mv_power_series.strongly_summable.mul MvPowerSeries.StronglySummable.mul

/-- The sum of a strongly summable family of power series. -/
noncomputable def sum {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) : MvPowerSeries σ α :=
  fun d => (hf d).toFinset.Sum fun i => coeff α d (f i)
#align mv_power_series.strongly_summable.sum MvPowerSeries.StronglySummable.sum

theorem CoeffSum.def {f : ι → MvPowerSeries σ α} {hf : StronglySummable f} (d : σ →₀ ℕ) :
    coeff α d hf.Sum = (hf d).toFinset.Sum fun i => coeff α d (f i) :=
  rfl
#align mv_power_series.strongly_summable.coeff_sum.def MvPowerSeries.StronglySummable.CoeffSum.def

theorem coeff_sum {f : ι → MvPowerSeries σ α} {hf : StronglySummable f} (d : σ →₀ ℕ) (s : Finset ι)
    (hs : (fun i => coeff α d (f i)).support ⊆ s) :
    coeff α d hf.Sum = s.Sum fun i => coeff α d (f i) :=
  by
  rw [coeff_sum.def, sum_subset (finite.to_finset_subset.mpr hs)]
  intro i hi hi'
  simpa only [finite.mem_to_finset, Function.mem_support, Classical.not_not] using hi'
#align mv_power_series.strongly_summable.coeff_sum MvPowerSeries.StronglySummable.coeff_sum

theorem sum_congr {f g : ι → MvPowerSeries σ α} {hf : StronglySummable f} {hg : StronglySummable g}
    (h : f = g) : hf.Sum = hg.Sum := by
  ext d
  rw [coeff_sum.def]
  refine' sum_congr _ fun i hi => by rw [h]
  ext i
  simp only [finite.mem_to_finset, mem_support, Ne.def, h]
#align mv_power_series.strongly_summable.sum_congr MvPowerSeries.StronglySummable.sum_congr

theorem sum_add {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g)
    (hh : StronglySummable (f + g)) : hh.Sum = hf.Sum + hg.Sum := by
  classical
  ext d
  simp only [coeff_sum, Pi.add_apply, map_add]
  rw [coeff_sum d _ (support_add hf hg d), coeff_sum d, coeff_sum d]
  simp only [Pi.add_apply, map_add, Finset.union_assoc]
  rw [sum_add_distrib]
  all_goals
    simp only [coe_union, finite.coe_to_finset, Set.subset_union_right, Set.subset_union_left]
#align mv_power_series.strongly_summable.sum_add MvPowerSeries.StronglySummable.sum_add

theorem sum_mul {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g)
    (hh : StronglySummable fun i : ι × κ => f i.fst * g i.snd) : hh.Sum = hf.Sum * hg.Sum := by
  classical
  ext d
  simp_rw [coeff_sum d _ (support_mul hf hg d), coeff_mul]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro bc hbc
  rw [coeff_sum bc.fst, coeff_sum bc.snd, sum_mul_sum]
  all_goals
    simp only [coe_bUnion, finite.coe_to_finset, mem_coe]
    exact @Set.subset_biUnion_of_mem _ _ _ _ bc hbc
#align mv_power_series.strongly_summable.sum_mul MvPowerSeries.StronglySummable.sum_mul

theorem of_indicator {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    StronglySummable fun i => s.indicator f i :=
  by
  intro d
  apply (hf d).Subset
  intro i
  simp only [mem_support, Ne.def, not_imp_not]
  intro hi
  cases s.indicator_eq_zero_or_self f i <;> simp only [h, hi, map_zero]
#align mv_power_series.strongly_summable.of_indicator MvPowerSeries.StronglySummable.of_indicator

theorem add_compl {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    hf.Sum = (hf.of_indicator s).Sum + (hf.of_indicator (sᶜ)).Sum :=
  by
  have hf' : strongly_summable (s.indicator f + sᶜ.indicator f) := by
    rw [s.indicator_self_add_compl f]; exact hf
  rw [← sum_add (hf.of_indicator s) (hf.of_indicator (sᶜ)) hf']
  exact sum_congr (s.indicator_self_add_compl f).symm
#align mv_power_series.strongly_summable.add_compl MvPowerSeries.StronglySummable.add_compl

theorem on_subtype {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    StronglySummable (f ∘ coe : ↥s → MvPowerSeries σ α) :=
  by
  intro d
  apply finite.of_finite_image _ (inj_on_of_injective Subtype.coe_injective _)
  apply (hf d).Subset
  rintro i ⟨j, hj, rfl⟩
  simp only [comp_app, mem_support, Ne.def] at hj ⊢
  exact hj
#align mv_power_series.strongly_summable.on_subtype MvPowerSeries.StronglySummable.on_subtype

theorem hasSum_coeff [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (d : σ →₀ ℕ) : HasSum (fun i => coeff α d (f i)) (coeff α d hf.Sum) :=
  by
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  rw [finite.mem_to_finset, Function.mem_support, Classical.not_not] at hb 
  exact hb
#align mv_power_series.strongly_summable.has_sum_coeff MvPowerSeries.StronglySummable.hasSum_coeff

theorem summable_coeff [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (d : σ →₀ ℕ) : Summable fun i => coeff α d (f i) :=
  ⟨coeff α d hf.Sum, hf.hasSum_coeff d⟩
#align mv_power_series.strongly_summable.summable_coeff MvPowerSeries.StronglySummable.summable_coeff

end StronglySummable

theorem homogeneous_components_self_stronglySummable (w : σ → ℕ) (f : MvPowerSeries σ α) :
    StronglySummable fun p => homogeneousComponent w p f :=
  by
  intro d
  apply (finite_to_set {weight w d}).Subset
  intro p
  rw [Function.mem_support, Ne.def, mem_coe, coeff_homogeneous_component, Finset.mem_singleton,
    ite_eq_right_iff, not_forall, exists_prop, and_imp]
  intro h h'
  exact h.symm
#align mv_power_series.homogeneous_components_self_strongly_summable MvPowerSeries.homogeneous_components_self_stronglySummable

theorem as_sum_of_homogeneous_components (w : σ → ℕ) (f : MvPowerSeries σ α) :
    ∀ hf : StronglySummable fun p => homogeneousComponent w p f, f = hf.Sum :=
  by
  intro hf
  ext d
  simp only [strongly_summable.sum, coeff_apply, coeff_homogeneous_component]
  rw [sum_eq_single (weight w d)]
  · simp only [eq_self_iff_true, if_true]
  · intro b h h'; rw [if_neg (Ne.symm h')]
  · simp only [finite.mem_to_finset, Function.mem_support, Classical.not_not, imp_self]
#align mv_power_series.as_sum_of_homogeneous_components MvPowerSeries.as_sum_of_homogeneous_components

end Semiring

end StronglySummable

section StronglyMultipliable

variable [CommRing α] {ι : Type _} (f : ι → MvPowerSeries σ α)

/-- The map sending `(I : finset ι)` to the finite product `I.prod (λ i, f i)`. -/
noncomputable def partialProduct : Finset ι → MvPowerSeries σ α := fun I => I.Prod fun i => f i
#align mv_power_series.partial_product MvPowerSeries.partialProduct

/- TODO : give a more general (and easier) definition 
 A family `f` is strongly multipliable if for each `d`,
 the coefficients `coeff α d (s.prod f)` of the finite products are eventually constant 
 and rewrite the case of sums in the same spirit
 But beware of subfamilies when `∃ i, f i = 0` -/
/-- The family f is strongly multipliable if the family F on { I : set ι | I.finite} 
  defined by… is strongly_summable -/
def StronglyMultipliable : Prop :=
  StronglySummable (partialProduct f)
#align mv_power_series.strongly_multipliable MvPowerSeries.StronglyMultipliable

variable {f}

/-- The product of the family of (1 + f ι), when it is strongly_multipliable  -/
noncomputable def StronglyMultipliable.prod (hf : StronglyMultipliable f) : MvPowerSeries σ α :=
  hf.Sum
#align mv_power_series.strongly_multipliable.prod MvPowerSeries.StronglyMultipliable.prod

theorem StronglyMultipliable.prod_eq (hf : StronglyMultipliable f) : hf.Prod = hf.Sum :=
  rfl
#align mv_power_series.strongly_multipliable.prod_eq MvPowerSeries.StronglyMultipliable.prod_eq

theorem StronglySummable.support_partialProduct_le [DecidableEq ι] (hf : StronglySummable f)
    (d : σ →₀ ℕ) :
    (support fun I => coeff α d (partialProduct f I)) ⊆ (hf.unionOfSupportOfCoeffLe d).powerset :=
  by
  intro I
  simp only [mem_support, Ne.def, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset,
    not_imp_comm, Finset.not_subset]
  rintro ⟨i, hi, h⟩
  rw [strongly_summable.not_mem_union_of_support_of_coeff_le_iff] at h 
  simp only [partial_product, prod_eq_mul_prod_diff_singleton hi, coeff_mul]
  apply sum_eq_zero
  rintro ⟨x, y⟩
  rw [Finsupp.mem_antidiagonal]
  intro hxy
  rw [h x _, MulZeroClass.zero_mul]
  simp only [← hxy, Finsupp.le_def, Finsupp.coe_add, Pi.add_apply, le_self_add]
#align mv_power_series.strongly_summable.support_partial_product_le MvPowerSeries.StronglySummable.support_partialProduct_le

theorem StronglySummable.to_stronglyMultipliable (hf : StronglySummable f) :
    StronglyMultipliable f := by
  classical exact fun d => finite.subset (finite_to_set _) (hf.support_partial_product_le d)
#align mv_power_series.strongly_summable.to_strongly_multipliable MvPowerSeries.StronglySummable.to_stronglyMultipliable

--TODO: move
theorem Finset.prod_one_add' {ι α : Type _} [CommRing α] {f : ι → α} (s : Finset ι) :
    (s.Prod fun i => 1 + f i) = s.powerset.Sum fun t => t.Prod f :=
  by
  simp_rw [add_comm, prod_add]
  apply congr_arg
  ext t
  convert mul_one _
  exact prod_eq_one fun i hi => rfl
#align mv_power_series.finset.prod_one_add' MvPowerSeries.Finset.prod_one_add'

theorem StronglyMultipliable.finset_prod_eq (s : Finset ι) (hf : StronglyMultipliable f) :
    (s.Prod fun i => 1 + f i) = (hf.of_indicator {I : Finset ι | I ⊆ s}).Sum :=
  by
  rw [finset.prod_one_add']
  ext d
  rw [map_sum, strongly_summable.coeff_sum d s.powerset]
  · apply sum_congr rfl
    intro t ht
    apply congr_arg
    rw [indicator, if_pos]; rfl
    · exact finset.mem_powerset.mp ht
  · intro t
    rw [mem_support, Ne.def, mem_coe, Finset.mem_powerset, not_imp_comm]
    intro ht'
    rw [indicator, if_neg, map_zero]
    exact ht'
#align mv_power_series.strongly_multipliable.finset_prod_eq MvPowerSeries.StronglyMultipliable.finset_prod_eq

theorem StronglyMultipliable.prod_eq_sum_add_sum (hf : StronglyMultipliable f) (s : Set ι) :
    hf.Prod =
      (hf.of_indicator {I : Finset ι | ↑I ⊆ s}).Sum +
        (hf.of_indicator ({I : Finset ι | ↑I ⊆ s}ᶜ)).Sum :=
  by rw [hf.prod_eq, ← hf.add_compl]
#align mv_power_series.strongly_multipliable.prod_eq_sum_add_sum MvPowerSeries.StronglyMultipliable.prod_eq_sum_add_sum

theorem StronglyMultipliable.prod_eq_finset_prod_add (hf : StronglyMultipliable f) (s : Finset ι) :
    hf.Prod = (s.Prod fun i => 1 + f i) + (hf.of_indicator ({I : Finset ι | I ⊆ s}ᶜ)).Sum := by
  rw [hf.prod_eq_sum_add_sum s, hf.finset_prod_eq s] <;> rfl
#align mv_power_series.strongly_multipliable.prod_eq_finset_prod_add MvPowerSeries.StronglyMultipliable.prod_eq_finset_prod_add

theorem StronglySummable.Finset.prod_of_one_add_eq [DecidableEq ι] (hf : StronglySummable f)
    (d : σ →₀ ℕ) (J : Finset ι) (hJ : hf.unionOfSupportOfCoeffLe d ⊆ J) :
    (coeff α d) (J.Prod fun i => 1 + f i) = (coeff α d) hf.to_stronglyMultipliable.Prod :=
  by
  rw [hf.to_strongly_multipliable.prod_eq_finset_prod_add J, map_add, self_eq_add_right,
    strongly_summable.coeff_sum.def]
  apply sum_eq_zero
  intro t ht
  rw [indicator]
  split_ifs with h
  · rw [mem_compl_iff, mem_set_of_eq, Finset.not_subset] at h 
    obtain ⟨i, hit, hiJ⟩ := h
    simp only [partial_product, prod_eq_mul_prod_diff_singleton hit, coeff_mul]
    apply sum_eq_zero
    rintro ⟨x, y⟩
    rw [Finsupp.mem_antidiagonal]
    intro hxy
    rw [(hf.not_mem_union_of_support_of_coeff_le_iff d i).mp (fun hi => hiJ (hJ hi)) x _,
      MulZeroClass.zero_mul]
    simp only [← hxy, Finsupp.le_def, Finsupp.coe_add, Pi.add_apply, le_self_add]
  · rw [map_zero]
#align mv_power_series.strongly_summable.finset.prod_of_one_add_eq MvPowerSeries.StronglySummable.Finset.prod_of_one_add_eq

end StronglyMultipliable

end MvPowerSeries

