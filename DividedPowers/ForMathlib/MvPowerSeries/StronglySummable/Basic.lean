import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Order.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Order
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
--import Mathlib.Data.Finsupp.Union

--TODO: move
--NOTE: I renamed it because `Finset.prod_one_add` is already declared in `MvPowerSeries.Topology`
theorem Finset.prod_one_add' {ι α : Type _} [CommRing α] {f : ι → α} (s : Finset ι) :
    (s.prod fun i => 1 + f i) = s.powerset.sum fun t => t.prod f := by
  classical
  simp_rw [add_comm, prod_add]
  apply congr_arg
  ext t
  convert mul_one ((Finset.prod t fun a => f a))
  exact prod_eq_one fun i _ => rfl

open Finset Filter Set

instance ENat.topology : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞
#align enat.topology ENat.topology

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
    sorry
    /- use (insert i S).sum f - a, S.sum f - a, hS (insert i S) (subset_insert i S), hS S le_rfl
    simp only [sum_insert his, sub_sub_sub_cancel_right, add_sub_cancel] -/
  · suffices h_open : IsOpen ((fun xy : α × α => xy.fst - xy.snd) ⁻¹' U₀) by
      rw [isOpen_prod_iff] at h_open
      obtain ⟨u, v, hu, hv, mem_u, mem_v, H⟩ :=
        h_open 0 0 (by simp only [Set.mem_preimage, sub_self, memU₀])
      use u ∩ v, IsOpen.inter hu hv, ⟨mem_u, mem_v⟩
      apply subset_trans _ (Set.image_subset_iff.mpr H)
      rw [image_prod]
      rintro z ⟨x, y, hx, hy, rfl⟩
      sorry --exact ⟨x, y, mem_of_mem_inter_left hx, mem_of_mem_inter_right hy, rfl⟩
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
    (hf : Tendsto (fun i => weightedOrder w (f i)) cofinite (nhds ⊤)) : StronglySummable f := by
  intro d
  rw [HasBasis.tendsto_right_iff nhds_top_basis] at hf
  specialize hf (weight w d : ℕ∞) (WithTop.coe_lt_top _)
  refine' hf.subset _
  intro i  h' h
  apply h'
  exact coeff_of_lt_weightedOrder w _ h
#align mv_power_series.strongly_summable.of_weighted_order_tendsto_top
  MvPowerSeries.StronglySummable.of_weightedOrder_tendsto_top

theorem of_order_tendsto_top (f : ι → MvPowerSeries σ α)
    (hf : Tendsto (fun i => order (f i)) cofinite (nhds ⊤)) : StronglySummable f :=
  of_weightedOrder_tendsto_top _ f hf
#align mv_power_series.strongly_summable.of_order_tendsto_top
  MvPowerSeries.StronglySummable.of_order_tendsto_top

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
      suffices h_ss : {i | (f i).weightedOrder w ≤ some n} ⊆
          ⋃ (d : σ →₀ ℕ) (_ : d ∈ s), {i | coeff α d (f i) ≠ 0} by
        exact ((finite_of_weight_le w hw n).biUnion fun d _ => hf d).subset h_ss
      · intro i hi
        simp only [mem_setOf_eq] at hi
        simp only [mem_setOf_eq, Nat.cast_id, Ne.def, mem_iUnion, mem_setOf_eq, exists_prop]
        have heq: (ENat.toNat (weightedOrder w (f i))) = weightedOrder w (f i) := by
          rw [ENat.coe_toNat_eq_self]
          exact ne_of_lt (lt_of_le_of_lt hi hn)
        obtain ⟨d, hd⟩ := exists_coeff_ne_zero_of_weightedOrder w (f i) heq
        refine' ⟨d, _, hd.2⟩
        simpa [← hd.1, WithTop.some_eq_coe, Nat.cast_le] using hi
#align mv_power_series.strongly_summable.weighted_order_tendsto_top_iff
  MvPowerSeries.StronglySummable.weightedOrder_tendsto_top_iff

/-- When σ is finite, a family of power series is strongly summable
  iff their orders tend to infinity. -/
theorem order_tendsto_top_iff [Finite σ] (f : ι → MvPowerSeries σ α) :
    StronglySummable f ↔ Tendsto (fun i => order (f i)) cofinite (nhds ⊤) :=
  weightedOrder_tendsto_top_iff (by simp) f
#align mv_power_series.strongly_summable.order_tendsto_top_iff
  MvPowerSeries.StronglySummable.order_tendsto_top_iff

end Order

-- NOTE (MI) : I had to add this
instance : LocallyFiniteOrderBot (σ →₀ ℕ) := sorry

/-- The union of the supports of the functions `λ i, coeff α e (f i)`, where `e` runs over
  the coefficients bounded by `d`. -/
noncomputable def unionOfSupportOfCoeffLe [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) : Finset ι :=
  Finset.biUnion (Iic d) fun e => (hf e).toFinset
#align mv_power_series.strongly_summable.union_of_support_of_coeff_le
  MvPowerSeries.StronglySummable.unionOfSupportOfCoeffLe

/-- A term `i : ι` does not belong to the union of the supports of the functions
  `λ i, coeff α e (f i)`, where `e` runs over the coefficients bounded by `d` if and only if
  `∀ e ≤ d, coeff α e (f i) = 0`. -/
theorem not_mem_unionOfSupportOfCoeffLe_iff [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) (i : ι) :
    i ∉ hf.unionOfSupportOfCoeffLe d ↔ ∀ (e) (_ : e ≤ d), coeff α e (f i) = 0 := by
  simp only [unionOfSupportOfCoeffLe, Finset.mem_biUnion, Finset.mem_Iic, Finite.mem_toFinset,
    mem_support, not_exists, ne_eq, not_and, not_not]
#align mv_power_series.strongly_summable.not_mem_union_of_support_of_coeff_le_iff
  MvPowerSeries.StronglySummable.not_mem_unionOfSupportOfCoeffLe_iff

/- lemma union_of_coeff_support_finite {f : ι → mv_power_series σ α}
  (hf : strongly_summable f) (d : σ →₀ ℕ) :
  (⋃ e (H : e ≤ d), (λ i, coeff α e (f i)).support).finite :=
(set.Iic d).to_finite.bUnion (λ d H, hf d) -/

-- TODO: ask
/-- If `f` is strongly summable, then the union of the supports of the functions
  `λ i, coeff α e (f i)`, where `e` runs over the coefficients bounded by `d`, contains
  finitely many finite sets. -/
theorem of_subset_unionOfSupportOfCoeffLe_finite [DecidableEq ι] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) (d : σ →₀ ℕ) :
    {I : Finset ι | I ⊆ hf.unionOfSupportOfCoeffLe d}.Finite := by
  suffices {I : Finset ι | I ⊆ hf.unionOfSupportOfCoeffLe  d} =
    (hf.unionOfSupportOfCoeffLe  d).powerset by
    rw [this]; apply finite_toSet
  ext I
  simp only [mem_setOf_eq, coe_powerset, Set.mem_preimage, mem_powerset_iff, Finset.coe_subset]
#align mv_power_series.strongly_summable.of_subset_union_of_coeff_support_finite
  MvPowerSeries.StronglySummable.of_subset_unionOfSupportOfCoeffLe_finite

/-- If `f` and `g` are strongly summable, then for all `d : σ →₀ ℕ`, the support of the function
  `λ i, coeff α d ((f + g) i)` is contained in the union of the supports of `λ i, coeff α d (f i)`
  and `λ i, coeff α d (g i)`-/
theorem support_add [DecidableEq ι] {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (hg : StronglySummable g) :
    ∀ d : σ →₀ ℕ, (fun i => coeff α d ((f + g) i)).support ⊆
      ((hf d).toFinset ∪ (hg d).toFinset : Finset ι) := by
  intro d i
  simp only [Pi.add_apply, map_add, Function.mem_support, Ne.def, coe_union, Finite.coe_toFinset,
    Set.mem_union]
  intro h
  by_cases h₁ : coeff α d (f i) = 0
  · right; simpa [h₁] using h
  · left; exact h₁
#align mv_power_series.strongly_summable.support_add MvPowerSeries.StronglySummable.support_add

/-- If `f` and `g` are strongly summable, then so is `f + g`.  -/
theorem add {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable (f + g) := by
  classical exact fun d => Finite.subset (finite_toSet _) (support_add hf hg d)
#align mv_power_series.strongly_summable.add MvPowerSeries.StronglySummable.add

/-- If `f` is strongly summable, then for every `a : ι → α`, `a • f` is strongly summable. -/
theorem smul {f : ι → MvPowerSeries σ α} (a : ι → α) (hf : StronglySummable f) :
    StronglySummable (a • f) := by
  intro d
  apply Finite.subset (hf d)
  intro i
  simp only [Pi.smul_apply', Pi.smul_apply, Function.mem_support, Ne.def]
  intro h h'
  apply h
  rw [coeff_smul, h', MulZeroClass.mul_zero]
#align mv_power_series.strongly_summable.smul MvPowerSeries.StronglySummable.smul

/-- If `f` and `g` are strongly summable, then for all `d : σ →₀ ℕ`, the support of the function
  `λ i, coeff α d (f i.fst * g i.snd)` is contained in the finite set
  `d.antidiagonal.biUnion fun b => (hf b.fst).toFinset).product
          (d.antidiagonal.biUnion fun b => (hg b.snd).toFinset)`. -/
theorem support_mul [DecidableEq ι] [DecidableEq σ] {f : ι → MvPowerSeries σ α} {κ : Type _}
    [DecidableEq κ] {g : κ → MvPowerSeries σ α} (hf : StronglySummable f)
    (hg : StronglySummable g) :
    ∀ d : σ →₀ ℕ,
      (fun i : ι × κ => coeff α d (f i.fst * g i.snd)).support ⊆
        (d.antidiagonal.biUnion fun b => (hf b.fst).toFinset).product
          (d.antidiagonal.biUnion fun b => (hg b.snd).toFinset) := by
  rintro d ⟨i, j⟩ h
  dsimp only [Function.mem_support, coeff_mul] at h
  suffices ∃ p ∈ d.antidiagonal, coeff α (p.fst : σ →₀ ℕ) (f i) * (coeff α p.snd) (g j) ≠ 0 by
    obtain ⟨⟨b, c⟩, hbc, h'⟩ := this
    simp only [Finsupp.mem_antidiagonal] at hbc
    erw [Finset.mem_product]
    simp only [Finset.mem_biUnion, Finsupp.mem_antidiagonal, Finite.mem_toFinset, mem_support,
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
    convert h'
#align mv_power_series.strongly_summable.support_mul MvPowerSeries.StronglySummable.support_mul

/-- If `f` and `g` are strongly summable, then `λ i, coeff α d (f i.fst * g i.snd)` is strongly
  summable. -/
theorem mul {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable fun i : ι × κ => f i.fst * g i.snd := by
  classical exact fun d => Finite.subset (finite_toSet _) (support_mul hf hg d)
#align mv_power_series.strongly_summable.mul MvPowerSeries.StronglySummable.mul

/-- The sum of a strongly summable family of power series. -/
noncomputable def sum {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) : MvPowerSeries σ α :=
  fun d => (hf d).toFinset.sum fun i => coeff α d (f i)
#align mv_power_series.strongly_summable.sum MvPowerSeries.StronglySummable.sum

theorem coeff_sum_def {f : ι → MvPowerSeries σ α} {hf : StronglySummable f} (d : σ →₀ ℕ) :
    coeff α d hf.sum = (hf d).toFinset.sum fun i => coeff α d (f i) :=
  rfl
#align mv_power_series.strongly_summable.coeff_sum.def MvPowerSeries.StronglySummable.coeff_sum_def

/-- If `f` is strongly summable, then for any `d : σ →₀ ℕ)` and any finite set `s` containing the
  support of `λ i, coeff α d (f i)`, the coefficient `coeff α d hf.sum` is equal to the sum
  of the coefficients `coeff α d (f i)`, where `i` runs over `s`. -/
theorem coeff_sum {f : ι → MvPowerSeries σ α} {hf : StronglySummable f} (d : σ →₀ ℕ) {s : Finset ι}
    (hs : (fun i => coeff α d (f i)).support ⊆ s) :
    coeff α d hf.sum = s.sum fun i => coeff α d (f i) := by
  rw [coeff_sum_def, sum_subset (Finite.toFinset_subset.mpr hs)]
  intro i _ hi'
  simpa only [Finite.mem_toFinset, Function.mem_support, Classical.not_not] using hi'
#align mv_power_series.strongly_summable.coeff_sum MvPowerSeries.StronglySummable.coeff_sum

/-- If `f` and `g` are strongly summable and equal, then their sums agree. -/
theorem sum_congr {f g : ι → MvPowerSeries σ α} {hf : StronglySummable f} {hg : StronglySummable g}
    (h : f = g) : hf.sum = hg.sum := by
  ext d
  simp only [coeff_sum_def]
  refine' Finset.sum_congr _ fun i _ => by rw [h]
  ext i
  simp only [Finite.mem_toFinset, mem_support, Ne.def, h]
#align mv_power_series.strongly_summable.sum_congr MvPowerSeries.StronglySummable.sum_congr

--ADDED
/-- If `f` and `g` are strongly summable, then the sum of `f + g` is equal to the sum of `f`
  plus the sum of `g`. -/
theorem sum_add {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g) :
  (add hf hg).sum = hf.sum + hg.sum := by
  classical
  ext d
  simp only [coeff_sum, Pi.add_apply, map_add]
  rw [coeff_sum d (support_add hf hg d), coeff_sum d, coeff_sum d]
  simp only [Pi.add_apply, map_add, Finset.union_assoc]
  rw [sum_add_distrib]
  all_goals
    simp only [coe_union, Finite.coe_toFinset, Set.subset_union_right, Set.subset_union_left]

--TODO: remove?
theorem sum_add' {f g : ι → MvPowerSeries σ α} (hf : StronglySummable f) (hg : StronglySummable g)
    (hh : StronglySummable (f + g)) : hh.sum = hf.sum + hg.sum := by
  classical
  ext d
  simp only [coeff_sum, Pi.add_apply, map_add]
  rw [coeff_sum d (support_add hf hg d), coeff_sum d, coeff_sum d]
  simp only [Pi.add_apply, map_add, Finset.union_assoc]
  rw [sum_add_distrib]
  all_goals
    simp only [coe_union, Finite.coe_toFinset, Set.subset_union_right, Set.subset_union_left]
#align mv_power_series.strongly_summable.sum_add MvPowerSeries.StronglySummable.sum_add'

/-- If `f` and `g` are strongly summable, then the sum of `λ i, coeff α d (f i.fst * g i.snd)`
  is equal to the sum of `f` times the sum of `g`. -/
theorem sum_mul {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    (mul hf hg).sum = hf.sum * hg.sum := by
  classical
  ext d
  simp_rw [coeff_sum d (support_mul hf hg d), coeff_mul]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro bc hbc
  rw [coeff_sum bc.fst, coeff_sum bc.snd, sum_mul_sum]
  rfl
  all_goals
    intro x hx
    apply @Finset.subset_biUnion_of_mem _ _ _ _ _ bc hbc
    exact (Finite.mem_toFinset _).mpr hx

--TODO: remove?
theorem sum_mul' {f : ι → MvPowerSeries σ α} {κ : Type _} {g : κ → MvPowerSeries σ α}
    (hf : StronglySummable f) (hg : StronglySummable g)
    (hh : StronglySummable fun i : ι × κ => f i.fst * g i.snd) : hh.sum = hf.sum * hg.sum := by
  classical
  ext d
  simp_rw [coeff_sum d (support_mul hf hg d), coeff_mul]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro bc hbc
  rw [coeff_sum bc.fst, coeff_sum bc.snd, sum_mul_sum]
  rfl
  all_goals
    intro x hx
    apply @Finset.subset_biUnion_of_mem _ _ _ _ _ bc hbc
    exact (Finite.mem_toFinset _).mpr hx
#align mv_power_series.strongly_summable.sum_mul MvPowerSeries.StronglySummable.sum_mul'

/-- If `f` is strongly summable and `s : Set ι` is any set, then `λ i, s.indicator f i` is
  strongly summable.-/
theorem of_indicator {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    StronglySummable fun i => s.indicator f i := by
  intro d
  apply (hf d).subset
  intro i
  simp only [mem_support, Ne.def, not_imp_not]
  intro hi
  cases' s.indicator_eq_zero_or_self f i with h h <;>
  . simp only [h, hi, map_zero]
#align mv_power_series.strongly_summable.of_indicator
  MvPowerSeries.StronglySummable.of_indicator

/-- If `f` is strongly summable and `s : Set ι` is any set, then the sum of `f` equals the sum of
  `f` over `s` plus the sum of `f` over the complement of `s`. -/
theorem add_compl {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    hf.sum = (hf.of_indicator s).sum + (hf.of_indicator (sᶜ)).sum := by
  rw [← sum_add (hf.of_indicator s) (hf.of_indicator (sᶜ))]
  exact sum_congr (s.indicator_self_add_compl f).symm
#align mv_power_series.strongly_summable.add_compl MvPowerSeries.StronglySummable.add_compl

/-- If `f` is strongly summable and `s : Set ι` is any set, then
  `f ∘ (↑) : ↥s → MvPowerSeries σ α` is strongly summable. -/
theorem on_subtype {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) (s : Set ι) :
    StronglySummable (f ∘ (↑) : ↥s → MvPowerSeries σ α) := by
  intro d
  apply Finite.of_finite_image _ (injOn_of_injective Subtype.coe_injective _)
  apply (hf d).subset
  rintro i ⟨j, hj, rfl⟩
  simp only [comp_apply, mem_support, Ne.def] at hj ⊢
  exact hj
#align mv_power_series.strongly_summable.on_subtype MvPowerSeries.StronglySummable.on_subtype

/-- If `f` is strongly summable and `d : σ →₀ ℕ`, then the infinite sum of
  `λ i, coeff α d (f i)` is equal to `coeff α d hf.sum`. -/
theorem hasSum_coeff [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (d : σ →₀ ℕ) : HasSum (fun i => coeff α d (f i)) (coeff α d hf.sum) := by
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  rw [Finite.mem_toFinset, Function.mem_support, Classical.not_not] at hb
  exact hb
#align mv_power_series.strongly_summable.has_sum_coeff
  MvPowerSeries.StronglySummable.hasSum_coeff

/-- If `f` is strongly summable and `d : σ →₀ ℕ`, then `λ i, coeff α d (f i)` is summable. -/
theorem summable_coeff [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f)
    (d : σ →₀ ℕ) : Summable fun i => coeff α d (f i) :=
  ⟨coeff α d hf.sum, hf.hasSum_coeff d⟩
#align mv_power_series.strongly_summable.summable_coeff
  MvPowerSeries.StronglySummable.summable_coeff

end StronglySummable

/-- Given `w : σ → ℕ` and `f : MvPowerSeries σ α`, the family `λ p, homogeneousComponent w p f`
  is strongly summable. -/
theorem homogeneous_components_self_stronglySummable (w : σ → ℕ) (f : MvPowerSeries σ α) :
    StronglySummable fun p => homogeneousComponent w p f := by
  intro d
  apply (finite_toSet {weight w d}).subset
  intro p
  rw [Function.mem_support, Ne.def, mem_coe, coeff_homogeneousComponent, Finset.mem_singleton,
    ite_eq_right_iff, not_forall, exists_prop, and_imp]
  intro h _
  exact h.symm
#align mv_power_series.homogeneous_components_self_strongly_summable
  MvPowerSeries.homogeneous_components_self_stronglySummable

/-- Given `w : σ → ℕ` and `f : MvPowerSeries σ α`, then `f` is equal to the sum of its
  homogeneous components. -/
theorem as_sum_of_homogeneous_components (w : σ → ℕ) (f : MvPowerSeries σ α) :
    f = (homogeneous_components_self_stronglySummable w f).sum := by
  ext d
  simp_rw [coeff_apply, StronglySummable.sum, coeff_homogeneousComponent]
  rw [sum_eq_single (weight w d)]
  · simp only [eq_self_iff_true, if_true]
    rfl
  · intro b _ h'
    rw [if_neg (Ne.symm h')]
  · simp only [Finite.mem_toFinset, Function.mem_support, Classical.not_not, imp_self]

-- TODO: remove?
theorem as_sum_of_homogeneous_components' (w : σ → ℕ) (f : MvPowerSeries σ α) :
    ∀ hf : StronglySummable fun p => homogeneousComponent w p f, f = hf.sum := by
  intro hf
  ext d
  simp_rw [coeff_apply, StronglySummable.sum, coeff_homogeneousComponent]
  rw [sum_eq_single (weight w d)]
  · simp only [eq_self_iff_true, if_true]
    rfl
  · intro b _ h'
    rw [if_neg (Ne.symm h')]
  · simp only [Finite.mem_toFinset, Function.mem_support, Classical.not_not, imp_self]
#align mv_power_series.as_sum_of_homogeneous_components
  MvPowerSeries.as_sum_of_homogeneous_components'

end Semiring

end StronglySummable

section StronglyMultipliable

variable [CommRing α] {ι : Type _} (f : ι → MvPowerSeries σ α)

/-- The map sending `(I : finset ι)` to the finite product `I.prod (λ i, f i)`. -/
noncomputable def partialProduct : Finset ι → MvPowerSeries σ α := fun I => I.prod fun i => f i
#align mv_power_series.partial_product MvPowerSeries.partialProduct

/-- If `f` is strongly summable, the support of `λ I, coeff α d (partialProduct f I)` is contained
  in the powerset of `hf.unionOfSupportOfCoeffLe d`. -/
theorem support_partialProduct_subset [DecidableEq ι] [DecidableEq σ]
    (hf : StronglySummable f) (d : σ →₀ ℕ) :
    (support fun I => coeff α d (partialProduct f I)) ⊆
      (hf.unionOfSupportOfCoeffLe d).powerset := by
  intro I
  simp only [mem_support, Ne.def, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset, not_imp_comm, Finset.not_subset]
  rintro ⟨i, hi, h⟩
  rw [StronglySummable.not_mem_unionOfSupportOfCoeffLe_iff] at h
  simp only [partialProduct, prod_eq_mul_prod_diff_singleton hi, coeff_mul]
  apply sum_eq_zero
  rintro ⟨x, y⟩
  rw [Finsupp.mem_antidiagonal]
  intro hxy
  rw [h x _, MulZeroClass.zero_mul]
  simp only [← hxy, Finsupp.le_def, Finsupp.coe_add, Pi.add_apply, le_self_add]
#align mv_power_series.strongly_summable.support_partial_product_le
  MvPowerSeries.support_partialProduct_subset



/- TODO : give a more general (and easier) definition
 A family `f` is strongly multipliable if for each `d`,
 the coefficients `coeff α d (s.prod f)` of the finite products are eventually constant
 and rewrite the case of sums in the same spirit
 But beware of subfamilies when `∃ i, f i = 0` -/
/-- The family `f` is strongly multipliable if the family `F` on `{ I : Set ι | I.Finite}`
  formed by all finite products `I.prod (λ i, f i)` is strongly_summable -/
def StronglyMultipliable : Prop :=
  StronglySummable (partialProduct f)
#align mv_power_series.strongly_multipliable MvPowerSeries.StronglyMultipliable

variable {f}

namespace StronglyMultipliable

/-- The product of the family of `(1 + f ι)`, when `f` is strongly_multipliable  -/
noncomputable def prod (hf : StronglyMultipliable f) : MvPowerSeries σ α :=
  hf.sum
#align mv_power_series.strongly_multipliable.prod MvPowerSeries.StronglyMultipliable.prod

/-- If `f` is strongly_multipliable, the product of the family of `(1 + f ι)` is equal to the
  sum of `partialProduct f`.   -/
theorem prod_eq (hf : StronglyMultipliable f) : hf.prod = hf.sum :=
  rfl
#align mv_power_series.strongly_multipliable.prod_eq MvPowerSeries.StronglyMultipliable.prod_eq

end StronglyMultipliable
namespace StronglySummable

--NOTE: renamed so that we can use dot notation
/-- If `f = Σ f i` is strongly summable, then `Π (1 + f i)` is strongly multipliable -/
theorem toStronglyMultipliable (hf : StronglySummable f) :
    StronglyMultipliable f := by
  classical
  exact fun d => Finite.subset (finite_toSet _) (support_partialProduct_subset f hf d)
#align mv_power_series.strongly_summable.to_strongly_multipliable
  MvPowerSeries.StronglySummable.toStronglyMultipliable

end StronglySummable
namespace StronglyMultipliable

/-- If `f` is strongly_multipliable and `s : Finset ι`, the product of `λ i, (1 + f ι)` over `s`
  is equal to the sum of `hf.of_indicator {I : Finset ι | I ⊆ s}`.   -/
theorem finset_prod_eq (s : Finset ι) (hf : StronglyMultipliable f) :
    (s.prod fun i => 1 + f i) = (hf.of_indicator {I : Finset ι | I ⊆ s}).sum := by
  rw [Finset.prod_one_add']
  ext d
  rw [map_sum, StronglySummable.coeff_sum d]
  · apply sum_congr rfl
    intro t ht
    apply congr_arg
    rw [indicator, if_pos]; rfl
    · exact Finset.mem_powerset.mp ht
  · intro t
    rw [mem_support, Ne.def, mem_coe, Finset.mem_powerset, not_imp_comm]
    intro ht'
    rw [indicator, if_neg, map_zero]
    exact ht'
#align mv_power_series.strongly_multipliable.finset_prod_eq
  MvPowerSeries.StronglyMultipliable.finset_prod_eq

/-- If `f` is strongly_multipliable and `s : Set ι`, the product of the family `(1 + f ι)`
  is equal to the sum `(hf.of_indicator {I : Finset ι | ↑I ⊆ s}).sum +
      (hf.of_indicator ({I : Finset ι | ↑I ⊆ s}ᶜ)).sum`.   -/
theorem prod_eq_sum_add_sum (hf : StronglyMultipliable f) (s : Set ι) :
    hf.prod = (hf.of_indicator {I : Finset ι | ↑I ⊆ s}).sum +
      (hf.of_indicator ({I : Finset ι | ↑I ⊆ s}ᶜ)).sum :=
  by rw [hf.prod_eq, ← hf.add_compl]
#align mv_power_series.strongly_multipliable.prod_eq_sum_add_sum
  MvPowerSeries.StronglyMultipliable.prod_eq_sum_add_sum

/-- A version of `prod_eq_sum_add_sum` for `s : Finset ι`. -/
theorem prod_eq_finset_prod_add (hf : StronglyMultipliable f) (s : Finset ι) :
    hf.prod = (s.prod fun i => 1 + f i) + (hf.of_indicator ({I : Finset ι | I ⊆ s}ᶜ)).sum := by
  rw [hf.prod_eq_sum_add_sum s, hf.finset_prod_eq s]
#align mv_power_series.strongly_multipliable.prod_eq_finset_prod_add
  MvPowerSeries.StronglyMultipliable.prod_eq_finset_prod_add

/-- If `f` is strongly summable, `d : σ →₀ ℕ`, and `J` is a finite set containing
  `hf.unionOfSupportOfCoeffLe d`, then the `d`th coefficients of the product of the strongly
  multipliable family `1 + f i` agrees with the one of `J.prod fun i => 1 + f i`. -/
theorem coeff_prod_apply_eq_finset_prod [DecidableEq ι] [DecidableEq σ]
    (hf : StronglySummable f) {d : σ →₀ ℕ} {J : Finset ι} (hJ : hf.unionOfSupportOfCoeffLe d ⊆ J) :
    (coeff α d) hf.toStronglyMultipliable.prod = (coeff α d) (J.prod fun i => 1 + f i) := by
  rw [hf.toStronglyMultipliable.prod_eq_finset_prod_add J, map_add, add_right_eq_self,
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
    rw [Finsupp.mem_antidiagonal] at hxy
    rw [(hf.not_mem_unionOfSupportOfCoeffLe_iff d i).mp (fun hi => hiJ (hJ hi)) x _,
      MulZeroClass.zero_mul]
    simp only [← hxy, Finsupp.le_def, Finsupp.coe_add, Pi.add_apply, le_self_add]

end StronglyMultipliable

end StronglyMultipliable

end MvPowerSeries
