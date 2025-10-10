import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.StronglySummable.Basic
import Mathlib.RingTheory.MvPowerSeries.PiTopology

open MvPowerSeries.WithPiTopology MvPowerSeries.WithPiTopology
namespace MvPowerSeries

open Function

variable {σ α : Type*} --[DecidableEq σ]

namespace StronglySummable

variable {ι : Type*}

section Semiring

variable [Semiring α]

theorem hasSum [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) :
    HasSum f hf.sum :=
  Pi.hasSum.mpr hf.hasSum_coeff

theorem summable [TopologicalSpace α] {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) :
    Summable f :=
  ⟨hf.sum, hf.hasSum⟩

theorem sum_eq_tsum [TopologicalSpace α] [T2Space α] {f : ι → MvPowerSeries σ α}
    (hf : StronglySummable f) : hf.sum = tsum f := by
  ext d
  rw [tsum_def, dif_pos hf.summable]
  apply HasSum.unique (hf.hasSum_coeff d)
  apply HasSum.map
  . split_ifs with h
    . simp only [SummationFilter.support_eq_univ, Set.indicator_univ]
      convert hf.summable.hasSum
      rw [tsum_eq_finsum]
      sorry
    . (expose_names; exact h_1) --exact (Classical.choose_spec hf.summable)
    · sorry
  . exact continuous_coeff α d

end Semiring

section Ring

variable [Ring α]

/-
# Comparisons of the various convergences on `mv_power_series σ α`

Ref. : Bourbaki, *Algèbre*, IV, §4, n°2, Lemme 1.

* pour toute topologie :
support fini => sommable : `strongly_summable.summable`
sommable => tend vers 0  : `tendsto_zero_of_summable`

* pour topologie discrète :
tend vers 0 => support fini : `summable.tendsto_cofinite_zero`
-/
example [TopologicalSpace α] {f : ι → MvPowerSeries σ α} : StronglySummable f → Summable f :=
  StronglySummable.summable

-- TODO (?): replace topological_ring instance by topological_add_group…
example [TopologicalSpace α] [IsTopologicalRing α] {f : ι → MvPowerSeries σ α} :
    Summable f → Filter.Tendsto f Filter.cofinite (nhds 0) :=
  haveI := instIsTopologicalRing σ α
  tendsto_zero_of_summable

theorem iff_summable [TopologicalSpace α] [DiscreteTopology α] {f : ι → MvPowerSeries σ α} :
    StronglySummable f ↔ Summable f :=
  ⟨summable, fun hf d => finite_support_of_summable (hf.map _ (continuous_coeff α d))⟩

theorem iff_summable' [TopologicalSpace α] [DiscreteTopology α] {f : ι → MvPowerSeries σ α} :
    StronglySummable f ↔ Filter.Tendsto f Filter.cofinite (nhds 0) := by
  haveI := instIsTopologicalRing σ α
  refine' ⟨fun hf => hf.summable.tendsto_cofinite_zero, _⟩
  rw [StronglySummable, nhds_pi, Filter.tendsto_pi]
  exact forall_imp fun d => finite_support_of_tendsto_zero

end Ring

end StronglySummable

section Summable

variable [Semiring α] [TopologicalSpace α]

/-- A family of power series is summable if their weighted orders tend to infinity. -/
theorem summable_of_weightedOrder_tendsto_top {ι : Type*} (w : σ → ℕ) (f : ι → MvPowerSeries σ α)
    (hf : Filter.Tendsto (fun i => weightedOrder w (f i)) Filter.cofinite (nhds ⊤)) : Summable f :=
  (StronglySummable.of_weightedOrder_tendsto_top w f hf).summable

theorem summable_of_order_tendsto_top {ι : Type*} (f : ι → MvPowerSeries σ α)
    (hf : Filter.Tendsto (fun i => order (f i)) Filter.cofinite (nhds ⊤)) : Summable f :=
  (StronglySummable.of_order_tendsto_top f hf).summable

end Summable

section StronglyMultipliable

variable {ι : Type*} {f : ι → MvPowerSeries σ α} [CommRing α]
namespace StronglySummable

variable [UniformSpace α] [IsUniformAddGroup α]

--#check MvPowerSeries.StronglyMultipliable.coeff_prod_apply_eq_finset_prod

theorem hasProd_of_one_add (hf : StronglySummable f) :
    HasProd (fun i => 1 + f i) hf.toStronglyMultipliable.prod := by
  classical
  haveI := instIsUniformAddGroup (σ := σ) (R := α)
  intro V hV
  simp only [Filter.mem_map]
  let V₀ := Add.add hf.toStronglyMultipliable.prod ⁻¹' V
  have hV'₀ : V = Add.add (-hf.toStronglyMultipliable.prod) ⁻¹' V₀ := by
    rw [← Set.preimage_comp, eq_comm]
    convert Set.preimage_id
    rw [funext_iff]
    intro f
    simp only [comp_apply, id_eq]
    change _ + (_ + f) = f
    simp_rw [← add_assoc, add_neg_cancel, zero_add]
  have hV₀ : V₀ ∈ nhds (0 : MvPowerSeries σ α) := by
    apply continuousAt_def.mp (Continuous.continuousAt (continuous_add_left _))
    rw [add_zero]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at hV₀
  obtain ⟨D, hD, t, ht, htV₀⟩ := hV₀
  simp only [SummationFilter.unconditional_filter, Filter.mem_atTop_sets, ge_iff_le,
    Finset.le_eq_subset, Set.mem_preimage]
  use hf.unionOfSupportOfCoeffLe (hD.toFinset.sup id)
  intro J hIJ
  rw [hV'₀, Set.mem_preimage]
  apply htV₀
  intro d hd
  convert mem_of_mem_nhds (ht d) using 1
  change (-_ + _) = 0
  rw [neg_add_eq_sub, sub_eq_zero]
  symm
  apply StronglyMultipliable.coeff_prod_apply_eq_finset_prod hf (J := J)
  · intro i hi
    apply hIJ
    revert hi
    contrapose
    simp only [StronglySummable.not_mem_unionOfSupportOfCoeffLe_iff]
    intro h e hed
    refine' h e (le_trans hed _)
    apply Finset.le_sup ((Set.Finite.mem_toFinset hD).mpr hd)

theorem multipliable_of_one_add {ι : Type*} (f : ι → MvPowerSeries σ α) (hf : StronglySummable f) :
    Multipliable fun i => 1 + f i := by classical exact hf.hasProd_of_one_add.multipliable

variable [T2Space α]

theorem tprod_eq_of_one_add {ι : Type*} {f : ι → MvPowerSeries σ α} (hf : StronglySummable f) :
    (tprod fun i => 1 + f i) = tsum (partialProduct f) := by
  haveI : T2Space (MvPowerSeries σ α) := instT2Space
  rw [hf.hasProd_of_one_add.tprod_eq, StronglyMultipliable.prod_eq, sum_eq_tsum]

end StronglySummable

-- TODO : treat the case of arbitrary topologies on α
/-
  but the statement is incorrect because `tsum F` has already used
  the given topology of `α`.
  Except for this problem, this runs roughly as follows:

  let h := @has_prod_of_one_add σ α _ (default) ι _ f hf,

  have := @has_prod.tprod_eq (mv_power_series σ α) ι _
    (@mv_power_series.topological_space σ α default)
    (@mv_power_series.t2_space σ α default (@discrete_topology.to_t2_space α default
      (discrete_topology_bot α))),

  exact this h,

-/
end StronglyMultipliable

end MvPowerSeries
