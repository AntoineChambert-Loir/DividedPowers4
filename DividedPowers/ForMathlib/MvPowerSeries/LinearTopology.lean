
import DividedPowers.ForMathlib.Topology.LinearTopology
import DividedPowers.ForMathlib.MvPowerSeries.Topology

import Mathlib.Control.Ulift

variable (σ : Type _)

namespace MvPowerSeries

section Ideals

variable (α : Type _) [CommRing α]

def j : (σ →₀ ℕ) → Ideal (MvPowerSeries σ α) := fun d =>
  { carrier := {f | ∀ e ≤ d, coeff α e f = 0}
    zero_mem' := by rw [Set.mem_setOf]; intro e he; rw [coeff_zero]
    add_mem' := fun f g hf hg => by
      rw [Set.mem_setOf] at hf hg ⊢
      intro e he; rw [map_add, hf e he, hg e he, add_zero]
    smul_mem' := fun f g hg => by
      rw [Set.mem_setOf] at hg ⊢
      intro e he; rw [smul_eq_mul, coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero _
      apply hg
      apply le_trans _ he
      rw [Finsupp.mem_antidiagonal] at huv 
      rw [le_iff_exists_add']; exact ⟨uv.fst, huv.symm⟩ }
#align mv_power_series.J MvPowerSeries.j

theorem mem_j (f : MvPowerSeries σ α) (d : σ →₀ ℕ) : f ∈ j σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by
  simp only [J, Submodule.mem_mk, Set.mem_setOf_eq]
#align mv_power_series.mem_J MvPowerSeries.mem_j

theorem j_le {e d : σ →₀ ℕ} (hed : e ≤ d) : j σ α d ≤ j σ α e :=
  by
  intro f
  simp only [mem_J]
  refine' forall_imp _
  intro a h ha; exact h (le_trans ha hed)
#align mv_power_series.J_le MvPowerSeries.j_le

theorem j_le_iff [Nontrivial α] (d e : σ →₀ ℕ) : j σ α d ≤ j σ α e ↔ e ≤ d :=
  by
  constructor
  · simp only [J, Submodule.mk_le_mk, Set.setOf_subset_setOf]
    intro h
    rw [← inf_eq_right]
    apply le_antisymm; exact inf_le_right
    by_contra h'
    specialize h (monomial α e 1) _
    intro e' he'; rw [coeff_monomial_ne]; intro hee'
    apply h'
    rw [le_inf_iff]; apply And.intro _ le_rfl
    simpa [hee'] using he'
    apply one_ne_zero' α
    convert h e le_rfl; rw [coeff_monomial_same]
  apply J_le
#align mv_power_series.J_le_iff MvPowerSeries.j_le_iff

theorem j_antitone : Antitone (j σ α) := fun d e h => j_le σ α h
#align mv_power_series.J_antitone MvPowerSeries.j_antitone

theorem idealsBasis : IdealsBasis (j σ α) :=
  IdealsBasis.ofComm fun d e => by use d ⊔ e; apply Antitone.map_sup_le (J_antitone σ α)
#align mv_power_series.ideals_basis MvPowerSeries.idealsBasis

theorem toRing_subgroups_basis : RingSubgroupsBasis fun d => (j σ α d).toAddSubgroup :=
  (idealsBasis σ α).toRing_subgroups_basis
#align mv_power_series.to_ring_subgroups_basis MvPowerSeries.toRing_subgroups_basis

end Ideals

section DiscreteTopology

variable (α : Type _) [CommRing α] [TopologicalSpace α]

theorem j_mem_nhds_zero [DiscreteTopology α] (d : σ →₀ ℕ) :
    ↑(j σ α d) ∈ nhds (0 : MvPowerSeries σ α) := by
  classical
  rw [nhds_pi]
  rw [Filter.mem_pi]
  use Finset.Iic d
  constructor
  apply Finset.finite_toSet
  let t : (σ →₀ ℕ) → Set α := fun e => ite (e ≤ d) {0} Set.univ
  use t
  constructor
  · intro e; simp only [t]
    split_ifs with h
    simp only [Pi.zero_apply, nhds_discrete, Filter.pure_zero, Filter.mem_zero, Set.mem_singleton]
    simp only [Filter.univ_mem]
  · intro f
    simp only [mem_J, Finset.coe_Iio, Set.mem_pi, Set.mem_Iio, Set.mem_ite_univ_right,
      Set.mem_singleton_iff, SetLike.mem_coe]
    refine' forall_imp _
    simp only [Finset.coe_Iic, Set.mem_Iic]; intro e h
    intro he; exact h he he
#align mv_power_series.J_mem_nhds_zero MvPowerSeries.j_mem_nhds_zero

theorem topology_eq_ideals_basis_topolgy [DiscreteTopology α] :
    MvPowerSeries.topologicalSpace σ α = (toRing_subgroups_basis σ α).topology :=
  by
  let τ := MvPowerSeries.topologicalSpace σ α
  let τ' := (to_ring_subgroups_basis σ α).topology
  change τ = τ'
  rw [topologicalSpace_eq_iff_nhds_eq]
  suffices ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0
    by
    -- mv nhds from 0 to a
    intro a s ha
    rw [← add_zero a]
    haveI := TopologicalRing σ α; rw [mem_nhds_add_iff]
    rw [mem_nhds_add_iff]
    apply this
  -- neighborhoods of 0
  intro s
  rw [(RingSubgroupsBasis.hasBasis_nhds (to_ring_subgroups_basis σ α) 0).mem_iff]
  simp only [sub_zero, Submodule.mem_toAddSubgroup, exists_true_left]
  constructor
  · rw [nhds_pi]; rw [Filter.mem_pi]
    rintro ⟨D, hD, t, ht, ht'⟩
    use Finset.sup hD.to_finset id
    apply subset_trans _ ht'
    intro f hf
    rw [Set.mem_pi]; intro e he
    change f ∈ J σ α _ at hf 
    rw [← coeff_eq_apply f e]; rw [hf e]
    exact mem_of_mem_nhds (ht e)
    convert Finset.le_sup _
    simp only [id.def]
    simp only [Set.Finite.mem_toFinset]; exact he
  · rintro ⟨d, hd⟩
    exact (nhds 0).sets_of_superset (J_mem_nhds_zero σ α d) hd
#align mv_power_series.topology_eq_ideals_basis_topolgy MvPowerSeries.topology_eq_ideals_basis_topolgy

/- -- TODO : problèmes d'univers

lemma to_has_linear_topology [discrete_topology α] : 
  has_linear_topology (mv_power_series σ α) := 
begin
  unfold has_linear_topology,
  sorry,
  refine ⟨σ →₀ ℕ, _,  _, _, _⟩,
  -- J σ α, ideals_basis σ α,  topology_eq_ideals_basis_topolgy σ α ⟩,
  simp only [nonempty_of_inhabited],
  let h:= ulift.map (J σ α),
  refine function.comp _ h,
  
end -/
/- 

lemma to_submodules_basis [discrete_topology α] : submodules_basis (J σ α) := submodules_basis.mk 
  (λ d e, by {
    use d + e, rw le_inf_iff, 
    split,
    apply J_antitone, rw le_iff_exists_add, exact ⟨e, rfl⟩, 
    apply J_antitone, rw le_iff_exists_add', exact ⟨d, rfl⟩, })
  (λ f d, by { rw filter.eventually_iff_exists_mem, 
    use ↑(J σ α d), apply and.intro (J_mem_nhds_zero σ α d),
    intros g hg, 
    rw [smul_eq_mul, mul_comm], 
    refine ideal.mul_mem_left _ f _, 
    simpa only [set_like.mem_coe] using hg, } )

lemma has_submodules_basis_topology [discrete_topology α] : mv_power_series.topological_space σ α = (to_submodules_basis σ α).topology := 
begin
  let τ := mv_power_series.topological_space σ α,
  let τ' := (to_submodules_basis σ α).topology, 
  suffices : τ = τ', exact this,
  rw topological_space_eq_iff_nhds_eq, 
  suffices : ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0,
  -- mv nhds from 0 to a
  { intros a s ha, 
    rw ← add_zero a, 
    haveI := (topological_ring σ α), rw mem_nhds_add_iff,
    rw mem_nhds_add_iff, 
    apply this, },
  -- neighborhoods of 0
  intro s,
  rw (ring_subgroups_basis.has_basis_nhds (to_ring_subgroups_basis σ α) 0).mem_iff,
  simp only [sub_zero, submodule.mem_to_add_subgroup, exists_true_left],
  split,
  { rw nhds_pi, rw filter.mem_pi,
    rintro ⟨D, hD, t, ht, ht'⟩,
    use finset.sup hD.to_finset id,
    apply subset_trans _ ht', 
    intros f hf, 
    rw set.mem_pi, intros e he, 
    change f ∈ J σ α _ at hf, 
    rw ← coeff_eq_apply f e, rw hf e, 
    exact mem_of_mem_nhds (ht e), 
    convert finset.le_sup _,
    simp only [id.def], 
    simp only [set.finite.mem_to_finset], exact he, },
  { rintro ⟨d, hd⟩,
    exact (nhds 0).sets_of_superset (J_mem_nhds_zero σ α d) hd,}  
end
 -/
end DiscreteTopology

end MvPowerSeries

