
import DividedPowers.ForMathlib.Topology.LinearTopology
import DividedPowers.ForMathlib.MvPowerSeries.Topology

--import Mathlib.Control.Ulift

open Set SetLike

variable (σ : Type _)

namespace MvPowerSeries

section Ideals

variable (α : Type _) [CommRing α]

set_option linter.uppercaseLean3 false

def basis : (σ →₀ ℕ) → Ideal (MvPowerSeries σ α) := fun d =>
  { carrier := {f | ∀ e ≤ d, coeff α e f = 0}
    zero_mem' := fun e _ => by rw [coeff_zero]
    add_mem' := fun hf hg e he => by
      rw [map_add, hf e he, hg e he, add_zero]
    smul_mem' := fun f g hg e he => by
      rw [smul_eq_mul, coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero (coeff α uv.fst f)
      exact hg  _ (le_trans (le_iff_exists_add'.mpr 
        ⟨uv.fst, (Finsupp.mem_antidiagonal.mp huv).symm⟩) he) }
#align mv_power_series.J MvPowerSeries.basis

theorem mem_basis (f : MvPowerSeries σ α) (d : σ →₀ ℕ) : 
    f ∈ basis σ α d ↔ ∀ e ≤ d, coeff α e f = 0 := by
  simp only [basis, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq]
#align mv_power_series.mem_J MvPowerSeries.mem_basis

theorem basis_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis σ α d ≤ basis σ α e := 
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))
#align mv_power_series.J_le MvPowerSeries.basis_le

theorem basis_le_iff [Nontrivial α] (d e : σ →₀ ℕ) : basis σ α d ≤ basis σ α e ↔ e ≤ d := by
  refine' ⟨_, basis_le _ _⟩
  simp only [basis, Submodule.mk_le_mk, AddSubmonoid.mk_le_mk, setOf_subset_setOf]
  intro h
  rw [← inf_eq_right]
  apply le_antisymm
  . exact inf_le_right 
  . by_contra h'
    specialize h (monomial α e 1) _
    . intro e' he'
      apply coeff_monomial_ne
      intro hee'
      rw [hee'] at he'
      apply h'
      exact le_inf_iff.mpr ⟨he', le_rfl⟩ 
    apply one_ne_zero' α
    convert h e le_rfl
    rw [coeff_monomial_same] 
#align mv_power_series.J_le_iff MvPowerSeries.basis_le_iff

theorem basis_antitone : Antitone (basis σ α) := fun _ _ h => basis_le σ α h
#align mv_power_series.J_antitone MvPowerSeries.basis_antitone

theorem idealsBasis : IdealsBasis (basis σ α) :=
  IdealsBasis.ofComm fun d e => by use d ⊔ e; apply Antitone.map_sup_le (basis_antitone σ α)
#align mv_power_series.ideals_basis MvPowerSeries.idealsBasis

theorem toRingSubgroupsBasis : RingSubgroupsBasis fun d => (basis σ α d).toAddSubgroup :=
  (idealsBasis σ α).toRingSubgroupsBasis
#align mv_power_series.to_ring_subgroups_basis MvPowerSeries.toRingSubgroupsBasis

end Ideals

section DiscreteTopology

set_option linter.uppercaseLean3 false

variable (α : Type _) [CommRing α] [TopologicalSpace α]

theorem basis_mem_nhds_zero [DiscreteTopology α] (d : σ →₀ ℕ) :
    ↑(basis σ α d) ∈ nhds (0 : MvPowerSeries σ α) := by
  classical
  rw [nhds_pi, Filter.mem_pi]
  use Finset.Iic d, Finset.finite_toSet _, (fun e => if e ≤ d then {0} else univ)
  constructor
  · intro e
    simp only
    split_ifs with h
    . simp only [nhds_discrete, Filter.mem_pure, mem_singleton_iff]
      rfl
    . simp only [Filter.univ_mem]
  · intro f
    simp only [Finset.coe_Iic, mem_pi, mem_Iic, mem_ite_univ_right, mem_singleton_iff, mem_coe]
    exact forall_imp (fun e h he => h he he)
#align mv_power_series.J_mem_nhds_zero MvPowerSeries.basis_mem_nhds_zero


theorem topology_eq_ideals_basis_topolgy [DiscreteTopology α] :
    MvPowerSeries.topologicalSpace σ α = (toRingSubgroupsBasis σ α).topology := by
  let τ := MvPowerSeries.topologicalSpace σ α
  let τ' := (toRingSubgroupsBasis σ α).topology
  change τ = τ'
  rw [topologicalSpace_eq_iff_nhds_eq]
  suffices ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0 by
    let tr := topologicalRing σ α
    let tg := @TopologicalRing.to_topologicalAddGroup _ _ τ ( topologicalRing σ α)
    intro s a ha 
    rw [← add_zero a, @mem_nhds_add_iff _ _ τ tg, mem_nhds_add_iff]
    apply this
  intro s
  rw [(RingSubgroupsBasis.hasBasis_nhds (toRingSubgroupsBasis σ α) 0).mem_iff]
  simp only [sub_zero, Submodule.mem_toAddSubgroup, exists_true_left, true_and]
  refine' ⟨_, fun ⟨d, hd⟩ => (@nhds _ τ 0).sets_of_superset (basis_mem_nhds_zero σ α d) hd⟩
  rw [nhds_pi, Filter.mem_pi]
  rintro ⟨D, hD, t, ht, ht'⟩
  use Finset.sup hD.toFinset id
  apply subset_trans _ ht'
  intro f hf e he
  rw [← coeff_eq_apply f e, hf e]
  exact mem_of_mem_nhds (ht e)
  . have he' : e ∈ (Finite.toFinset hD) := by
      simp only [id.def, Finite.mem_toFinset]
      exact he
    apply Finset.le_sup he'
#align mv_power_series.topology_eq_ideals_basis_topolgy MvPowerSeries.topology_eq_ideals_basis_topolgy

/- -- TODO : problèmes d'univers

lemma to_has_linear_topology [discrete_topology α] : 
  has_linear_topology (mv_power_series σ α) := 
begin
  unfold has_linear_topology,
  sorry,
  refine ⟨σ →₀ ℕ, _,  _, _, _⟩,
  -- basis σ α, ideals_basis σ α,  topology_eq_ideals_basis_topolgy σ α ⟩,
  simp only [nonempty_of_inhabited],
  let h:= ulift.map (basis σ α),
  refine function.comp _ h,
  
end -/
/- 

lemma to_submodules_basis [discrete_topology α] : submodules_basis (basis σ α) := submodules_basis.mk 
  (λ d e, by {
    use d + e, rw le_inf_iff, 
    split,
    apply basis_antitone, rw le_iff_exists_add, exact ⟨e, rfl⟩, 
    apply basis_antitone, rw le_iff_exists_add', exact ⟨d, rfl⟩, })
  (λ f d, by { rw filter.eventually_iff_exists_mem, 
    use ↑(basis σ α d), apply and.intro (basis_mem_nhds_zero σ α d),
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
    change f ∈ basis σ α _ at hf, 
    rw ← coeff_eq_apply f e, rw hf e, 
    exact mem_of_mem_nhds (ht e), 
    convert finset.le_sup _,
    simp only [id.def], 
    simp only [set.finite.mem_to_finset], exact he, },
  { rintro ⟨d, hd⟩,
    exact (nhds 0).sets_of_superset (basis_mem_nhds_zero σ α d) hd,}  
end
 -/
end DiscreteTopology

end MvPowerSeries

