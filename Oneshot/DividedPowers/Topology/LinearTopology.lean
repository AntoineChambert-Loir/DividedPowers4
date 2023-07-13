import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.Topology.Algebra.Nonarchimedean.Bases

section Complements

theorem topologicalSpace_eq_iff_nhds_eq {α : Type _} (τ τ' : TopologicalSpace α) :
    τ = τ' ↔ ∀ (a : α) (s : Set α) (has : a ∈ s), s ∈ @nhds α τ a ↔ s ∈ @nhds α τ' a :=
  by
  constructor
  · intro h a s has; rw [h]
  intro h; ext s
  simp only [isOpen_iff_mem_nhds]
  apply forall_congr'; intro a
  apply imp_congr_right; exact h a s
#align topological_space_eq_iff_nhds_eq topologicalSpace_eq_iff_nhds_eq

theorem topologicalSpace_le_iff_nhds_le {α : Type _} (τ τ' : TopologicalSpace α) :
    τ ≤ τ' ↔ ∀ (a : α) (s : Set α) (has : a ∈ s), s ∈ @nhds α τ' a → s ∈ @nhds α τ a :=
  by
  rw [TopologicalSpace.le_def]
  constructor
  · intro h a s has
    simp only [mem_nhds_iff]
    apply Exists.imp; intro t
    apply Exists.imp; intro ht
    rintro ⟨ht_open, h'⟩; exact ⟨h t ht_open, h'⟩
  intro h
  intro s
  simp only [isOpen_iff_mem_nhds]
  intro hs a has
  exact h a s has (hs a has)
#align topological_space_le_iff_nhds_le topologicalSpace_le_iff_nhds_le

theorem mem_nhds_add_iff {α : Type _} [AddGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
    (V : Set α) (a b : α) : V ∈ nhds (a + b) ↔ Add.add a ⁻¹' V ∈ nhds b :=
  by
  constructor
  exact fun hV => (continuous_add_left a).ContinuousAt hV
  · intro hV
    suffices : V = Add.add (-a) ⁻¹' (Add.add a ⁻¹' V)
    rw [this]
    apply (continuous_add_left (-a)).ContinuousAt
    simp only [neg_add_cancel_left]
    exact hV
    rw [Set.preimage_preimage]
    simp only [add_neg_cancel_left, Set.preimage_id']
#align mem_nhds_add_iff mem_nhds_add_iff

end Complements

/-- A family of ideals of a ring `α` is an `ideals_basis` if the ideals 
  are both left- and right-ideals, 
  and if every intersection of two of them contains another one. -/
structure IdealsBasis {α : Type _} [Ring α] {ι : Type _} (B : ι → Ideal α) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  mul_right : ∀ i a r, a ∈ B i → a * r ∈ B i
#align ideals_basis IdealsBasis

namespace IdealsBasis

variable {α : Type _} [Ring α]

/-- An `ideals_basis` on a `comm_ring` -/
def ofComm {α : Type _} [CommRing α] {ι : Type _} {B : ι → Ideal α}
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) : IdealsBasis B :=
  { inter
    mul_right := fun i a r h => by rw [mul_comm]; refine' Ideal.mul_mem_left (B i) r h }
#align ideals_basis.of_comm IdealsBasis.ofComm

/- def to_submodules_ring_basis {α  : Type*} [comm_ring α] {ι : Type*} {B : ι → ideal α} (hB : ideals_basis B) :
  submodules_ring_basis B := sorry 
 -/
def to_ringSubgroupsBasis {ι : Type _} {B : ι → Ideal α} (hB : IdealsBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup
    where
  inter := hB.inter
  mul i :=
    ⟨i, fun u => by
      rintro ⟨x, y, hx, hy, rfl⟩
      apply Ideal.mul_mem_left; exact hy⟩
  leftMul a i :=
    ⟨i, by
      intro x hx; rw [Set.mem_preimage]
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe] at hx ⊢
      apply Ideal.mul_mem_left; exact hx⟩
  rightMul a i :=
    ⟨i, by
      intro y hy; rw [Set.mem_preimage]
      apply hB.mul_right; exact hy⟩
#align ideals_basis.to_ring_subgroups_basis IdealsBasis.to_ringSubgroupsBasis

def toRingFilterBasis {ι : Type _} [Nonempty ι] {B : ι → Ideal α} (hB : IdealsBasis B) :
    RingFilterBasis α :=
  hB.toRing_subgroups_basis.toRingFilterBasis
#align ideals_basis.to_ring_filter_basis IdealsBasis.toRingFilterBasis

def topology {ι : Type _} {B : ι → Ideal α} [Nonempty ι] (hB : IdealsBasis B) :
    TopologicalSpace α :=
  (toRingFilterBasis hB).topology
#align ideals_basis.topology IdealsBasis.topology

theorem to_topologicalRing {ι : Type _} {B : ι → Ideal α} [Nonempty ι] (hB : IdealsBasis B) :
    @TopologicalRing α hB.topology _ :=
  hB.toRingFilterBasis.isTopologicalRing
#align ideals_basis.to_topological_ring IdealsBasis.to_topologicalRing

/-  Junk

structure linear_topological_ring (α : Type*)[comm_ring α] [topological_space α] : Prop :=
(to_has_ideal_basis : has_submodules_basis α α)


def has_ring_subgroups_basis 
  (α : Type*) [comm_ring α] [H : topological_space α] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → add_subgroup α) (hB : ring_subgroups_basis B), 
by exactI H = ring_subgroups_basis.topology hB
 

def has_submodules_basis 
  (α : Type*) [comm_ring α] [topological_space α] 
  (M : Type*) [add_comm_group M] [module α M] [H : topological_space M] : Prop :=
∃ (ι : Type*) [nonempty ι] (B : ι → submodule α M) (hB : submodules_basis B), 
by exactI H = submodules_basis.topology hB

structure linear_topological_module 
  (α : Type*) [comm_ring α] [topological_space α] 
  (M : Type*) [add_comm_group M] [module α M] [H : topological_space M] : Prop := 
(to_has_submodules_basis : has_submodules_basis α M) -/
end IdealsBasis

/-  -- TODO : faire marcher ça !
section linear_topology


variables (α : Type *) [comm_ring α]

structure has_linear_topology  [τ : topological_space α] : Prop :=
(to_linear_topology : ∃ (ι : Type*) [nonempty ι] 
  (J : ι → ideal α) (hJ : ideals_basis J),  
  by exactI τ = hJ.to_ring_subgroups_basis.topology)

lemma has_linear_topology.to_topological_ring [τ : topological_space α] 
  (h : has_linear_topology α) : 
  topological_ring α := 
begin
  sorry
end

end linear_topology
 -/
