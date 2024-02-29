import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

section Complements

-- TODO: Do we need this?
theorem TopologicalSpace.eq_iff_nhds_eq {α : Type _} (τ τ' : TopologicalSpace α) :
    τ = τ' ↔ ∀ (s : Set α), ∀ a ∈ s, s ∈ @nhds α τ a ↔ s ∈ @nhds α τ' a := by
  constructor
  · intro h s a _; rw [h]
  intro h; ext s
  rw [@isOpen_iff_mem_nhds α s τ, @isOpen_iff_mem_nhds α s τ']
  apply forall_congr'; intro a
  apply imp_congr_right; exact h s a
#align topological_space_eq_iff_nhds_eq TopologicalSpace.eq_iff_nhds_eq

-- ADDED
/-- Two topologies on `α` are equal if and only if their neighborhood filters agree. -/
theorem TopologicalSpace.eq_iff_nhds_eq_nhds {α : Type _} (τ τ' : TopologicalSpace α) :
    τ = τ' ↔ @nhds α τ = @nhds α τ'  := by
  constructor
  · intro h; rw [h]
  · intro h
    apply eq_of_nhds_eq_nhds
    simp only [h, implies_true]

-- TODO: This is similar to `le_iff_nhds`, do we need this variant?
theorem TopologicalSpace.le_iff_nhds_le {α : Type _} (τ τ' : TopologicalSpace α) :
    τ ≤ τ' ↔ ∀ (s : Set α), ∀ a ∈ s, s ∈ @nhds α τ' a → s ∈ @nhds α τ a := by
  rw [TopologicalSpace.le_def]
  constructor
  · intro h s a _
    simp only [@mem_nhds_iff α a s τ, @mem_nhds_iff α a s τ']
    apply Exists.imp; intro t
    apply And.imp_right
    simp only [and_imp]
    intro ht_open h'
    exact ⟨h t ht_open, h'⟩
  · intro h
    intro s
    simp only [@isOpen_iff_mem_nhds α s τ, @isOpen_iff_mem_nhds α s τ']
    intro hs a has
    exact h s a has (hs a has)
#align topological_space_le_iff_nhds_le TopologicalSpace.le_iff_nhds_le

/-- If `a, b` are two elements of a topological group `α`, then a set `V` belongs to `nhds (a + b)`
  if and only if `Add.add a ⁻¹' V ∈ nhds b`.  -/
theorem mem_nhds_add_iff {α : Type _} [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
    (V : Set α) (a b : α) : V ∈ nhds (a + b) ↔ Add.add a ⁻¹' V ∈ nhds b := by
  constructor
  . exact fun hV => ContinuousAt.preimage_mem_nhds (continuous_add_left a).continuousAt hV
  · intro hV
    suffices h : V = Add.add (-a) ⁻¹' (Add.add a ⁻¹' V) by
      rw [h]
      apply ContinuousAt.preimage_mem_nhds (continuous_add_left (-a)).continuousAt
      convert hV
      apply neg_add_cancel_left
    rw [Set.preimage_preimage, eq_comm]
    convert Set.preimage_id'
    apply add_neg_cancel_left a
#align mem_nhds_add_iff mem_nhds_add_iff

end Complements

/-- `Ideal.IsBasis B` means the image of `B` is a filter basis consisting of left- and right-ideals. -/
structure Ideal.IsBasis {α : Type _} [Ring α] {ι : Sort*}
  (B : ι → Ideal α) : Prop where
  /-- There is an `i : ι` -/
  nonempty : Nonempty ι
  /-- Every intersection of ideals in `B` contains an ideal in `B`. -/
  inter : ∀ (i j : ι), ∃ (k : ι), B k ≤ B i ⊓ B j
  /-- Every ideal in `B` is a right ideal. -/
  mul_right : ∀ i {a} r, a ∈ B i → a * r ∈ B i
#align ideals_basis Ideal.IsBasis

/-- `IdealBasis B` means `B` is a filter basis of left- and right-ideals -/
structure IdealBasis (α : Type*) [Ring α] where
  /-- Sets of a filter basis. -/
  sets : Set (Ideal α)
  /-- The set of filter basis sets is nonempty. -/
  nonempty : sets.Nonempty
  /-- The set of filter basis sets is directed downwards. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ≤ x ⊓ y
  /-- Ideals in sets are right ideals -/
  mul_right {x} {a b : α}: x ∈ sets → a ∈ x → a * b ∈ x

namespace Ideal.IsBasis

variable {α : Type _} [Ring α]

/-- The `IdealBasis` associated with an `Ideal.IsBasis` -/
def toIdealBasis {ι : Type _} {B : ι → Ideal α} (hB : Ideal.IsBasis B) : IdealBasis α where
  sets := Set.range B
  nonempty := Set.range_nonempty (h := hB.nonempty) _
  inter_sets {x y} := by
    rintro ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hB.inter i j
    exact ⟨B k,  Exists.intro k rfl, hk⟩
  mul_right {x a b} hx ha := by
    obtain ⟨i, rfl⟩ := hx
    exact hB.mul_right i b ha

/-- An `Ideal.IsBasis` associated with an `IdealBasis` -/
def ofIdealBasis (B : IdealBasis α) : Ideal.IsBasis (ι := B.sets) (fun x => (x : Ideal α)) where
  nonempty := Set.nonempty_coe_sort.mpr B.nonempty
  inter := sorry
  mul_right := sorry


/-- An `Ideal.IsBasis` on a `CommRing`. -/
lemma ofComm {α : Type _} [CommRing α] {ι : Type _} [Nonempty ι] {B : ι → Ideal α}
    (inter : ∀ (i j), ∃ k, B k ≤ B i ⊓ B j) : Ideal.IsBasis B :=
  { inter
    nonempty := inferInstance
    mul_right := fun i a r h => by rw [mul_comm]; refine' Ideal.mul_mem_left (B i) r h }

/-- An `Ideal.IsBasis` is a `RingSubgroupsBasis`. -/
lemma toRingSubgroupsBasis {ι : Type _} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup where
  inter := hB.inter
  mul i := ⟨i, fun u => by
    rintro ⟨x, _, _, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul a i := ⟨i, fun x hx => Ideal.mul_mem_left _ _ hx⟩
  rightMul a i := ⟨i, fun y hy =>  hB.mul_right _ _ hy⟩

/-- An `Ideal.IsBasis` is a `RingFilterBasis`. -/
def toRingFilterBasis {ι : Type _} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :=
  let _: Nonempty ι := hB.nonempty
  hB.toRingSubgroupsBasis.toRingFilterBasis
#align ideals_basis.to_ring_filter_basis Ideal.IsBasis.toRingFilterBasis

/-- The topology generated by an `Ideal.IsBasis`. -/
def topology {ι : Type _} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
    TopologicalSpace α :=
  (toRingFilterBasis hB).topology

/-- A ring `α` with the topology generated by an `Ideal.IsBasis` is a topological ring. -/
theorem to_topologicalRing {ι : Type _} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
    @TopologicalRing α hB.topology _ :=
  hB.toRingFilterBasis.isTopologicalRing
#align ideals_basis.to_topological_ring Ideal.IsBasis.to_topologicalRing

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
end Ideal.IsBasis

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

section LinearTopology

variable (α : Type*) [CommRing α]

class LinearTopology (α : Type u) [CommRing α] [τ : TopologicalSpace α]
    extends IdealBasis α   where
  isTopology :=  τ = (Ideal.IsBasis.ofIdealBasis toIdealBasis).topology

/-
class IsLinearTopology (α : Type u) [CommRing α] [τ : TopologicalSpace α]
  (ι : Type*) [Nonempty ι]  : Prop where
  toLinearTopology : ∃ (J : ι → Ideal α) (hJ : IdealBasis J),
    τ = hJ.toRingSubgroupsBasis.topology

lemma IsLinearTopology.toTopologicalRing [τ : TopologicalSpace α] (ι : Type*) [Nonempty ι]
  (h : IsLinearTopology α ι) : TopologicalRing α := by
  obtain ⟨_, hJ, _⟩ := h
  convert hJ.to_topologicalRing
-/

end LinearTopology
