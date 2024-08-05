import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

section Complements

/- -- TODO: Do we need this?
  -- NO, this is more or less TopologicalSpace.ext_iff_nhds
theorem TopologicalSpace.eq_iff_nhds_eq {α : Type*} (τ τ' : TopologicalSpace α) :
    τ = τ' ↔ ∀ (s : Set α), ∀ a ∈ s, s ∈ @nhds α τ a ↔ s ∈ @nhds α τ' a := by
  constructor
  · intro h s a _; rw [h]
  intro h; ext s
  rw [@isOpen_iff_mem_nhds α s τ, @isOpen_iff_mem_nhds α s τ']
  apply forall_congr'; intro a
  apply imp_congr_right; exact h s a
#align topological_space_eq_iff_nhds_eq TopologicalSpace.eq_iff_nhds_eq
-/

/- -- ADDED.
  -- This is exactly TopologicalSpace.ext_iff_nhds
/-- Two topologies on `α` are equal if and only if their neighborhood filters agree. -/
theorem TopologicalSpace.eq_iff_nhds_eq_nhds {α : Type*} (τ τ' : TopologicalSpace α) :
    τ = τ' ↔ @nhds α τ = @nhds α τ'  := by
  constructor
  · intro h; rw [h]
  · intro h
    apply TopologicalSpace.ext_nhds
    simp only [h, implies_true]
-/

-- TODO: This is similar to `le_iff_nhds`, do we need this variant?
-- Probably not :
theorem TopologicalSpace.le_iff_nhds_le {α : Type*} (τ τ' : TopologicalSpace α) :
    τ ≤ τ' ↔ ∀ (s : Set α), ∀ a ∈ s, s ∈ @nhds α τ' a → s ∈ @nhds α τ a := by
  rw [le_iff_nhds]
  rw [forall_comm]
  apply forall_congr'
  intro a
  rw [Filter.le_def]
  apply forall_congr'
  intro s
  constructor
  · exact fun h _ ↦ h
  · intro h
    by_cases ha : a ∈ s
    · exact h ha
    · exact fun hs ↦ False.elim (ha (mem_of_mem_nhds hs))

/-   rw [TopologicalSpace.le_def]
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
-/

/-- If `a, b` are two elements of a topological group `α`, then a set `V` belongs to `nhds (a + b)`
  if and only if `Add.add a ⁻¹' V ∈ nhds b`.  -/
theorem mem_nhds_add_iff {α : Type*} [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
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

theorem TopologicalAddGroup.ext_iff_nhds_zero {α : Type*} [AddCommGroup α]
    (τ : TopologicalSpace α) [@TopologicalAddGroup α τ _]
    (τ' : TopologicalSpace α) [@TopologicalAddGroup α τ' _] :
    τ = τ' ↔ @nhds _ τ 0 = @nhds _ τ' 0 := by
  rw [TopologicalSpace.ext_iff_nhds]
  constructor
  · intro h
    exact h 0
  · intro h a
    ext s
    rw [← add_zero a]
    simp only [mem_nhds_add_iff, h]


end Complements

/-- `Ideal.IsBasis B` means the image of `B` is a filter basis consisting of left- and right-ideals. -/
structure Ideal.IsBasis {α : Type*} [Ring α] {ι : Sort*}
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

variable {α : Type*} [Ring α]

/-- The `IdealBasis` associated with an `Ideal.IsBasis` -/
def toIdealBasis {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B) : IdealBasis α where
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
def _root_.IdealBasis.toIsBasis (B : IdealBasis α) :
    Ideal.IsBasis (ι := B.sets) (fun x => (x : Ideal α)) where
  nonempty := Set.nonempty_coe_sort.mpr B.nonempty
  inter := fun s t ↦ by
    obtain ⟨u, hu, hu'⟩ := B.inter_sets s.prop t.prop
    use ⟨u, hu⟩
  mul_right := fun s {a} r has ↦ B.mul_right (Subtype.coe_prop s) has

/-- An `Ideal.IsBasis` on a `CommRing`. -/
lemma ofComm {α : Type*} [CommRing α] {ι : Type*} [Nonempty ι] {B : ι → Ideal α}
    (inter : ∀ (i j), ∃ k, B k ≤ B i ⊓ B j) : Ideal.IsBasis B :=
  { inter
    nonempty := inferInstance
    mul_right := fun i a r h => by
      rw [mul_comm]; refine' Ideal.mul_mem_left (B i) r h }

/-- An `Ideal.IsBasis` is a `RingSubgroupsBasis`. -/
lemma toRingSubgroupsBasis {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup where
  inter := hB.inter
  mul i := ⟨i, fun u => by
    rintro ⟨x, _, _, hy, rfl⟩
    exact Ideal.mul_mem_left _ _ hy⟩
  leftMul a i := ⟨i, fun x hx => Ideal.mul_mem_left _ _ hx⟩
  rightMul a i := ⟨i, fun y hy =>  hB.mul_right _ _ hy⟩

/-- An `Ideal.IsBasis` is a `RingFilterBasis`. -/
def toRingFilterBasis {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :=
  let _: Nonempty ι := hB.nonempty
  hB.toRingSubgroupsBasis.toRingFilterBasis
#align ideals_basis.to_ring_filter_basis Ideal.IsBasis.toRingFilterBasis

/-- The topology generated by an `Ideal.IsBasis`. -/
def topology {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
    TopologicalSpace α :=
  (toRingFilterBasis hB).topology

theorem mem_nhds_zero_iff {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B)
    (s : Set α) :
    (s ∈ @nhds _ hB.topology 0) ↔
    (∃ i, ((B i : Set α) ∈ @nhds _ hB.topology 0) ∧ (B i : Set α) ⊆ s) := by
  simp only [AddGroupFilterBasis.nhds_eq, AddGroupFilterBasis.N_zero,
    Filter.IsBasis.mem_filter_iff, FilterBasis.mem_filter_iff]
  constructor
  · rintro ⟨t, ⟨i, rfl⟩, hts⟩
    simp only [Submodule.coe_toAddSubgroup] at hts
    exact ⟨i, ⟨B i, ⟨i, rfl⟩, subset_of_eq rfl⟩, hts⟩
  · rintro ⟨i, _, his⟩
    use B i, ⟨i, rfl⟩, his

theorem ofIdealBasis_topology_eq {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
    (hB.toIdealBasis.toIsBasis).topology = hB.topology := by
  rw [TopologicalSpace.ext_iff_nhds]
  intro a
  simp [AddGroupFilterBasis.nhds_eq]
  simp only [AddGroupFilterBasis.N]
  apply congr_arg₂ _ rfl
  -- Now we have to prove that both filter bases (sets vs families) coincide
  ext s
  simp only [FilterBasis.mem_filter_iff]
  constructor
  · rintro ⟨u, ⟨⟨v, ⟨i, rfl⟩⟩, rfl⟩, hus⟩
    simp only [Submodule.coe_toAddSubgroup] at hus
    exact ⟨B i, ⟨i, rfl⟩, hus⟩
  · rintro ⟨u, ⟨i, rfl⟩, hus⟩
    simp only [Submodule.coe_toAddSubgroup] at hus
    refine ⟨B i, ⟨⟨B i, ⟨i, rfl⟩⟩, rfl⟩, hus⟩

/-- A ring `α` with the topology generated by an `Ideal.IsBasis` is a topological ring. -/
theorem to_topologicalRing {ι : Type*} {B : ι → Ideal α} (hB : Ideal.IsBasis B) :
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




namespace IdealBasis

variable {α : Type*} [Ring α]

theorem mem_nhds_zero_iff (B : IdealBasis α)
    (s : Set α) :
    (s ∈ @nhds _ B.toIsBasis.topology 0) ↔
    ∃ i ∈ B.sets, (i : Set α) ∈ @nhds _ B.toIsBasis.topology 0 ∧ i ≤ s := by
  rw [Ideal.IsBasis.mem_nhds_zero_iff]
  simp only [Subtype.exists, exists_and_left, exists_prop, Set.le_eq_subset]
  constructor
  · rintro ⟨a, mem_nhds, mem_sets, subset_s⟩
    exact ⟨a, mem_sets, mem_nhds, subset_s⟩
  · rintro ⟨i, hi, mem_nhds, subset_s⟩
    exact ⟨i, mem_nhds, hi, subset_s⟩

/-- The `IdealBasis` of a commutative ring from an adequate set of ideals -/
def ofComm {α : Type*} [CommRing α] (B : Set (Ideal α))
    (nonempty : Set.Nonempty B)
    (inter : ∀ {i j}, i ∈ B → j ∈ B → ∃ k ∈ B, k ≤ i ⊓ j) :
    IdealBasis α where
  sets := B
  inter_sets := inter
  nonempty := nonempty
  mul_right {i} {a b} _ ha := by
    rw [mul_comm]
    exact Ideal.mul_mem_left i b ha

/-
/-- An `IdealBasis` is a `RingFilterBasis` -/
def toRingFilterBasis (B : IdealBasis α) : RingFilterBasis α where
  sets := (fun (i : Ideal α) ↦ (i : Set α)) '' B.sets
  nonempty := by simp ; exact B.nonempty
  inter_sets {s t} hs ht := sorry
  zero' := sorry
  add' := sorry
  neg' := sorry
  conj' := sorry
  mul' := sorry
  mul_left' := sorry
  mul_right' := sorry

-/
end IdealBasis

universe u

section LinearTopology

variable (α : Type u) [Ring α]

class LinearTopology [τ : TopologicalSpace α]
    extends IdealBasis α where
  isTopology :  τ = toIdealBasis.toIsBasis.topology

example [TopologicalSpace α] [hLT : LinearTopology α] :
  TopologicalRing α  :=
  hLT.isTopology ▸ Ideal.IsBasis.to_topologicalRing hLT.toIdealBasis.toIsBasis

namespace LinearTopology

theorem mem_nhds_zero_iff [TopologicalSpace α] [hL : LinearTopology α]
    (s : Set α) :
    (s ∈ nhds 0) ↔
    ∃ i ∈ hL.sets, (i : Set α) ∈ nhds 0 ∧ i ≤ s := by
  rw [TopologicalSpace.ext_iff_nhds.mp hL.isTopology,
    hL.toIdealBasis.mem_nhds_zero_iff]

theorem tendsto_zero_mul [TopologicalSpace α] [LinearTopology α]
    {ι : Type*} {f : Filter ι} (a b : ι → α)
    (hb : Filter.Tendsto b f (nhds 0)) :
    Filter.Tendsto (a * b) f (nhds 0) := by
  intro v hv
  rw [LinearTopology.mem_nhds_zero_iff] at hv
  obtain ⟨I, _, I_mem, I_le⟩ := hv
  simp only [Set.le_eq_subset] at I_le
  apply Filter.sets_of_superset _ _ I_le
  simp only [Filter.mem_sets, Filter.mem_map]
  rw [Filter.tendsto_def] at hb
  specialize hb _ I_mem
  apply Filter.sets_of_superset _ hb
  intro x
  simp only [Set.mem_preimage, Pi.mul_apply, SetLike.mem_coe]
  intro hx
  apply Ideal.mul_mem_left _ _ hx

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
