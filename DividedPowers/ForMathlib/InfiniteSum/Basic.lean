/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module infinite_sum.basic
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Logic.Encodable.Lattice
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.Algebra.Star

/-!
# Infinite product/sum over a topological monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations.
For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute convergence.

Note: There are multipliable sequences which are not unconditionally convergent!
The other way holds generally, see `has_prod.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

noncomputable section

open Classical Filter Finset Function

open scoped BigOperators Classical Topology

variable {α α': Type u_1} {β : Type _} {γ : Type _} {δ : Type _}


section HasProd

variable [TopologicalSpace α] [CommMonoid α] [TopologicalSpace α'] [AddCommMonoid α']

/-- Infinite products on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type.
So we sum up bigger and bigger sets. This sum operation is invariant under reordering.
In particular, the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid.
We only add this assumption later, for the lemmas where it is relevant.
-/
@[to_additive "Infinite sums on a topological monoid"]
def HasProd (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β => ∏ b in s, f b) atTop (𝓝 a)
#align has_prod HasProd
#align has_sum HasSum

/-- `multipliable f` means that `f` has some (infinite) product.
Use `tprod` to get the value. -/
@[to_additive Summable
      "multipliable f` means that `f` has some (infinite) sum.\nUse `tsum` to get the value."]
def Multipliable (f : β → α) : Prop :=
  ∃ a, HasProd f a
#align multipliable Multipliable
#align summable Summable

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise. -/
irreducible_def tsum {β} (f : β → α') :=
  if h : Summable f then
  /- Note that the sum might not be uniquely defined if the topology is not separated.
  When the support of `f` is finite, we make the most reasonable choice to use the finite sum over
  the support. Otherwise, we choose arbitrarily an `a` satisfying `HasSum f a`. -/
    if (support f).Finite then finsum f
    else Classical.choose h
  else 0
#align tsum tsum

/-- `∏' i, f i` is the product of `f` it exists, or 1 otherwise -/
@[to_additive existing tsum]
irreducible_def tprod {β} (f : β → α):=
  if h : Multipliable f then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the support of `f` is finite, we make the most reasonable choice to use the finite product
  over the support. Otherwise, we choose arbitrarily an `a` satisfying `HasProd f a`. -/
    if (mulSupport f).Finite then finprod f
    else Classical.choose h
  else 1
#align tprod tprod

notation3"∏' "-- see Note [operator precedence of big operators]
(...)", "r:67:(scoped f => tprod f) => r

notation3"∑' "(...)", "r:67:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

@[to_additive HasSum.summable]
theorem HasProd.multipliable (h : HasProd f a) : Multipliable f :=
  ⟨a, h⟩
#align has_prod.multipliable HasProd.multipliable
#align has_sum.summable HasSum.summable

/-- Constant one function has sum `1` -/
@[to_additive "Constant zero function has sum `0`"]
theorem hasProd_one : HasProd (fun _ => 1 : β → α) 1 := by simp [HasProd, tendsto_const_nhds]
#align has_prod_one hasProd_one
#align has_sum_zero hasSum_zero

@[to_additive]
theorem hasProd_empty [IsEmpty β] : HasProd f (1 : α) := by 
  convert @hasProd_one α β _ _ 
#align has_prod_empty hasProd_empty
#align has_sum_empty hasSum_empty

@[to_additive]
theorem multipliable_one : Multipliable (fun _ => 1 : β → α) :=
  hasProd_one.multipliable
#align multipliable_one multipliable_one
#align multipliable_zero multipliable_zero

@[to_additive summable_empty]
theorem multipliable_empty [IsEmpty β] : Multipliable f :=
  hasProd_empty.multipliable
#align multipliable_empty multipliable_empty
#align summable_empty summable_empty

theorem tsum_eq_zero_of_not_summable {f' : β → α'} (h : ¬Summable f') : 
  ∑' b, f' b = 0 := by simp [tsum, h]
#align tsum_eq_zero_of_not_summable tsum_eq_zero_of_not_summable

@[to_additive existing tsum_eq_zero_of_not_summable]
theorem tprod_eq_one_of_not_multipliable (h : ¬Multipliable f) : ∏' b, f b = 1 := by simp [tprod, h]
#align tprod_eq_one_of_not_multipliable tprod_eq_one_of_not_multipliable

@[to_additive summable_congr]
theorem multipliable_congr (hfg : ∀ b, f b = g b) : Multipliable f ↔ Multipliable g :=
  iff_of_eq (congr_arg Multipliable <| funext hfg)
#align multipliable_congr multipliable_congr
#align summable_congr summable_congr

@[to_additive]
theorem Multipliable.congr (hf : Multipliable f) (hfg : ∀ b, f b = g b) : Multipliable g :=
  (multipliable_congr hfg).mp hf
#align multipliable.congr Multipliable.congr
#align summable.congr Summable.congr

@[to_additive]
theorem HasProd.hasProd_of_prod_eq {g : γ → α}
    (h_eq :
      ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∏ x in u', g x = ∏ b in v', f b)
    (hf : HasProd g a) : HasProd f a :=
  le_trans (map_atTop_finset_prod_le_of_prod_eq h_eq) hf
#align has_prod.has_prod_of_prod_eq HasProd.hasProd_of_prod_eq
#align has_sum.has_sum_of_sum_eq HasSum.hasSum_of_sum_eq

@[to_additive]
theorem hasProd_iff_hasProd {g : γ → α}
    (h₁ :
      ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∏ x in u', g x = ∏ b in v', f b)
    (h₂ :
      ∀ v : Finset β,
        ∃ u : Finset γ, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ ∏ b in v', f b = ∏ x in u', g x) :
    HasProd f a ↔ HasProd g a :=
  ⟨HasProd.hasProd_of_prod_eq h₂, HasProd.hasProd_of_prod_eq h₁⟩
#align has_prod_iff_has_prod hasProd_iff_hasProd
#align has_sum_iff_has_sum hasSum_iff_hasSum

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » set.range[set.range] g) -/
@[to_additive]
theorem Function.Injective.hasProd_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 1) : HasProd (f ∘ g) a ↔ HasProd f a := by
  simp only [HasProd, Tendsto, comp_apply, hg.map_atTop_finset_prod_eq hf]
#align function.injective.has_prod_iff Function.Injective.hasProd_iff
#align function.injective.has_sum_iff Function.Injective.hasSum_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » set.range[set.range] g) -/
@[to_additive Function.Injective.summable_iff]
theorem Function.Injective.multipliable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ (x) (_ : x ∉ Set.range g), f x = 1) : Multipliable (f ∘ g) ↔ Multipliable f :=
  exists_congr fun _ => hg.hasProd_iff hf
#align function.injective.multipliable_iff Function.Injective.multipliable_iff
#align function.injective.summable_iff Function.Injective.summable_iff

@[to_additive (attr := simp)] 
theorem hasProd_extend_one {g : β → γ} (hg : Injective g) :
    HasProd (extend g f 1) a ↔ HasProd f a := by
  rw [← hg.hasProd_iff, extend_comp hg]
  exact extend_apply' _ _

@[to_additive (attr := simp) summable_extend_zero] 
theorem multipliable_extend_one {g : β → γ} (hg : Injective g) :
    Multipliable (extend g f 1) ↔ Multipliable f :=
  exists_congr fun _ => hasProd_extend_one hg

@[to_additive]
theorem hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f ⊆ s) :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd f a :=
  Subtype.coe_injective.hasProd_iff <| by simpa using mulSupport_subset_iff'.1 hf
#align has_prod_subtype_iff_of_mul_support_subset hasProd_subtype_iff_of_mulSupport_subset
#align has_sum_subtype_iff_of_support_subset hasSum_subtype_iff_of_support_subset

@[to_additive]
theorem hasProd_subtype_iff_mulIndicator {s : Set β} :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd (s.mulIndicator f) a := by
  rw [← Set.mulIndicator_range_comp, Subtype.range_coe,
    hasProd_subtype_iff_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]
#align has_prod_subtype_iff_mul_indicator hasProd_subtype_iff_mulIndicator
#align has_sum_subtype_iff_indicator hasSum_subtype_iff_indicator

@[to_additive]
theorem multipliable_subtype_iff_mulIndicator {s : Set β} :
    Multipliable (f ∘ (↑) : s → α) ↔ Multipliable (s.mulIndicator f) :=
  exists_congr fun _ => hasProd_subtype_iff_mulIndicator
#align multipliable_subtype_iff_mul_indicator multipliable_subtype_iff_mulIndicator
#align multipliable_subtype_iff_indicator multipliable_subtype_iff_indicator

@[to_additive, simp]
theorem hasProd_subtype_mulSupport : HasProd (f ∘ (↑) : mulSupport f → α) a ↔ HasProd f a :=
  hasProd_subtype_iff_of_mulSupport_subset <| Set.Subset.refl _
#align has_prod_subtype_mul_support hasProd_subtype_mulSupport
#align has_sum_subtype_support hasSum_subtype_support

@[to_additive]
theorem hasProd_fintype [Fintype β] (f : β → α) : HasProd f (∏ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
#align has_prod_fintype hasProd_fintype
#align has_sum_fintype hasSum_fintype

@[to_additive] --Q : is the additive version also protected?
protected theorem Finset.hasProd (s : Finset β) (f : β → α) :
    HasProd (f ∘ (↑) : (↑s : Set β) → α) (∏ b in s, f b) := by 
  rw [← prod_attach];
  exact hasProd_fintype _
#align finset.has_prod Finset.hasProd
#align finset.has_sum Finset.hasSum

@[to_additive Finset.summable] 
protected theorem Finset.multipliable (s : Finset β) (f : β → α) :
    Multipliable (f ∘ (↑) : (↑s : Set β) → α) :=
  (s.hasProd f).multipliable
#align finset.multipliable Finset.multipliable
#align finset.summable Finset.summable

@[to_additive Set.Finite.summable]
protected theorem Set.Finite.multipliable {s : Set β} (hs : s.Finite) (f : β → α) :
    Multipliable (f ∘ (↑) : s → α) := by
  convert hs.toFinset.multipliable f <;> simp only [hs.coe_toFinset]
#align set.finite.multipliable Set.Finite.multipliable
#align set.finite.summable Set.Finite.summable

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b «expr ∉ » s) -/
/-- If a function `f` vanishes outside of a finite set `s`, then it `has_prod` `∑ b in s, f b`. -/
@[to_additive
      "If a function `f` is 1 outside of a finite set `s`, then it `has_prod` `∏ b in s, f b`"]
theorem hasProd_prod_of_ne_finset_one (hf : ∀ (b) (_ : b ∉ s), f b = 1) :
    HasProd f (∏ b in s, f b) :=
  (hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f
#align has_prod_prod_of_ne_finset_one hasProd_prod_of_ne_finset_one
#align has_sum_sum_of_ne_finset_zero hasSum_sum_of_ne_finset_zero

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b «expr ∉ » s) -/
@[to_additive summable_of_ne_finset_zero]
theorem multipliable_of_ne_finset_one (hf : ∀ (b) (_ : b ∉ s), f b = 1) : Multipliable f :=
  (hasProd_prod_of_ne_finset_one hf).multipliable
#align multipliable_of_ne_finset_one multipliable_of_ne_finset_one
#align summable_of_ne_finset_zero summable_of_ne_finset_zero

@[to_additive summable_of_finite_support]
theorem multipliable_of_finite_mulSupport (h : (mulSupport f).Finite) : Multipliable f := by
  apply multipliable_of_ne_finset_one (s := h.toFinset); simp

theorem Summable.hasSum {f : β → α'} (ha : Summable f) : HasSum f (∑' d, f d) := by
  simp only [tsum_def, ha, dite_true]
  by_cases H : (support f).Finite
  · simp [H, hasSum_sum_of_ne_finset_zero, finsum_eq_sum]
  · simpa [H] using Classical.choose_spec ha
#align summable.has_sum Summable.hasSum

@[to_additive existing]
theorem Multipliable.hasProd (ha : Multipliable f) : HasProd f (∏' b, f b) := by
  --simp only [tprod_def, ha, dite_true]; exact choose_spec ha
  simp only [tprod_def, ha, dite_true]
  by_cases H : (mulSupport f).Finite
  · simp [H, hasProd_prod_of_ne_finset_one, finprod_eq_prod]
  · simpa [H] using Classical.choose_spec ha
#align multipliable.has_prod Multipliable.hasProd

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b' «expr ≠ » b) -/
@[to_additive]
theorem hasProd_mulSingle {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 1) :
    HasProd f (f b) :=
  suffices HasProd f (∏ b' in {b}, f b') by simpa using this
  hasProd_prod_of_ne_finset_one <| by simpa [hf]
#align has_prod_mul_single hasProd_mulSingle
#align has_sum_single hasSum_single

@[to_additive]
theorem hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    HasProd (fun b' => if b' = b then a else 1) a := by
  convert @hasProd_mulSingle α β _ _ _ b _
  · exact (if_pos rfl).symm
  intro b' hb'
  exact if_neg hb'
#align has_prod_ite_eq hasProd_ite_eq
#align has_sum_ite_eq hasSum_ite_eq

@[to_additive]
theorem hasProd_pi_mulSingle [DecidableEq β] (b : β) (a : α) : HasProd (Pi.mulSingle b a) a := by
  convert hasProd_ite_eq b a
  simp [Pi.mulSingle_apply]
#align has_prod_pi_mul_single hasProd_pi_mulSingle
#align has_sum_pi_single hasSum_pi_single

@[to_additive]
theorem Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ HasProd f a :=
  e.injective.hasProd_iff <| by simp
#align equiv.has_prod_iff Equiv.hasProd_iff
#align equiv.has_sum_iff Equiv.hasSum_iff

@[to_additive]
theorem Function.Injective.hasProd_range_iff {g : γ → β} (hg : Injective g) :
    HasProd (fun x : Set.range g => f x) a ↔ HasProd (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasProd_iff.symm
#align function.injective.has_prod_range_iff Function.Injective.hasProd_range_iff
#align function.injective.has_sum_range_iff Function.Injective.hasSum_range_iff

@[to_additive Equiv.summable_iff]
theorem Equiv.multipliable_iff (e : γ ≃ β) : Multipliable (f ∘ e) ↔ Multipliable f :=
  exists_congr fun _ => e.hasProd_iff
#align equiv.multipliable_iff Equiv.multipliable_iff
#align equiv.summable_iff Equiv.summable_iff

@[to_additive]
theorem Multipliable.prod_symm {f : β × γ → α} (hf : Multipliable f) :
    Multipliable fun p : γ × β => f p.swap :=
  (Equiv.prodComm γ β).multipliable_iff.2 hf
#align multipliable.prod_symm Multipliable.prod_symm
#align summable.sum_symm Summable.sum_symm

@[to_additive]
theorem Equiv.hasProd_iff_of_mulSupport {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x : mulSupport f, g (e x) = f x) : HasProd f a ↔ HasProd g a :=
  by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasProd_subtype_mulSupport, ← this, e.hasProd_iff, hasProd_subtype_mulSupport]
#align equiv.has_prod_iff_of_mul_support Equiv.hasProd_iff_of_mulSupport
#align equiv.has_sum_iff_of_support Equiv.hasSum_iff_of_support

@[to_additive]
theorem hasProd_iff_hasProd_of_ne_one_bij {g : γ → α} (i : mulSupport g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : mulSupport f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasProd f a ↔ HasProd g a :=
  Iff.symm <|
    Equiv.hasProd_iff_of_mulSupport
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun _ _ h => Subtype.ext <| hi <| Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun _ hx => Subtype.ext hx⟩)
      hfg
#align has_prod_iff_has_prod_of_ne_one_bij hasProd_iff_hasProd_of_ne_one_bij
#align has_sum_iff_has_sum_of_ne_zero_bij hasSum_iff_hasSum_of_ne_zero_bij

@[to_additive]
theorem Equiv.multipliable_iff_of_mulSupport {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x : mulSupport f, g (e x) = f x) : Multipliable f ↔ Multipliable g :=
  exists_congr fun _ => e.hasProd_iff_of_mulSupport he
#align equiv.multipliable_iff_of_mul_support Equiv.multipliable_iff_of_mulSupport
#align equiv.multipliable_iff_of_support Equiv.multipliable_iff_of_support

@[to_additive]
protected theorem HasProd.map [CommMonoid γ] [TopologicalSpace γ] (hf : HasProd f a) {G}
    [MonoidHomClass G α γ] (g : G) (hg : Continuous g) : HasProd (g ∘ f) (g a) :=
  have : (g ∘ fun s : Finset β => ∏ b in s, f b) = fun s : Finset β => ∏ b in s, g (f b) :=
    funext <| map_prod g _
  show Tendsto (fun s : Finset β => ∏ b in s, g (f b)) atTop (𝓝 (g a)) from
    this ▸ (hg.tendsto a).comp hf
#align has_prod.map HasProd.map
#align has_sum.map HasSum.map

@[to_additive]
protected theorem Multipliable.map [CommMonoid γ] [TopologicalSpace γ] (hf : Multipliable f) {G}
    [MonoidHomClass G α γ] (g : G) (hg : Continuous g) : Multipliable (g ∘ f) :=
  (hf.hasProd.map g hg).multipliable
#align multipliable.map Multipliable.map

@[to_additive]
protected theorem Multipliable.map_iff_of_leftInverse [CommMonoid γ] [TopologicalSpace γ] {G G'}
    [MonoidHomClass G α γ] [MonoidHomClass G' γ α] (g : G) (g' : G') (hg : Continuous g)
    (hg' : Continuous g') (hinv : Function.LeftInverse g' g) :
    Multipliable (g ∘ f) ↔ Multipliable f :=
  ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp.assoc, hinv.id] at this , fun h => h.map _ hg⟩
#align multipliable.map_iff_of_left_inverse Multipliable.map_iff_of_leftInverse
#align summable.map_iff_of_left_inverse Summable.map_iff_of_leftInverse

/-- A special case of `multipliable.map_iff_of_left_inverse` for convenience -/
@[to_additive]
protected theorem Multipliable.map_iff_of_equiv [CommMonoid γ] [TopologicalSpace γ] {G} [MulEquivClass G α γ]
    (g : G) (hg : Continuous g) (hg' : Continuous (EquivLike.inv g : γ → α)) :
    Multipliable (g ∘ f) ↔ Multipliable f :=
  Multipliable.map_iff_of_leftInverse g (g : α ≃* γ).symm hg hg' (EquivLike.left_inv g)
#align multipliable.map_iff_of_equiv Multipliable.map_iff_of_equiv
#align summable.map_iff_of_equiv Summable.map_iff_of_equiv

/-- If `f : ℕ → α` has product `a`,
  then the partial products `∏_{i=0}^{n-1} f i` converge to `a`. -/
@[to_additive
      "If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`."]
theorem HasProd.tendsto_sum_nat {f : ℕ → α} (h : HasProd f a) :
    Tendsto (fun n : ℕ => ∏ i in range n, f i) atTop (𝓝 a) :=
  h.comp tendsto_finset_range
#align has_prod.tendsto_sum_nat HasProd.tendsto_sum_nat
#align has_sum.tendsto_sum_nat HasSum.tendsto_sum_nat

@[to_additive]
theorem HasProd.unique {a₁ a₂ : α} [T2Space α] : HasProd f a₁ → HasProd f a₂ → a₁ = a₂ :=
  tendsto_nhds_unique
#align has_prod.unique HasProd.unique
#align has_sum.unique HasSum.unique

@[to_additive]
theorem Multipliable.hasProd_iff_tendsto_nat [T2Space α] {f : ℕ → α} {a : α} (hf : Multipliable f) :
    HasProd f a ↔ Tendsto (fun n : ℕ => ∏ i in range n, f i) atTop (𝓝 a) := by
  refine' ⟨fun h => h.tendsto_sum_nat, fun h => _⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_sum_nat]
  exact hf.hasProd
#align multipliable.has_prod_iff_tendsto_nat Multipliable.hasProd_iff_tendsto_nat

@[to_additive Function.Surjective.summable_iff_of_hasSum_iff]
theorem Function.Surjective.multipliable_iff_of_hasProd_iff {α' : Type _} [CommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasProd f (e a) ↔ HasProd g a) : Multipliable f ↔ Multipliable g :=
  hes.exists.trans <| exists_congr <| @he
#align function.surjective.multipliable_iff_of_has_prod_iff Function.Surjective.multipliable_iff_of_hasProd_iff
#align function.surjective.summable_iff_of_has_sum_iff Function.Surjective.summable_iff_of_hasSum_iff

variable [ContinuousMul α] [ContinuousAdd α']

@[to_additive]
theorem HasProd.mul (hf : HasProd f a) (hg : HasProd g b) : HasProd (fun b => f b * g b) (a * b) :=
  by 
  dsimp only [HasProd] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg
#align has_prod.mul HasProd.mul
#align has_sum.add HasSum.add

@[to_additive]
theorem Multipliable.mul (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable fun b => f b * g b :=
  (hf.hasProd.mul hg.hasProd).multipliable
#align multipliable.mul Multipliable.mul

@[to_additive hasSum_sum]
theorem hasProd_mul {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasProd (f i) (a i)) → HasProd (fun b => ∏ i in s, f i b) (∏ i in s, a i) :=
  Finset.induction_on s (by simp only [hasProd_one, prod_empty, forall_true_iff]) <| by
    -- Porting note: with some help, `simp` used to be able to close the goal
    simp (config := { contextual := true }) only [mem_insert, forall_eq_or_imp, not_false_iff,
      prod_insert, and_imp]
    exact fun x s _ IH hx h ↦ hx.mul (IH h)
#align has_prod_mul hasProd_mul
#align has_sum_add hasSum_sum

@[to_additive summable_sum]
theorem multipliable_prod {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Multipliable (f i)) :
    Multipliable fun b => ∏ i in s, f i b :=
  (hasProd_mul fun i hi => (hf i hi).hasProd).multipliable
#align multipliable_prod multipliable_prod
#align summable_sum summable_sum

@[to_additive]
theorem HasProd.mul_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : t → α) b) : HasProd (f ∘ (↑) : (s ∪ t : Set β) → α) (a * b) :=
  by
  rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_union_of_disjoint hs]
  exact ha.mul hb
#align has_prod.mul_disjoint HasProd.mul_disjoint
#align has_sum.add_disjoint HasSum.add_disjoint

@[to_additive]
theorem hasProd_prod_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasProd (f ∘ (↑) : t i → α) (a i)) :
    HasProd (f ∘ (↑) : (⋃ i ∈ s, t i) → α) (∏ i in s, a i) :=
  by
  simp_rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_finset_biUnion _ _ hs]
  exact hasProd_mul hf
#align has_prod_prod_disjoint hasProd_prod_disjoint
#align has_sum_sum_disjoint hasSum_sum_disjoint

@[to_additive]
theorem HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : t → α) b) : HasProd f (a * b) := by
  simpa [← hs.compl_eq] using
    (hasProd_subtype_iff_mulIndicator.1 ha).mul (hasProd_subtype_iff_mulIndicator.1 hb)
#align has_prod.mul_is_compl HasProd.mul_isCompl
#align has_sum.add_is_compl HasSum.add_isCompl

@[to_additive]
theorem HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) → α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl hb
#align has_prod.mul_compl HasProd.mul_compl
#align has_sum.add_compl HasSum.add_compl

@[to_additive]
theorem Multipliable.mul_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s → α))
    (hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α)) : Multipliable f :=
  (hs.hasProd.mul_compl hsc.hasProd).multipliable
#align multipliable.mul_compl Multipliable.mul_compl
#align summable.add_compl Summable.add_compl

@[to_additive]
theorem HasProd.compl_mul {s : Set β} (ha : HasProd (f ∘ (↑) : (sᶜ : Set β) → α) a)
    (hb : HasProd (f ∘ (↑) : s → α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl.symm hb
#align has_prod.compl_mul HasProd.compl_mul
#align has_sum.compl_add HasSum.compl_add

@[to_additive]
theorem HasProd.even_mul_odd {f : ℕ → α} (he : HasProd (fun k => f (2 * k)) a)
    (ho : HasProd (fun k => f (2 * k + 1)) b) : HasProd f (a * b) := by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace he := this.hasProd_range_iff.2 he
  replace ho := ((add_left_injective 1).comp this).hasProd_range_iff.2 ho
  refine' he.mul_isCompl _ ho
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
#align has_prod.even_mul_odd HasProd.even_mul_odd
#align has_sum.even_add_odd HasSum.even_add_odd

@[to_additive]
theorem Multipliable.compl_mul {s : Set β} (hs : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α))
    (hsc : Multipliable (f ∘ (↑) : s → α)) : Multipliable f :=
  (hs.hasProd.compl_mul hsc.hasProd).multipliable
#align multipliable.compl_mul Multipliable.compl_mul
#align summable.compl_add Summable.compl_add

@[to_additive]
theorem Multipliable.even_mul_odd {f : ℕ → α} (he : Multipliable fun k => f (2 * k))
    (ho : Multipliable fun k => f (2 * k + 1)) : Multipliable f :=
  (he.hasProd.even_mul_odd ho.hasProd).multipliable
#align multipliable.even_mul_odd Multipliable.even_mul_odd
#align summable.even_add_odd Summable.even_add_odd

@[to_additive]
theorem HasProd.sigma [RegularSpace α] {γ : β → Type _} {f : (Σ b : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasProd f a) (hf : ∀ b, HasProd (fun c => f ⟨b, c⟩) (g b)) : HasProd g a :=
  by
  refine' (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr _
  rintro s ⟨hs, hsc⟩
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage, ge_iff_le, Finset.le_iff_subset] at hu 
  have :
    Tendsto (fun t : Finset (Σ b, γ b) => ∏ p in t.filter fun p => p.1 ∈ bs, f p) atTop
      (𝓝 <| ∏ b in bs, g b) :=
    by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine' tendsto_finset_prod _ fun b _ => _
    change
      Tendsto (fun t => (fun t => ∏ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  refine' hsc.mem_of_tendsto this (eventually_atTop.2 ⟨u, fun t ht => hu _ fun x hx => _⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩
#align has_prod.sigma HasProd.sigma
#align has_sum.sigma HasSum.sigma

/-- If a series `f` on `β × γ` has product `a`
and for each `b` the restriction of `f` to `{b} × γ` has product `g b`,
then the series `g` has product `a`. -/
@[to_additive HasSum.prod_fiberwise
      "If a series `f` on `β × γ` has sum `a`\nand for each `b` the restriction of `f` to `{b} × γ` has sum `g b`,\nthen the series `g` has sum `a`."]
theorem HasProd.prod_fiberwise [RegularSpace α] {f : β × γ → α} {g : β → α} {a : α}
    (ha : HasProd f a) (hf : ∀ b, HasProd (fun c => f (b, c)) (g b)) : HasProd g a :=
  HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf
#align has_prod.prod_fiberwise HasProd.prod_fiberwise
#align has_sum.prod_fiberwise HasSum.prod_fiberwise

@[to_additive]
theorem Multipliable.sigma' [RegularSpace α] {γ : β → Type _} {f : (Σ b : β, γ b) → α}
    (ha : Multipliable f) (hf : ∀ b, Multipliable fun c => f ⟨b, c⟩) :
    Multipliable fun b => ∏' c, f ⟨b, c⟩ :=
  (ha.hasProd.sigma fun b => (hf b).hasProd).multipliable
#align multipliable.sigma' Multipliable.sigma'
#align summable.sigma' Summable.sigma'

@[to_additive]
theorem HasProd.sigma_of_hasProd [T3Space α] {γ : β → Type _} {f : (Σ b : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasProd g a) (hf : ∀ b, HasProd (fun c => f ⟨b, c⟩) (g b))
    (hf' : Multipliable f) : HasProd f a := by
  simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd
#align has_prod.sigma_of_has_prod HasProd.sigma_of_hasProd
#align has_sum.sigma_of_has_sum HasSum.sigma_of_hasSum

/-- Version of `has_prod.update` for `comm_monoid` rather than `comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_prod`,
it gives a relationship between the products of `f` and `f.update` given that both exist. -/
@[to_additive "Version of `has_sum.update` for `add_comm_monoid` rather than 
`add_comm_group`.\nRather than showing that `f.update` has a specific sum in terms of `has_sum`,
\nit gives a relationship between the sums of `f` and `f.update` given that both exist. -/\n"]
theorem HasProd.update' {α β : Type _} [TopologicalSpace α] [CommMonoid α] [T2Space α]
    [ContinuousMul α] {f : β → α} {a a' : α} (hf : HasProd f a) (b : β) (x : α)
    (hf' : HasProd (update f b x) a') : a * x = a' * f b :=
  by
  have : ∀ b', f b' * ite (b' = b) x 1 = update f b x b' * ite (b' = b) (f b) 1 :=
    by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using mul_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.mul (hasProd_ite_eq b x)
  simp_rw [this] at h 
  exact HasProd.unique h (hf'.mul (hasProd_ite_eq b (f b)))
#align has_prod.update' HasProd.update'
#align has_sum.update' HasSum.update'

/-- Version of `has_prod_ite_div_has_prod` for `comm_monoid` rather than `comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_prod`,
it gives a relationship between the sums of `f` and `ite (n = b) 1 (f n)` given that both exist. -/
@[to_additive
      "Version of `has_sum_ite_sub_has_sum` for `add_comm_monoid` rather than `add_comm_group`.\nRather than showing that the `ite` expression has a specific sum in terms of `has_prod`,\nit gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist."]
theorem eq_mul_of_hasProd_ite {α β : Type _} [TopologicalSpace α] [CommMonoid α] [T2Space α]
    [ContinuousMul α] {f : β → α} {a : α} (hf : HasProd f a) (b : β) (a' : α)
    (hf' : HasProd (fun n => ite (n = b) 1 (f n)) a') : a = a' * f b :=
  by
  refine' (mul_one a).symm.trans (hf.update' b 1 _)
  convert hf'
  apply update_apply
#align eq_mul_of_has_prod_ite eq_mul_of_hasProd_ite
#align eq_add_of_has_sum_ite eq_add_of_hasSum_ite

end HasProd

section tprod

variable [CommMonoid α] [TopologicalSpace α] [AddCommMonoid α'] [TopologicalSpace α']

@[to_additive tsum_congr_subtype]
theorem tprod_congr_subtype (f : β → α) {s t : Set β} (h : s = t) : 
    ∏' x : s, f x = ∏' x : t, f x :=
  by rw [h]
#align tprod_congr_subtype tprod_congr_subtype
#align tsum_congr_subtype tsum_congr_subtype

theorem tsum_eq_finsum {f : β → α'} (hf : (support f).Finite) :
    ∑' b, f b = ∑ᶠ b, f b := by simp [tsum_def, summable_of_finite_support hf, hf]

theorem tprod_eq_finprod {f : β → α} (hf : (mulSupport f).Finite) :
    ∏' b, f b = ∏ᶠ b, f b := by simp [tprod_def, multipliable_of_finite_mulSupport hf, hf]

@[simp]
theorem tsum_zero : ∑' _ : β, (0 : α') = 0 := by rw [tsum_eq_finsum] <;> simp
#align tsum_zero tsum_zero
#align tsum_zero' tsum_zero

@[to_additive (attr := simp) existing tsum_zero]
theorem tprod_one : ∏' _ : β, (1 : α) = 1 := by rw [tprod_eq_finprod] <;> simp
#align tprod_one tprod_one

variable [T2Space α] [T2Space α'] {f g : β → α} {a a₁ a₂ : α}

@[to_additive HasSum.tsum_eq]
theorem HasProd.tprod_eq (ha : HasProd f a) : ∏' b, f b = a :=
  (Multipliable.hasProd ⟨a, ha⟩).unique ha
#align has_prod.tprod_eq HasProd.tprod_eq

@[to_additive]
theorem Multipliable.hasProd_iff (h : Multipliable f) : HasProd f a ↔ ∏' b, f b = a :=
  Iff.intro HasProd.tprod_eq fun eq => eq ▸ h.hasProd
#align multipliable.has_prod_iff Multipliable.hasProd_iff
#align summable.has_sum_iff Summable.hasSum_iff

@[to_additive tsum_empty]
theorem tprod_empty [IsEmpty β] : ∏' b, f b = 1 :=
  hasProd_empty.tprod_eq
#align tprod_empty tprod_empty
#align tsum_empty tsum_empty


/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b «expr ∉ » s) -/
@[to_additive tsum_eq_sum]
theorem tprod_eq_prod {f : β → α} {s : Finset β} (hf : ∀ (b) (_ : b ∉ s), f b = 1) :
    ∏' b, f b = ∏ b in s, f b :=
  (hasProd_prod_of_ne_finset_one hf).tprod_eq
#align tprod_eq_prod tprod_eq_prod
#align tsum_eq_sum tsum_eq_sum

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » s) -/
@[to_additive sum_eq_tsum_indicator]
theorem prod_eq_tprod_mulIndicator (f : β → α) (s : Finset β) :
    ∏ x in s, f x = ∏' x, Set.mulIndicator (↑s) f x :=
  have : ∀ (x) (_ : x ∉ s), Set.mulIndicator (↑s) f x = 1 := fun _ hx =>
    Set.mulIndicator_apply_eq_one.2 fun hx' => (hx <| Finset.mem_coe.1 hx').elim
  (Finset.prod_congr rfl fun _ hx =>
        (Set.mulIndicator_apply_eq_self.2 fun hx' => (hx' <| Finset.mem_coe.2 hx).elim).symm).trans
    (tprod_eq_prod this).symm
#align prod_eq_tprod_mul_indicator prod_eq_tprod_mulIndicator
#align sum_eq_tsum_indicator sum_eq_tsum_indicator

@[to_additive tsum_congr]
theorem tprod_congr {α β : Type _} [CommMonoid α] [TopologicalSpace α] {f g : β → α}
    (hfg : ∀ b, f b = g b) : ∏' b, f b = ∏' b, g b :=
  congr_arg tprod (funext hfg)
#align tprod_congr tprod_congr
#align tsum_congr tsum_congr

@[to_additive tsum_fintype]
theorem tprod_fintype [Fintype β] (f : β → α) : ∏' b, f b = ∏ b, f b :=
  (hasProd_fintype f).tprod_eq
#align tprod_fintype tprod_fintype
#align tsum_fintype tsum_fintype

@[to_additive tsum_bool]
theorem tprod_bool (f : Bool → α) : ∏' i : Bool, f i = f False * f True := by
  rw [tprod_fintype, Finset.prod_eq_mul] <;> simp
#align tprod_bool tprod_bool
#align tsum_bool tsum_bool

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b' «expr ≠ » b) -/
@[to_additive tsum_eq_single]
theorem tprod_eq_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 1) :
    ∏' b, f b = f b :=
  (hasProd_mulSingle b hf).tprod_eq
#align tprod_eq_mul_single tprod_eq_single
#align tprod_eq_single tsum_eq_single

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b' c') -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b' «expr ≠ » b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b' c') -/
@[to_additive tsum_tsum_eq_single]
theorem tprod_tprod_eq_single (f : β → γ → α) (b : β) (c : γ)
    (hfb : ∀ (b') (_ : b' ≠ b), f b' c = 1) (hfc : ∀ (b' : β) (c' : γ), c' ≠ c → f b' c' = 1) :
    ∏' (b') (c'), f b' c' = f b c :=
  calc
    ∏' (b') (c'), f b' c' = ∏' b', f b' c := tprod_congr fun b' => tprod_eq_single _ (hfc b')
    _ = f b c := tprod_eq_single _ hfb
#align tprod_tprod_eq_single tprod_tprod_eq_single
#align tsum_tsum_eq_single tsum_tsum_eq_single

@[to_additive (attr := simp) tsum_ite_eq]
theorem tprod_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    (∏' b', if b' = b then a else 1) = a :=
  (hasProd_ite_eq b a).tprod_eq
#align tprod_ite_eq tprod_ite_eq
#align tsum_ite_eq tsum_ite_eq

@[to_additive (attr := simp) tsum_pi_single]
theorem tprod_pi_mulSingle [DecidableEq β] (b : β) (a : α) : ∏' b', Pi.mulSingle b a b' = a :=
  (hasProd_pi_mulSingle b a).tprod_eq
#align tprod_pi_mul_single tprod_pi_mulSingle
#align tsum_pi_single tsum_pi_single

@[to_additive tsum_dite_right]
theorem tprod_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    (∏' b : β, if h : P then (1 : α) else x b h) = if h : P then (1 : α) else ∏' b : β, x b h := by
  by_cases hP : P <;> simp [hP]
#align tprod_dite_right tprod_dite_right
#align tsum_dite_right tsum_dite_right

@[to_additive tsum_dite_left]
theorem tprod_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    (∏' b : β, if h : P then x b h else 1) = if h : P then ∏' b : β, x b h else 1 := by
  by_cases hP : P <;> simp [hP]
#align tprod_dite_left tprod_dite_left
#align tsum_dite_left tsum_dite_left

theorem Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum  {γ' : Type _} [AddCommMonoid γ']
    [TopologicalSpace γ'] {e : γ' → α'} (hes : Function.Surjective e) (h0 : e 0 = 0) {f : β → α'}
    {g : δ → γ'} (h : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : ∑' b, f b = e (∑' c, g c) :=
  _root_.by_cases (fun this : Summable g => (h.mpr this.hasSum).tsum_eq) fun hg : ¬Summable g =>
    by
    have hf : ¬Summable f := mt (hes.summable_iff_of_hasSum_iff @h).1 hg
    simp [tsum, hf, hg, h0]
#align function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum 
  Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum

@[to_additive existing Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum]
theorem Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd {α' : Type _} [CommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h1 : e 1 = 1) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasProd f (e a) ↔ HasProd g a) : ∏' b, f b = e (∏' c, g c) :=
  _root_.by_cases (fun this : Multipliable g => (h.mpr this.hasProd).tprod_eq) 
    fun hg : ¬Multipliable g => by
    have hf : ¬Multipliable f := mt (hes.multipliable_iff_of_hasProd_iff @h).1 hg
    simp [tprod, hf, hg, h1]
#align function.surjective.tprod_eq_tprod_of_has_prod_iff_has_prod
  Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd

@[to_additive tsum_eq_tsum_of_hasSum_iff_hasSum]
theorem tprod_eq_tprod_of_hasProd_iff_hasProd {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasProd f a ↔ HasProd g a) : ∏' b, f b = ∏' c, g c :=
  surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd rfl @h
#align tprod_eq_tprod_of_has_prod_iff_has_prod tprod_eq_tprod_of_hasProd_iff_hasProd
#align tsum_eq_tsum_of_has_sum_iff_has_sum tsum_eq_tsum_of_hasSum_iff_hasSum

@[to_additive Equiv.tsum_eq]
theorem Equiv.tprod_eq (j : γ ≃ β) (f : β → α) : ∏' c, f (j c) = ∏' b, f b :=
  tprod_eq_tprod_of_hasProd_iff_hasProd j.hasProd_iff
#align equiv.tprod_eq Equiv.tprod_eq
#align equiv.tsum_eq Equiv.tsum_eq

@[to_additive Equiv.tsum_eq_tsum_of_support]
theorem Equiv.tprod_eq_tprod_of_mulSupport {f : β → α} {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x, g (e x) = f x) : ∏' x, f x = ∏' y, g y :=
  tprod_eq_tprod_of_hasProd_iff_hasProd (e.hasProd_iff_of_mulSupport he)
#align equiv.tprod_eq_tprod_of_mul_support Equiv.tprod_eq_tprod_of_mulSupport
#align equiv.tsum_eq_tsup_of_support Equiv.tsum_eq_tsum_of_support

@[to_additive tsum_eq_tsum_of_ne_zero_bij]
theorem tprod_eq_tprod_of_ne_one_bij {g : γ → α} (i : mulSupport g → β)
    (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : mulSupport f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : ∏' x, f x = ∏' y, g y :=
  tprod_eq_tprod_of_hasProd_iff_hasProd (hasProd_iff_hasProd_of_ne_one_bij i hi hf hfg)
#align tprod_eq_tprod_of_ne_one_bij tprod_eq_tprod_of_ne_one_bij
#align tsum_eq_tsum_of_ne_zero_bij tsum_eq_tsum_of_ne_zero_bij

/-! ### `tprod` on subsets -/

@[to_additive Finset.tsum_subtype]
theorem Finset.tprod_subtype (s : Finset β) (f : β → α) :
    ∏' x : { x // x ∈ s }, f x = ∏ x in s, f x :=
  (s.hasProd f).tprod_eq
#align finset.tprod_subtype Finset.tprod_subtype
#align finset.tsum_subtype Finset.tsum_subtype

@[to_additive Finset.tsum_subtype']
theorem Finset.tprod_subtype' (s : Finset β) (f : β → α) :
    ∏' x : (s : Set β), f x = ∏ x in s, f x :=
  s.tprod_subtype f
#align finset.tprod_subtype' Finset.tprod_subtype'
#align finset.tsum_subtype' Finset.tsum_subtype'

@[to_additive tsum_subtype]
theorem tprod_subtype (s : Set β) (f : β → α) : ∏' x : s, f x = ∏' x, s.mulIndicator f x :=
  tprod_eq_tprod_of_hasProd_iff_hasProd hasProd_subtype_iff_mulIndicator
#align tprod_subtype tprod_subtype
#align tsum_subtype tsum_subtype

@[to_additive]
theorem tprod_subtype_eq_of_mulSupport_subset {f : β → α} {s : Set β} (hs : mulSupport f ⊆ s) :
    ∏' x : s, f x = ∏' x, f x :=
  tprod_eq_tprod_of_hasProd_iff_hasProd (hasProd_subtype_iff_of_mulSupport_subset hs)
#align tprod_subtype_eq_of_mul_support_subset tprod_subtype_eq_of_mulSupport_subset
#align tprod_subtype_eq_of_support_subset tprod_subtype_eq_of_support_subset

@[to_additive tsum_univ]
theorem tprod_univ (f : β → α) : ∏' x : (Set.univ : Set β), f x = ∏' x, f x :=
  tprod_subtype_eq_of_mulSupport_subset <| Set.subset_univ _
#align tprod_univ tprod_univ
#align tsum_univ tsum_univ

@[to_additive tsum_singleton]
theorem tprod_singleton (b : β) (f : β → α) : ∏' x : ({b} : Set β), f x = f b := by
  rw [← coe_singleton, Finset.tprod_subtype', prod_singleton]
#align tprod_singleton tprod_singleton
#align tsum_singleton tsum_singleton

@[to_additive tsum_image]
theorem tprod_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    ∏' x : g '' s, f x = ∏' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tprod_eq fun x => f x).symm
#align tprod_image tprod_image
#align tsum_image tsum_image

@[to_additive tsum_range]
theorem tprod_range {g : γ → β} (f : β → α) (hg : Injective g) :
    ∏' x : Set.range g, f x = ∏' x, f (g x) := by
  rw [← Set.image_univ, tprod_image f (hg.injOn _)]
  simp_rw [← comp_apply (g := g), tprod_univ (f ∘ g)]
#align tprod_range tprod_range
#align tsum_range tsum_range

section ContinuousAdd

variable [ContinuousMul α]

@[to_additive tsum_add]
theorem tprod_mul (hf : Multipliable f) (hg : Multipliable g) :
    ∏' b, f b * g b = (∏' b, f b) * ∏' b, g b :=
  (hf.hasProd.mul hg.hasProd).tprod_eq
#align tprod_mul tprod_mul
#align tsum_add tsum_add

@[to_additive tsum_sum]
theorem tprod_prod {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Multipliable (f i)) :
    ∏' b, ∏ i in s, f i b = ∏ i in s, ∏' b, f i b :=
  (hasProd_mul fun i hi => (hf i hi).hasProd).tprod_eq
#align tprod_prod tprod_prod
#align tsum_sum tsum_sum

/-- Version of `tprod_eq_mul_tprod_ite` for `comm_monoid` rather than `comm_group`.
Requires a different convergence assumption involving `function.update`. -/
@[to_additive tsum_eq_add_tsum_ite'
      "Version of `tsum_eq_add_tsum_ite` for `add_comm_monoid` rather than `add_comm_group`.\nRequires a different convergence assumption involving `function.update`."]
theorem tprod_eq_mul_tprod_ite' {f : β → α} (b : β) (hf : Multipliable (update f b 1)) :
    ∏' x, f x = f b * ∏' x, ite (x = b) 1 (f x) := by
  have : ∏' x, f x = ∏' x, ite (x = b) (f x) 1 * update f b 1 x := by 
    apply tprod_congr
    intro c
    split_ifs with h <;> simp [Function.update_apply, h]
  rw [this, tprod_mul _ hf]
  . congr
    . rw [tprod_eq_single b]
      simp only [eq_self_iff_true, if_true]
      intro c hc
      rw [if_neg hc]
    . simp only [Function.update_apply]
  . exact ⟨ite (b = b) (f b) 1, hasProd_mulSingle b fun b hb => if_neg hb⟩
#align tprod_eq_mul_tprod_ite' tprod_eq_mul_tprod_ite'
#align tsum_eq_add_tsum_ite' tsum_eq_add_tsum_ite'

variable [TopologicalSpace δ] [T3Space δ]

variable [CommMonoid δ] [ContinuousMul δ]

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
@[to_additive tsum_sigma']
theorem tprod_sigma' {γ : β → Type _} {f : (Σ b : β, γ b) → δ}
    (h₁ : ∀ b, Multipliable fun c => f ⟨b, c⟩) (h₂ : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  (h₂.hasProd.sigma fun b => (h₁ b).hasProd).tprod_eq.symm
#align tprod_sigma' tprod_sigma'
#align tsum_sigma' tsum_sigma'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
@[to_additive tsum_sum']
theorem tprod_prod' {f : β × γ → δ} (h : Multipliable f)
    (h₁ : ∀ b, Multipliable fun c => f (b, c)) : ∏' p, f p = ∏' (b) (c), f (b, c) :=
  (h.hasProd.prod_fiberwise fun b => (h₁ b).hasProd).tprod_eq.symm
#align tprod_prod' tprod_prod'
#align tsum_sum' tsum_sum'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (c b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
@[to_additive tsum_comm']
theorem tprod_comm' {f : β → γ → δ} (h : Multipliable (Function.uncurry f))
    (h₁ : ∀ b, Multipliable (f b)) (h₂ : ∀ c, Multipliable fun b => f b c) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c :=
  by
  erw [← tprod_prod' h h₁, ← tprod_prod' h.prod_symm h₂, ←
    (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl
#align tprod_comm' tprod_comm'
#align tsum_comm' tsum_comm'

end ContinuousAdd

open Encodable

section Encodable

variable [Encodable γ]

/- have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).isSome :=by
    intro n h
    generalize decode₂ γ n = foo at *
    cases' foo with b
    · refine' (h <| by simp [m0]).elim
    · exact rfl
  symm
  refine' tsum_eq_tsum_of_ne_zero_bij (fun a => Option.get _ (H a.1 a.2)) _ _ _
  · dsimp only []
    rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    have := mem_decode₂.1 (Option.get_mem (H n hn))
    rwa [← e, mem_decode₂.1 (Option.get_mem (H m hm))] at this
  · intro b h
    refine' ⟨⟨encode b, _⟩, _⟩
    · simp only [mem_support, encodek₂] at h ⊢
      convert h
      simp [Set.ext_iff, encodek₂]
    · exact Option.get_of_mem _ (encodek₂ _)
  · rintro ⟨n, h⟩
    dsimp only [Subtype.coe_mk]
    trans
    swap
    rw [show decode₂ γ n = _ from Option.get_mem (H n h)]
    congr
    simp [ext_iff, -Option.some_get]-/

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_iSup_decode₂ [CompleteLattice β] (m : β → α') (m0 : m ⊥ = 0) (s : γ → β) :
    ∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∑' b : γ, m (s b) := by
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).isSome :=by
    intro n h
    generalize decode₂ γ n = foo at *
    cases' foo with b
    · refine' (h <| by simp [m0]).elim
    · exact rfl
  symm
  refine' tsum_eq_tsum_of_ne_zero_bij (fun a => Option.get _ (H a.1 a.2)) _ _ _
  · dsimp only []
    rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    have := mem_decode₂.1 (Option.get_mem (H n hn))
    rwa [← e, mem_decode₂.1 (Option.get_mem (H m hm))] at this
  · intro b h
    refine' ⟨⟨encode b, _⟩, _⟩
    · simp only [mem_support, encodek₂] at h ⊢
      convert h
      simp [Set.ext_iff, encodek₂]
    · exact Option.get_of_mem _ (encodek₂ _)
  · rintro ⟨n, h⟩
    dsimp only [Subtype.coe_mk]
    trans
    swap
    rw [show decode₂ γ n = _ from Option.get_mem (H n h)]
    congr
    simp [ext_iff, -Option.some_get]
#align tsum_supr_decode₂ tsum_iSup_decode₂

/-- You can compute a product over an encodably type by multiplying over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
@[to_additive existing tsum_iSup_decode₂]
theorem tprod_iSup_decode₂ [CompleteLattice β] (m : β → α) (m1 : m ⊥ = 1) (s : γ → β) :
    ∏' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∏' b : γ, m (s b) := by
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 1 → (decode₂ γ n).isSome := by
    intro n h
    generalize decode₂ γ n = foo at *
    cases' foo with b
    · refine' (h <| by simp [m1]).elim
    · exact rfl
  symm
  refine' tprod_eq_tprod_of_ne_one_bij (fun a => Option.get _ (H a.1 a.2)) _ _ _
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    have := mem_decode₂.1 (Option.get_mem (H n hn))
    simp only at e 
    rwa [← e, mem_decode₂.1 (Option.get_mem (H m hm))] at this
  · intro b h
    refine' ⟨⟨encode b, _⟩, _⟩
    · simp only [mem_mulSupport, encodek₂] at h ⊢; convert h; simp [Set.ext_iff, encodek₂]
    · exact Option.get_of_mem _ (encodek₂ _)
  · rintro ⟨n, h⟩; dsimp only [Subtype.coe_mk]
    trans; swap
    rw [show decode₂ γ n = _ from Option.get_mem (H n h)]
    congr; simp [ext_iff, -Option.some_get]
#align tprod_supr_decode₂ tprod_iSup_decode₂

/-- `tprod_supr_decode₂` specialized to the complete lattice of sets. -/
@[to_additive tsum_iUnion_decode₂]
theorem tprod_iUnion_decode₂ (m : Set β → α) (m1 : m ∅ = 1) (s : γ → Set β) :
    ∏' i, m (⋃ b ∈ decode₂ γ i, s b) = ∏' b, m (s b) :=
  tprod_iSup_decode₂ m m1 s
#align tprod_Union_decode₂ tprod_iUnion_decode₂
#align tsum_Union_decode₂ tsum_iUnion_decode₂

end Encodable

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/


section Countable

variable [Countable γ]

/-- If a function is countably sub-additive then it is sub-additive on countable types -/
@[to_additive rel_iSup_tsum]
theorem rel_iSup_tprod [CompleteLattice β] (m : β → α) (m1 : m ⊥ = 1) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : γ → β) :
    R (m (⨆ b : γ, s b)) (∏' b : γ, m (s b)) := by 
  cases nonempty_encodable γ
  rw [← iSup_decode₂, ← tprod_iSup_decode₂ _ m1 s] 
  exact m_supr _
#align rel_supr_tprod rel_iSup_tprod
#align rel_supr_tsum rel_iSup_tsum

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
@[to_additive]
theorem rel_iSup_prod [CompleteLattice β] (m : β → α) (m1 : m ⊥ = 1) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : δ → β) (t : Finset δ) :
    R (m (⨆ d ∈ t, s d)) (∏ d in t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tprod_subtype]
  exact rel_iSup_tprod m m1 R m_supr _
#align rel_supr_prod rel_iSup_prod
#align rel_supr_sum rel_iSup_sum

/-- If a function is countably sub-additive then it is binary sub-additive -/
@[to_additive]
theorem rel_sup_mul [CompleteLattice β] (m : β → α) (m1 : m ⊥ = 1) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ : β) :
    R (m (s₁ ⊔ s₂)) (m s₁ * m s₂) :=
  by
  convert rel_iSup_tprod m m1 R m_supr fun b => cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]
#align rel_sup_mul rel_sup_mul
#align rel_sup_add rel_sup_add

end Countable

variable [ContinuousMul α]

@[to_additive tsum_add_tsum_compl]
theorem tprod_mul_tprod_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s → α))
    (hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α)) : 
    (∏' x : s, f x) * ∏' x : (sᶜ : Set β), f x = ∏' x, f x :=
  (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm
#align tprod_mul_tprod_compl tprod_mul_tprod_compl
#align tsum_add_tsum_compl tsum_add_tsum_compl

@[to_additive tsum_union_disjoint]
theorem tprod_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Multipliable (f ∘ (↑) : s → α))
    (ht : Multipliable (f ∘ (↑) : t → α)) : 
    ∏' x : (s ∪ t : Set β), f x = (∏' x : s, f x) * ∏' x : t, f x :=
  (hs.hasProd.mul_disjoint hd ht.hasProd).tprod_eq
#align tprod_union_disjoint tprod_union_disjoint
#align tsum_union_disjoint tsum_union_disjoint

@[to_additive tsum_finset_bUnion_disjoint]
theorem tprod_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Multipliable (f ∘ (↑) : t i → α)) :
    ∏' x : ⋃ i ∈ s, t i, f x = ∏ i in s, ∏' x : t i, f x :=
  (hasProd_prod_disjoint _ hd fun i hi => (hf i hi).hasProd).tprod_eq
#align tprod_finset_bUnion_disjoint tprod_finset_bUnion_disjoint
#align tsum_finset_bUnion_disjoint tsum_finset_bUnion_disjoint

@[to_additive tsum_even_add_odd]
theorem tprod_even_mul_odd {f : ℕ → α} (he : Multipliable fun k => f (2 * k))
    (ho : Multipliable fun k => f (2 * k + 1)) :
    (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' k, f k :=
  (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm
#align tprod_even_mul_odd tprod_even_mul_odd
#align tsum_even_add_odd tsum_even_add_odd

end tprod

section TopologicalGroup

variable [TopologicalSpace α]

variable [CommGroup α] [TopologicalGroup α]

variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
@[to_additive]
theorem HasProd.inv (h : HasProd f a) : HasProd (fun b => (f b)⁻¹) a⁻¹ := by
  simpa only using h.map (MonoidHom.id α)⁻¹ continuous_inv
#align has_prod.inv HasProd.inv
#align has_sum.neg HasSum.neg

@[to_additive]
theorem Multipliable.inv (hf : Multipliable f) : Multipliable fun b => (f b)⁻¹ :=
  hf.hasProd.inv.multipliable
#align multipliable.inv Multipliable.inv
#align summable.neg Summable.neg

@[to_additive]
theorem Multipliable.of_inv (hf : Multipliable fun b => (f b)⁻¹) : Multipliable f := by
  simpa only [inv_inv] using hf.inv
#align multipliable.of_inv Multipliable.of_inv
#align summable.of_neg Summable.of_neg

@[to_additive summable_neg_iff]
theorem multipliable_inv_iff : (Multipliable fun b => (f b)⁻¹) ↔ Multipliable f :=
  ⟨Multipliable.of_inv, Multipliable.inv⟩
#align multipliable_inv_iff multipliable_inv_iff
#align summable_neg_iff summable_neg_iff

@[to_additive]
theorem HasProd.div (hf : HasProd f a₁) (hg : HasProd g a₂) :
    HasProd (fun b => f b / g b) (a₁ / a₂) := by simp only [div_eq_mul_inv]; exact hf.mul hg.inv
#align has_prod.div HasProd.div
#align has_sum.sub HasSum.sub

@[to_additive]
theorem Multipliable.div (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable fun b => f b / g b :=
  (hf.hasProd.div hg.hasProd).multipliable
#align multipliable.div Multipliable.div
#align summable.sub Summable.sub

@[to_additive]
theorem Multipliable.trans_div (hg : Multipliable g) (hfg : Multipliable fun b => f b / g b) :
    Multipliable f := by simpa only [div_mul_cancel'] using hfg.mul hg
#align multipliable.trans_div Multipliable.trans_div
#align summable.trans_sub Summable.trans_sub

@[to_additive summable_iff_of_summable_sub]
theorem multipliable_iff_of_multipliable_div (hfg : Multipliable fun b => f b / g b) :
    Multipliable f ↔ Multipliable g :=
  ⟨fun hf => hf.trans_div <| by simpa only [inv_div] using hfg.inv, fun hg => hg.trans_div hfg⟩
#align multipliable_iff_of_multipliable_div multipliable_iff_of_multipliable_div
#align summable_iff_of_summable_sub summable_iff_of_summable_sub

@[to_additive]
theorem HasProd.update (hf : HasProd f a₁) (b : β) [DecidableEq β] (a : α) :
    HasProd (update f b a) (a / f b * a₁) := by
  convert (hasProd_ite_eq b _).mul hf
  rename_i b'
  by_cases h : b' = b
  · rw [h, update_same]
    simp only [eq_self_iff_true, if_true, div_mul_cancel']
  simp only [h, update_noteq, if_false, Ne.def, one_mul, not_false_iff]
#align has_prod.update HasProd.update
#align has_sum.update HasSum.update

@[to_additive]
theorem Multipliable.update (hf : Multipliable f) (b : β) [DecidableEq β] (a : α) :
    Multipliable (update f b a) :=
  (hf.hasProd.update b a).multipliable
#align multipliable.update Multipliable.update
#align summable.update Summable.update
 
@[to_additive]
theorem HasProd.hasProd_compl_iff {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd (f ∘ (↑) : (sᶜ : Set β) → α) a₂ ↔ HasProd f (a₁ * a₂) := by
  refine' ⟨fun h => hf.mul_compl h, fun h => _⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  convert h.div hf
  simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  rw [mul_div_cancel''']
#align has_prod.has_prod_compl_iff HasProd.hasProd_compl_iff
#align has_sum.has_sum_compl_iff HasSum.hasSum_compl_iff

@[to_additive]
theorem HasProd.hasProd_iff_compl {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd f a₂ ↔ HasProd (f ∘ (↑) : (sᶜ : Set β) → α) (a₂ / a₁) :=
  Iff.symm <| hf.hasProd_compl_iff.trans <| by rw [mul_div_cancel'_right]
#align has_prod.has_prod_iff_compl HasProd.hasProd_iff_compl
#align has_sum.has_sum_iff_compl HasSum.hasSum_iff_compl

@[to_additive Summable.summable_compl_iff]
theorem Multipliable.multipliable_compl_iff {s : Set β} (hf : Multipliable (f ∘ (↑) : s → α)) :
    Multipliable (f ∘ (↑) : (sᶜ : Set β) → α) ↔ Multipliable f :=
  ⟨fun ⟨_, ha⟩ => (hf.hasProd.hasProd_compl_iff.1 ha).multipliable, fun ⟨_, ha⟩ =>
    (hf.hasProd.hasProd_iff_compl.1 ha).multipliable⟩
#align multipliable.multipliable_compl_iff Multipliable.multipliable_compl_iff
#align summable.summable_compl_iff Summable.summable_compl_iff

@[to_additive]
protected theorem Finset.hasProd_compl_iff (s : Finset β) :
    HasProd (fun x : { x // x ∉ s } => f x) a ↔ HasProd f (a * ∏ i in s, f i) :=
  (s.hasProd f).hasProd_compl_iff.trans <| by rw [mul_comm]
#align finset.has_prod_compl_iff Finset.hasProd_compl_iff
#align finset.has_sum_compl_iff Finset.hasSum_compl_iff

@[to_additive]
protected theorem Finset.hasProd_iff_compl (s : Finset β) :
    HasProd f a ↔ HasProd (fun x : { x // x ∉ s } => f x) (a / ∏ i in s, f i) :=
  (s.hasProd f).hasProd_iff_compl
#align finset.has_prod_iff_compl Finset.hasProd_iff_compl
#align finset.has_sum_iff_compl Finset.hasSum_iff_compl

@[to_additive Finset.summable_compl_iff]
protected theorem Finset.multipliable_compl_iff (s : Finset β) :
    (Multipliable fun x : { x // x ∉ s } => f x) ↔ Multipliable f :=
  (s.multipliable f).multipliable_compl_iff
#align finset.multipliable_compl_iff Finset.multipliable_compl_iff
#align finset.summable_compl_iff Finset.summable_compl_iff

@[to_additive Set.Finite.summable_compl]
theorem Set.Finite.multipliable_compl_iff {s : Set β} (hs : s.Finite) :
    Multipliable (f ∘ (↑) : (sᶜ : Set β) → α) ↔ Multipliable f :=
  (hs.multipliable f).multipliable_compl_iff
#align set.finite.multipliable_compl_iff Set.Finite.multipliable_compl_iff
#align set.finite.summable_compl Set.Finite.summable_compl

@[to_additive]
theorem hasProd_ite_div_hasProd [DecidableEq β] (hf : HasProd f a) (b : β) :
    HasProd (fun n => ite (n = b) 1 (f n)) (a / f b) :=
  by
  convert hf.update b 1 using 1
  · ext n; rw [Function.update_apply]
  · rw [div_mul_eq_mul_div, one_mul]
#align has_prod_ite_div_has_prod hasProd_ite_div_hasProd
#align has_sum_ite_sub_has_sum hasSum_ite_sub_hasSum

section tprod

variable [T2Space α]

@[to_additive tsum_neg]
theorem tprod_inv : ∏' b, (f b)⁻¹ = (∏' b, f b)⁻¹ :=
  by
  by_cases hf : Multipliable f
  · exact hf.hasProd.inv.tprod_eq
  · simp [tprod_eq_one_of_not_multipliable hf,
      tprod_eq_one_of_not_multipliable (mt Multipliable.of_inv hf)]
#align tprod_inv tprod_inv
#align tsum_neg tsum_neg

@[to_additive tsum_div]
theorem tprod_sub (hf : Multipliable f) (hg : Multipliable g) :
    ∏' b, f b / g b = (∏' b, f b) / ∏' b, g b :=
  (hf.hasProd.div hg.hasProd).tprod_eq
#align tprod_sub tprod_sub
#align tsum_div tsum_div

@[to_additive sum_add_tsum_compl]
theorem prod_mul_tprod_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s → α)) 
    (hsc : Multipliable (f ∘ (↑) : ↑sᶜ → α)) :
    (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm
#align prod_mul_tprod_compl prod_mul_tprod_compl
#align sum_add_tsum_compl sum_add_tsum_compl

/-- Let `f : β → α` be a sequence with multipliable series and let `b ∈ β` be an index.
Lemma `tprod_eq_mul_tprod_ite` writes `∏' f n` as the product of `f b` times
the infinite produt of the remaining terms. -/
@[to_additive tsum_eq_add_tsum_ite
      "Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.\nLemma `tsum_eq_add_tsum_ite` writes `Σ' f n` as the sum of `f b` plus the series of the\nremaining terms"]
theorem tprod_eq_mul_tprod_ite [DecidableEq β] (hf : Multipliable f) (b : β) :
    ∏' n, f n = f b * ∏' n, ite (n = b) 1 (f n) :=
  by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel'_right _ _).symm
#align tprod_eq_mul_tprod_ite tprod_eq_mul_tprod_ite
#align tsum_eq_add_tsum_ite tsum_eq_add_tsum_ite

end tprod

/-!
### Sums on nat

We show the formula `(∑ i in range k, f i) + (∏' i, f (i + k)) = (∏' i, f i)`, in
`sum_add_tprod_nat_add`, as well as several results relating sums on `ℕ` and `ℤ`.
-/

section Nat

@[to_additive]
theorem hasProd_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
    HasProd (fun n => f (n + k)) a ↔ HasProd f (a * ∏ i in range k, f i) := by
  refine' Iff.trans _ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff]
  rfl
#align has_prod_nat_add_iff hasProd_nat_add_iff
#align has_sum_nat_add_iff hasSum_nat_add_iff

@[to_additive summable_nat_add_iff]
theorem multipliable_nat_add_iff {f : ℕ → α} (k : ℕ) :
    (Multipliable fun n => f (n + k)) ↔ Multipliable f :=
  Iff.symm <|
    (Equiv.mulRight (∏ i in range k, f i)).surjective.multipliable_iff_of_hasProd_iff 
      (hasProd_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff

@[to_additive]
theorem hasProd_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
    HasProd (fun n => f (n + k)) (a / ∏ i in range k, f i) ↔ HasProd f a := by
  simp [hasProd_nat_add_iff]
#align has_prod_nat_add_iff' hasProd_nat_add_iff'
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

@[to_additive sum_add_tsum_nat_add]
theorem prod_mul_tprod_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Multipliable f) :
    (∏ i in range k, f i) * ∏' i, f (i + k) = ∏' i, f i := by
  simpa only [mul_comm] using
    ((hasProd_nat_add_iff k).1 ((multipliable_nat_add_iff k).2 h).hasProd).unique h.hasProd
#align prod_mul_tprod_nat_add prod_mul_tprod_nat_add
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

@[to_additive tsum_eq_zero_add]
theorem tprod_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Multipliable f) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) := by
  simpa only [prod_range_one] using (prod_mul_tprod_nat_add 1 hf).symm
#align tprod_eq_zero_add tprod_eq_zero_add
#align tsum_eq_zero_add tsum_eq_zero_add

/-- For `f : ℕ → α`, then `∏' k, f (k + i)` tends to 1.
This does not require a summability assumption on `f`, as otherwise all sums are 1. -/
@[to_additive
      "For `f : ℕ → α`, then `∑' k, f (k + i)` tends to 0. This does not require a summability\nassumption on `f`, as otherwise all sums are 0."]
theorem tendsto_prod_nat_add [T2Space α] (f : ℕ → α) :
    Tendsto (fun i => ∏' k, f (k + i)) atTop (𝓝 1) :=
  by
  by_cases hf : Multipliable f
  · have h₀ : (fun i => (∏' i, f i) / ∏ j in range i, f j) = fun i => ∏' k : ℕ, f (k + i) :=
      by
      ext1 i
      rw [div_eq_iff_eq_mul, mul_comm, prod_mul_tprod_nat_add i hf]
    have h₁ : Tendsto (fun _ : ℕ => ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [← h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_sum_nat
  . convert tendsto_const_nhds (α := α) (β := ℕ) (a := 1) (f := atTop)
    rename_i i
    rw [← multipliable_nat_add_iff i] at hf
    exact tprod_eq_one_of_not_multipliable hf
#align tendsto_prod_nat_add tendsto_prod_nat_add
#align tendsto_sum_nat_add tendsto_sum_nat_add

/- simpa only [h₀, sub_self] using Tendsto.sub h₁ hf.hasSum.tendsto_sum_nat -/

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
@[to_additive]
theorem HasProd.int_rec {b : α} {f g : ℕ → α} (hf : HasProd f a) (hg : HasProd g b) :
    @HasProd α _ _ _ (@Int.rec (fun _ => α) f g : ℤ → α) (a * b) :=
  by
  -- note this proof works for any two-case inductive
  have h₁ : Injective ((↑) : ℕ → ℤ) := @Int.ofNat.inj
  have h₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) :=
    by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) _
      exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  exact HasProd.mul_isCompl this (h₁.hasProd_range_iff.mpr hf) (h₂.hasProd_range_iff.mpr hg)
#align has_prod.int_rec HasProd.int_rec
#align has_sum.int_rec HasSum.int_rec

@[to_additive HasSum.nonneg_mul_inv]
theorem HasProd.nonneg_add_neg {b : α} {f : ℤ → α} (hnonneg : HasProd (fun n : ℕ => f n) a)
    (hneg : HasProd (fun n : ℕ => f (-n.succ)) b) : HasProd f (a * b) :=
  by
  simp_rw [← Int.negSucc_coe] at hneg 
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl
#align has_prod.nonneg_add_neg HasProd.nonneg_add_neg
#align has_sum.nonneg_mul_inv HasSum.nonneg_mul_inv

@[to_additive]
theorem HasProd.pos_mul_zero_mul_neg {b : α} {f : ℤ → α} (hpos : HasProd (fun n : ℕ => f (n + 1)) a)
    (hneg : HasProd (fun n : ℕ => f (-n.succ)) b) : HasProd f (a * f 0 * b) :=
  haveI : ∀ g : ℕ → α, HasProd (fun k => g (k + 1)) a → HasProd g (a * g 0) := by
    intro g hg
    simpa using (hasProd_nat_add_iff _).mp hg
  (this (fun n => f n) hpos).nonneg_add_neg hneg
#align has_prod.pos_add_zero_add_neg HasProd.pos_mul_zero_mul_neg
#align has_sum.pos_mul_zero_add_neg HasSum.pos_add_zero_add_neg

@[to_additive summable_int_of_summable_nat]
theorem multipliable_int_of_multipliable_nat {f : ℤ → α} (hp : Multipliable fun n : ℕ => f n)
    (hn : Multipliable fun n : ℕ => f (-n)) : Multipliable f :=
  (HasProd.nonneg_add_neg hp.hasProd <|
      Multipliable.hasProd <| (multipliable_nat_add_iff 1).mpr hn).multipliable
#align multipliable_int_of_multipliable_nat multipliable_int_of_multipliable_nat
#align summable_int_of_summable_nat summable_int_of_summable_nat

@[to_additive]
theorem HasProd.prod_nat_of_prod_int {α : Type _} [CommMonoid α] [TopologicalSpace α]
    [ContinuousMul α] {a : α} {f : ℤ → α} (hf : HasProd f a) :
    HasProd (fun n : ℕ => f n * f (-n)) (a * f 0) := by
  apply (hf.mul (hasProd_ite_eq (0 : ℤ) (f 0))).hasProd_of_prod_eq fun u => ?_
  refine' ⟨u.image Int.natAbs, fun v' hv' => _⟩
  let u1 := v'.image fun x : ℕ => (x : ℤ)
  let u2 := v'.image fun x : ℕ => -(x : ℤ)
  have A : u ⊆ u1 ∪ u2 := by
    intro x hx
    simp only [mem_union, mem_image, exists_prop]
    rcases le_total 0 x with (h'x | h'x)
    · left
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [h'x, Int.coe_natAbs, abs_eq_self]
    · right
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [abs_of_nonpos h'x, Int.coe_natAbs, neg_neg]
  refine' ⟨u1 ∪ u2, A, _⟩
  calc
    ∏ x in u1 ∪ u2, f x * ite (x = 0) (f 0) 1 = (∏ x in u1 ∪ u2, f x) * ∏ x in u1 ∩ u2, f x :=
      by
      rw [prod_mul_distrib]
      congr 1
      refine' (prod_subset_one_on_sdiff inter_subset_union _ _).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simp only [mem_sdiff, mem_union, mem_image, neg_eq_zero, or_self_iff, mem_inter,
          and_self_iff, and_not_self_iff] at hx
      · intro x hx
        simp only [mem_inter, mem_image, exists_prop] at hx 
        have : x = 0 := by
          apply le_antisymm
          · rcases hx.2 with ⟨a, _, rfl⟩
            simp only [Right.neg_nonpos_iff, Nat.cast_nonneg]
          · rcases hx.1 with ⟨a, _, rfl⟩
            simp only [Nat.cast_nonneg]
        simp only [this, eq_self_iff_true, if_true]
    _ = (∏ x in u1, f x) * ∏ x in u2, f x := prod_union_inter
    _ = (∏ b in v', f b) * ∏ b in v', f (-b) := by
      simp only [prod_image, Nat.cast_inj, imp_self, imp_true_iff, neg_inj]
    _ = ∏ b in v', f b * f (-b) := prod_mul_distrib.symm 
#align has_prod.prod_nat_of_prod_int HasProd.prod_nat_of_prod_int
#align has_sum.sum_nat_of_sum_int HasSum.sum_nat_of_sum_int

end Nat

end TopologicalGroup

section UniformGroup

variable [CommGroup α]

variable [UniformSpace α]

/-- The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test** -/
@[to_additive summable_iff_cauchySeq_finset
      "The **Cauchy criterion** for infinite products, also known as the **Cauchy convergence test**"]
theorem multipliable_iff_cauchySeq_finset [CompleteSpace α] {f : β → α} :
    Multipliable f ↔ CauchySeq fun s : Finset β => ∏ b in s, f b :=
  cauchy_map_iff_exists_tendsto.symm
#align multipliable_iff_cauchy_seq_finset multipliable_iff_cauchySeq_finset
#align summable_iff_cauchy_seq_finset summable_iff_cauchySeq_finset

variable [UniformGroup α]

variable {f g : β → α} {a a₁ a₂ : α}

@[to_additive cauchySeq_finset_iff_vanishing]
theorem cauchySeq_finset_iff_mul_vanishing : (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → ∏ b in t, f b ∈ e := by
  simp only [CauchySeq, cauchy_map_iff, and_iff_right atTop_neBot, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, (· ∘ ·)]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.prod_union ht.symm, mul_div_cancel'''] using h
  · intro h e he
    rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : (∏ b in t₂, f b) / ∏ b in t₁, f b = (∏ b in t₂ \ s, f b) / ∏ b in t₁ \ s, f b := by
      rw [← Finset.prod_sdiff ht₁, ← Finset.prod_sdiff ht₂, mul_div_mul_right_eq_div]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)
#align cauchy_seq_finset_iff_mul_vanishing cauchySeq_finset_iff_mul_vanishing
#align cauchy_seq_finset_iff_vanishing cauchySeq_finset_iff_vanishing

/-- The product over the complement of a finset tends to `1` when the finset grows
to cover the whole space. This does not need a multipliability assumption,
as otherwise all sums are zero. -/
@[to_additive tendsto_tsum_compl_atTop_zero
      "The sum over the complement of a finset tends to `0` when the finset grows to cover the whole\nspace. This does not need a summability assumption, as otherwise all sums are zero"]
theorem tendsto_tprod_compl_atTop_one (f : β → α) :
    Tendsto (fun s : Finset β => ∏' b : { x // x ∉ s }, f b) atTop (𝓝 1) := by
  by_cases H : Multipliable f
  · intro e he
    rcases exists_mem_nhds_isClosed_subset he with ⟨o, ho, o_closed, oe⟩
    simp only [le_eq_subset, Set.mem_preimage, mem_atTop_sets, Filter.mem_map, ge_iff_le]
    obtain ⟨s, hs⟩ : ∃ s : Finset β, ∀ t : Finset β, Disjoint t s → (∏ b : β in t, f b) ∈ o :=
      cauchySeq_finset_iff_mul_vanishing.1 (Tendsto.cauchySeq H.hasProd) o ho
    refine' ⟨s, fun a sa => oe _⟩
    have A : Multipliable fun b : { x // x ∉ a } => f b := a.multipliable_compl_iff.2 H
    refine' IsClosed.mem_of_tendsto o_closed A.hasProd (eventually_of_forall fun b => _)
    have : Disjoint (Finset.image (fun i : { x // x ∉ a } => (i : β)) b) s := by
      refine' disjoint_left.2 fun i hi his => _
      rcases mem_image.1 hi with ⟨i', _, rfl⟩
      exact i'.2 (sa his)
    convert hs _ this using 1
    rw [prod_image]
    intro i _ j _ hij
    exact Subtype.ext hij
  · convert tendsto_const_nhds (α := α) (β := Finset β) (f := atTop) (a := 1)
    apply tprod_eq_one_of_not_multipliable
    rwa [Finset.multipliable_compl_iff]
#align tendsto_tprod_compl_at_top_one tendsto_tprod_compl_atTop_one
#align tendsto_tsum_compl_at_top_zero tendsto_tsum_compl_atTop_zero

variable [CompleteSpace α]

@[to_additive summable_iff_vanishing]
theorem multipliable_iff_mul_vanishing :
    Multipliable f ↔ ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → ∏ b in t, f b ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_mul_vanishing]
#align multipliable_iff_mul_vanishing multipliable_iff_mul_vanishing
#align summable_iff_vanishing summable_iff_vanishing

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
@[to_additive Summable.summable_of_eq_zero_or_self]
theorem Multipliable.multipliable_of_eq_one_or_self (hf : Multipliable f)
    (h : ∀ b, g b = 1 ∨ g b = f b) : Multipliable g :=
  multipliable_iff_mul_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := multipliable_iff_mul_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : ∏ b in t.filter fun b => g b = f b, f b = ∏ b in t, g b :=
        calc
          ∏ b in t.filter fun b => g b = f b, f b = ∏ b in t.filter fun b => g b = f b, g b :=
            Finset.prod_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b in t, g b :=
            by
            refine' Finset.prod_subset (Finset.filter_subset _ _) _
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb
      eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩
#align multipliable.multipliable_of_eq_one_or_self Multipliable.multipliable_of_eq_one_or_self
#align summable.summable_of_eq_zero_or_self Summable.summable_of_eq_zero_or_self

@[to_additive]
protected theorem Multipliable.mulIndicator (hf : Multipliable f) (s : Set β) :
    Multipliable (s.mulIndicator f) :=
  hf.multipliable_of_eq_one_or_self <| Set.mulIndicator_eq_one_or_self _ _
#align multipliable.mul_indicator Multipliable.mulIndicator
#align summable.indicator Summable.indicator

@[to_additive]
theorem Multipliable.comp_injective {i : γ → β} (hf : Multipliable f) (hi : Injective i) :
    Multipliable (f ∘ i) := by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx => Set.mulIndicator_of_not_mem hx _)).2 
    (hf.mulIndicator (Set.range i))
#align multipliable.comp_injective Multipliable.comp_injective
#align summable.comp_injective Summable.comp_injective

@[to_additive]
theorem Multipliable.subtype (hf : Multipliable f) (s : Set β) : Multipliable (f ∘ (↑) : s → α) :=
  hf.comp_injective Subtype.coe_injective
#align multipliable.subtype Multipliable.subtype
#align summable.subtype Summable.subtype

@[to_additive summable_subtype_and_compl]
theorem multipliable_subtype_and_compl {s : Set β} :
    ((Multipliable fun x : s => f x) ∧ Multipliable fun x : (sᶜ : Set β) => f x) ↔ Multipliable f :=
  ⟨and_imp.2 Multipliable.mul_compl, fun h => ⟨h.subtype s, h.subtype (sᶜ)⟩⟩
#align multipliable_subtype_and_compl multipliable_subtype_and_compl
#align summable_subtype_and_compl summable_subtype_and_compl

@[to_additive]
theorem Multipliable.sigma_factor {γ : β → Type _} {f : (Σ b : β, γ b) → α} (ha : Multipliable f)
    (b : β) : Multipliable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective
#align multipliable.sigma_factor Multipliable.sigma_factor
#align summable.sigma_factor Summable.sigma_factor

@[to_additive]
theorem Multipliable.sigma {γ : β → Type _} {f : (Σ b : β, γ b) → α} (ha : Multipliable f) :
    Multipliable fun b => ∏' c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b
#align multipliable.sigma Multipliable.sigma
#align summable.sigma Summable.sigma

@[to_additive]
theorem Multipliable.prod_factor {f : β × γ → α} (h : Multipliable f) (b : β) :
    Multipliable fun c => f (b, c) :=
  h.comp_injective fun _ _ h => (Prod.ext_iff.1 h).2
#align multipliable.prod_factor Multipliable.prod_factor
#align summable.sum_factor Summable.sum_factor

section LocInstances

-- enable inferring a T3-topological space from a topological group
attribute [local instance] TopologicalGroup.t3Space

-- enable inferring a T3-topological space from a topological add group
attribute [local instance] TopologicalAddGroup.t3Space

-- disable getting a T0-space from a T1-space as this causes loops
attribute [-instance] T1Space.t0Space

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
@[to_additive tsum_sigma]
theorem tprod_sigma [T0Space α] {γ : β → Type _} {f : (Σ b : β, γ b) → α} (ha : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  tprod_sigma' (fun b => ha.sigma_factor b) ha
#align tprod_sigma tprod_sigma
#align tsum_sigma tsum_sigma

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
@[to_additive tsum_prod]
theorem tprod_on_prod [T0Space α] {f : β × γ → α} (h : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  tprod_prod' h h.prod_factor
#align tprod_on_prod tprod_on_prod
#align tsum_prod tsum_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (c b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b c) -/
@[to_additive tsum_comm]
theorem tprod_comm [T0Space α] {f : β → γ → α} (h : Multipliable (Function.uncurry f)) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c :=
  tprod_comm' h h.prod_factor h.prod_symm.prod_factor
#align tprod_comm tprod_comm
#align tsum_comm tsum_comm

end LocInstances

@[to_additive tsum_subtype_add_tsum_subtype_compl]
theorem tprod_subtype_mul_tprod_subtype_compl [T2Space α] {f : β → α} (hf : Multipliable f)
    (s : Set β) : (∏' x : s, f x) * ∏' x : (sᶜ : Set β), f x = ∏' x, f x :=
  ((hf.subtype s).hasProd.mul_compl (hf.subtype {x | x ∉ s}).hasProd).unique hf.hasProd
#align tprod_subtype_mul_tprod_subtype_compl tprod_subtype_mul_tprod_subtype_compl
#align tsum_subtype_add_tsum_subtype_compl tsum_subtype_add_tsum_subtype_compl

@[to_additive sum_add_tsum_subtype_compl]
theorem prod_mul_tprod_subtype_compl [T2Space α] {f : β → α} (hf : Multipliable f) (s : Finset β) :
    (∏ x in s, f x) * ∏' x : { x // x ∉ s }, f x = ∏' x, f x := by
  rw [← tprod_subtype_mul_tprod_subtype_compl hf s]
  simp only [Finset.tprod_subtype', add_right_inj]
  rfl
#align prod_mul_tprod_subtype_compl prod_mul_tprod_subtype_compl
#align sum_add_tsum_subtype_compl sum_add_tsum_subtype_compl

end UniformGroup

section TopologicalGroup

variable {G : Type _} [TopologicalSpace G]

variable [CommGroup G] [TopologicalGroup G]

variable {f : α → G}

@[to_additive]
theorem Multipliable.mul_vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (1 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → ∏ k in t, f k ∈ e :=
  by
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  letI : UniformGroup G := comm_topologicalGroup_is_uniform
  rcases hf with ⟨y, hy⟩
  exact cauchySeq_finset_iff_mul_vanishing.1 hy.cauchySeq e he
#align multipliable.mul_vanishing Multipliable.mul_vanishing
#align summable.add_vanishing Summable.add_vanishing

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
@[to_additive]
theorem Multipliable.tendsto_cofinite_one (hf : Multipliable f) : Tendsto f cofinite (𝓝 1) :=
  by
  intro e he
  rw [Filter.mem_map]
  rcases hf.mul_vanishing he with ⟨s, hs⟩
  refine' s.eventually_cofinite_nmem.mono fun x hx => _
  · simpa using hs {x} (disjoint_singleton_left.2 hx)
#align multipliable.tendsto_cofinite_one Multipliable.tendsto_cofinite_one
#align summable.tendsto_cofinite_zero Summable.tendsto_cofinite_zero

@[to_additive]
theorem Multipliable.tendsto_atTop_one {f : ℕ → G} (hf : Multipliable f) : Tendsto f atTop (𝓝 1) :=
  by rw [← Nat.cofinite_eq_atTop]; exact hf.tendsto_cofinite_one
#align multipliable.tendsto_at_top_one Multipliable.tendsto_atTop_one
#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zero

end TopologicalGroup

section ConstSmul

variable [Monoid γ] [TopologicalSpace α] [AddCommMonoid α] [DistribMulAction γ α]
  [ContinuousConstSMul γ α] {f : β → α}

theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a) : HasSum (fun i => b • f i) (b • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α _) <| continuous_const_smul _
#align has_sum.const_smul HasSum.const_smul

theorem Summable.const_smul (b : γ) (hf : Summable f) : Summable fun i => b • f i :=
  (hf.hasSum.const_smul _).summable
#align summable.const_smul Summable.const_smul

theorem tsum_const_smul [T2Space α] (b : γ) (hf : Summable f) : ∑' i, b • f i = b • ∑' i, f i :=
  (hf.hasSum.const_smul _).tsum_eq
#align tsum_const_smul tsum_const_smul

end ConstSmul

/-! ### Product and pi types -/


section Prod

variable [CommMonoid α] [CommMonoid γ]

variable [TopologicalSpace α] [TopologicalSpace γ]

@[to_additive HasSum.prod_mk]
theorem HasProd.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasProd f a)
    (hg : HasProd g b) : HasProd (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ := by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prod_mk_nhds hf hg]
#align has_prod.prod_mk HasProd.prod_mk
#align has_sum.prod_mk HasSum.prod_mk

end Prod

section Pi

variable {ι : Type _} {π : α → Type _} [∀ x, TopologicalSpace (π x)]

variable [∀ x, CommMonoid (π x)]

@[to_additive]
theorem Pi.hasProd {f : ι → ∀ x, π x} {g : ∀ x, π x} :
    HasProd f g ↔ ∀ x, HasProd (fun i => f i x) (g x) := by
  simp only [HasProd, tendsto_pi_nhds, prod_apply]
#align pi.has_prod Pi.hasProd
#align pi.has_sum Pi.hasSum

@[to_additive Pi.summable]
theorem Pi.multipliable {f : ι → ∀ x, π x} : Multipliable f ↔ ∀ x, Multipliable fun i => f i x := by
  simp only [Multipliable, Pi.hasProd, skolem]
#align pi.multipliable Pi.multipliable
#align pi.summable Pi.summable

@[to_additive tsum_apply]
theorem tprod_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Multipliable f) :
    (∏' i, f i) x = ∏' i, f i x :=
  (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm
#align tprod_apply tprod_apply
#align tsum_apply tsum_apply

end Pi

/-! ### Multiplicative opposite -/


-- No obvious multiplicative version
section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α} {a : α}

theorem HasSum.op (hf : HasSum f a) : HasSum (fun a => op (f a)) (op a) :=
  (hf.map (@opAddEquiv α _) continuous_op : _)
#align has_sum.op HasSum.op

theorem Summable.op (hf : Summable f) : Summable (op ∘ f) :=
  hf.hasSum.op.summable
#align summable.op Summable.op

theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a) :
    HasSum (fun a => unop (f a)) (unop a) :=
  (hf.map (@opAddEquiv α _).symm continuous_unop : _)
#align has_sum.unop HasSum.unop

theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f) : Summable (unop ∘ f) :=
  hf.hasSum.unop.summable
#align summable.unop Summable.unop

@[simp]
theorem hasSum_op : HasSum (fun a => op (f a)) (op a) ↔ HasSum f a :=
  ⟨HasSum.unop, HasSum.op⟩
#align has_sum_op hasSum_op

@[simp]
theorem hasSum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a => unop (f a)) (unop a) ↔ HasSum f a :=
  ⟨HasSum.op, HasSum.unop⟩
#align has_sum_unop hasSum_unop

@[simp]
theorem summable_op : (Summable fun a => op (f a)) ↔ Summable f :=
  ⟨Summable.unop, Summable.op⟩
#align summable_op summable_op

-- Porting note: This theorem causes a loop easily in Lean 4, so the priority should be `low`.
@[simp low]
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable fun a => unop (f a)) ↔ Summable f :=
  ⟨Summable.op, Summable.unop⟩
#align summable_unop summable_unop

variable [T2Space α]

theorem tsum_op : ∑' x, MulOpposite.op (f x) = MulOpposite.op (∑' x, f x) := by
  by_cases h : Summable f
  · exact h.hasSum.op.tsum_eq
  · have ho := summable_op.not.mpr h
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, MulOpposite.op_zero]
#align tsum_op tsum_op

theorem tsum_unop {f : β → αᵐᵒᵖ} : ∑' x, MulOpposite.unop (f x) = MulOpposite.unop (∑' x, f x) :=
  MulOpposite.op_injective tsum_op.symm
#align tsum_unop tsum_unop

end MulOpposite

/-! ### Interaction with the star -/


-- No obvious multiplicative version
section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

theorem HasSum.star (h : HasSum f a) : HasSum (fun b => star (f b)) (star a) := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star
#align has_sum.star HasSum.star

theorem Summable.star (hf : Summable f) : Summable fun b => star (f b) :=
  hf.hasSum.star.summable
#align summable.star Summable.star

theorem Summable.ofStar (hf : Summable fun b => Star.star (f b)) : Summable f := by
  simpa only [star_star] using hf.star
#align summable.of_star Summable.ofStar

@[simp]
theorem summable_star_iff : (Summable fun b => star (f b)) ↔ Summable f :=
  ⟨Summable.ofStar, Summable.star⟩
#align summable_star_iff summable_star_iff

@[simp]
theorem summable_star_iff' : Summable (star f) ↔ Summable f :=
  summable_star_iff
#align summable_star_iff' summable_star_iff'

variable [T2Space α]

theorem tsum_star : star (∑' b, f b) = ∑' b, star (f b) := by
  by_cases hf : Summable f
  · exact hf.hasSum.star.tsum_eq.symm
  · rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.ofStar hf),
      star_zero]
#align tsum_star tsum_star

end ContinuousStar
