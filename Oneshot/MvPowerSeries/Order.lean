import Mathbin.RingTheory.PowerSeries.Basic

namespace MvPowerSeries

noncomputable section

open ENat WithTop

open scoped BigOperators

variable {σ α : Type _} [Semiring α]

theorem coeff_apply (f : MvPowerSeries σ α) (d : σ →₀ ℕ) : coeff α d f = f d :=
  rfl
#align mv_power_series.coeff_apply MvPowerSeries.coeff_apply

theorem exists_coeff_ne_zero_iff_ne_zero (f : MvPowerSeries σ α) :
    (∃ d : σ →₀ ℕ, coeff α d f ≠ 0) ↔ f ≠ 0 := by
  simp only [ext_iff, Ne.def, coeff_zero, not_forall]
#align mv_power_series.exists_coeff_ne_zero_iff_ne_zero MvPowerSeries.exists_coeff_ne_zero_iff_ne_zero

section WeightedOrder

variable (w : σ → ℕ)

variable (f : MvPowerSeries σ α)

/-- The weight of a monomial -/
def weight : (σ →₀ ℕ) →+ ℕ where
  toFun d := d.Sum fun x y => w x * y
  map_zero' := Finsupp.sum_zero_index
  map_add' x y := by
    rw [Finsupp.sum_add_index']
    · intro i; rw [MulZeroClass.mul_zero]
    · intro i m n; rw [mul_add]
#align mv_power_series.weight MvPowerSeries.weight

theorem weight_apply (d : σ →₀ ℕ) : weight w d = d.Sum fun x => Mul.mul (w x) := by
  simp only [weight] <;> rfl
#align mv_power_series.weight_apply MvPowerSeries.weight_apply

theorem le_weight (x : σ) (hx : w x ≠ 0) (d : σ →₀ ℕ) : d x ≤ weight w d := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases hxd : x ∈ d.support
  · rw [Finset.sum_eq_add_sum_diff_singleton hxd]
    refine' le_trans _ (Nat.le_add_right _ _)
    exact Nat.le_mul_of_pos_left (zero_lt_iff.mpr hx)
  simp only [Finsupp.mem_support_iff, Classical.not_not] at hxd 
  rw [hxd]
  apply zero_le
#align mv_power_series.le_weight MvPowerSeries.le_weight

theorem finite_of_weight_le [Finite σ] (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {f : σ →₀ ℕ | weight w f ≤ n}.Finite := by
  classical
  let fg := Finsupp.antidiagonal (finsupp.equiv_fun_on_finite.symm (Function.const σ n))
  suffices : {f : σ →₀ ℕ | weight w f ≤ n} ⊆ ↑(fg.image fun uv => uv.fst)
  apply Set.Finite.subset _ this
  apply Finset.finite_toSet
  intro f hf
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_antidiagonal, Prod.exists,
    exists_and_right, exists_eq_right]
  use finsupp.equiv_fun_on_finite.symm (Function.const σ n) - f
  ext x
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.equivFunOnFinite_symm_apply_to_fun, Function.const_apply]
  rw [add_comm]
  apply Nat.sub_add_cancel
  apply le_trans (le_weight w x (hw x) f)
  simpa only [Set.mem_setOf_eq] using hf
#align mv_power_series.finite_of_weight_le MvPowerSeries.finite_of_weight_le

theorem exists_coeff_ne_zero_of_weight_iff_ne_zero :
    (∃ n : ℕ, ∃ d : σ →₀ ℕ, weight w d = n ∧ coeff α d f ≠ 0) ↔ f ≠ 0 :=
  by
  refine' not_iff_not.mp _
  push_neg
  constructor
  · intro h; ext d
    exact h _ d rfl
  · rintro rfl n d hn; exact coeff_zero _
#align mv_power_series.exists_coeff_ne_zero_of_weight_iff_ne_zero MvPowerSeries.exists_coeff_ne_zero_of_weight_iff_ne_zero

/-- The weighted order of a mv_power_series -/
def weightedOrder (f : MvPowerSeries σ α) : ℕ∞ := by
  classical exact
    dite (f = 0) (fun h => ⊤) fun h =>
      Nat.find ((exists_coeff_ne_zero_of_weight_iff_ne_zero w f).mpr h)
#align mv_power_series.weighted_order MvPowerSeries.weightedOrder

@[simp]
theorem weightedOrder_zero : (0 : MvPowerSeries σ α).weightedOrder w = ⊤ := by
  simp only [weighted_order, dif_pos rfl]
#align mv_power_series.weighted_order_zero MvPowerSeries.weightedOrder_zero

theorem weightedOrder_finite_iff_ne_zero :
    ↑(toNat (f.weightedOrder w)) = f.weightedOrder w ↔ f ≠ 0 :=
  by
  simp only [weighted_order]
  constructor
  · split_ifs with h h <;> intro H
    · simp only [to_nat_top, ENat.coe_zero, zero_ne_top] at H 
      exfalso <;> exact H
    · exact h
  · intro h
    simp only [h, not_false_iff, dif_neg, to_nat_coe]
#align mv_power_series.weighted_order_finite_iff_ne_zero MvPowerSeries.weightedOrder_finite_iff_ne_zero

/-- If the order of a formal power series `f` is finite,
then some coefficient of weight equal to the order of `f` is nonzero.-/
theorem exists_coeff_ne_zero_of_weightedOrder
    (h : ↑(toNat (f.weightedOrder w)) = f.weightedOrder w) :
    ∃ d : σ →₀ ℕ, ↑(weight w d) = f.weightedOrder w ∧ coeff α d f ≠ 0 :=
  by
  simp_rw [weighted_order, dif_neg ((weighted_order_finite_iff_ne_zero _ f).mp h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1
#align mv_power_series.exists_coeff_ne_zero_of_weighted_order MvPowerSeries.exists_coeff_ne_zero_of_weightedOrder

/-- If the `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w`.-/
theorem weightedOrder_le {d : σ →₀ ℕ} (h : coeff α d f ≠ 0) : f.weightedOrder w ≤ weight w d :=
  by
  have := Exists.intro d h
  rw [weighted_order, dif_neg]
  · simp only [WithTop.coe_le_coe, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, rfl, h⟩
  · exact (f.exists_coeff_ne_zero_of_weight_iff_ne_zero w).mp ⟨weight w d, d, rfl, h⟩
#align mv_power_series.weighted_order_le MvPowerSeries.weightedOrder_le

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_weightedOrder {d : σ →₀ ℕ} (h : ↑(weight w d) < f.weightedOrder w) :
    coeff α d f = 0 := by contrapose! h; exact weighted_order_le w f h
#align mv_power_series.coeff_of_lt_weighted_order MvPowerSeries.coeff_of_lt_weightedOrder

/-- The `0` power series is the unique power series with infinite order.-/
@[simp]
theorem weightedOrder_eq_top_iff {f : MvPowerSeries σ α} : f.weightedOrder w = ⊤ ↔ f = 0 :=
  by
  constructor
  · intro h; ext d;
    simp only [(coeff α d).map_zero, coeff_of_lt_weighted_order w, h, WithTop.coe_lt_top]
  · rintro rfl; exact weighted_order_zero w
#align mv_power_series.weighted_order_eq_top_iff MvPowerSeries.weightedOrder_eq_top_iff

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
theorem nat_le_weightedOrder {f : MvPowerSeries σ α} {n : ℕ}
    (h : ∀ d, weight w d < n → coeff α d f = 0) : ↑n ≤ f.weightedOrder w :=
  by
  by_contra H; rw [not_le] at H 
  have : ↑(toNat (f.weighted_order w)) = f.weighted_order w := by rw [coe_to_nat_eq_self];
    exact ne_top_of_lt H
  obtain ⟨d, hd, hfd⟩ := exists_coeff_ne_zero_of_weighted_order w f this
  simp only [← hd, WithTop.coe_lt_coe] at H 
  exact hfd (h d H)
#align mv_power_series.nat_le_weighted_order MvPowerSeries.nat_le_weightedOrder

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
theorem le_weightedOrder {f : MvPowerSeries σ α} {n : ℕ∞}
    (h : ∀ d : σ →₀ ℕ, ↑(weight w d) < n → coeff α d f = 0) : n ≤ f.weightedOrder w :=
  by
  cases n
  · rw [none_eq_top, top_le_iff, weighted_order_eq_top_iff]
    ext d; exact h d (coe_lt_top _)
  · rw [some_eq_coe] at h ⊢
    apply nat_le_weighted_order; simpa only [WithTop.coe_lt_coe] using h
#align mv_power_series.le_weighted_order MvPowerSeries.le_weightedOrder

/-- The order of a formal power series is exactly `n` if and only if some coefficient of weight `n`
is nonzero, and the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
theorem weightedOrder_eq_nat {f : MvPowerSeries σ α} {n : ℕ} :
    f.weightedOrder w = n ↔
      (∃ d, weight w d = n ∧ coeff α d f ≠ 0) ∧ ∀ d, weight w d < n → coeff α d f = 0 :=
  by
  rcases eq_or_ne f 0 with (rfl | hf)
  ·
    simp only [weighted_order_zero, top_ne_nat, coeff_zero, Ne.def, eq_self_iff_true, not_true,
      and_false_iff, exists_false, false_and_iff]
  · simp only [weighted_order, dif_neg hf, coe_eq_coe, Nat.find_eq_iff]
    apply and_congr_right'
    simp only [not_exists, not_and, Classical.not_not, imp_forall_iff]
    rw [forall_swap]
    apply forall_congr'
    intro d
    constructor
    · intro h hd
      exact h (weight w d) hd rfl
    · intro h m hm hd; rw [← hd] at hm ; exact h hm
#align mv_power_series.weighted_order_eq_nat MvPowerSeries.weightedOrder_eq_nat

/-- The order of the sum of two formal power series is at least the minimum of their orders.-/
theorem le_weightedOrder_add (f g : MvPowerSeries σ α) :
    min (f.weightedOrder w) (g.weightedOrder w) ≤ (f + g).weightedOrder w :=
  by
  refine' le_weighted_order w _
  simp (config := { contextual := true }) only [coeff_of_lt_weighted_order w, lt_min_iff, map_add,
    add_zero, eq_self_iff_true, imp_true_iff]
#align mv_power_series.le_weighted_order_add MvPowerSeries.le_weightedOrder_add

private theorem weighted_order_add_of_weighted_order_lt.aux {f g : MvPowerSeries σ α}
    (H : f.weightedOrder w < g.weightedOrder w) : (f + g).weightedOrder w = f.weightedOrder w :=
  by
  obtain ⟨n, hn⟩ := ne_top_iff_exists.mp (ne_top_of_lt H)
  rw [← hn]
  rw [weighted_order_eq_nat]
  obtain ⟨d, hd, hd'⟩ := ((weighted_order_eq_nat w).mp hn.symm).1
  constructor
  · use d; use hd
    rw [← hn, ← hd] at H 
    rw [(coeff _ _).map_add, coeff_of_lt_weighted_order w g H, add_zero]
    exact hd'
  · intro b hb
    suffices ↑(weight w b) < weighted_order w f by
      rw [(coeff _ _).map_add, coeff_of_lt_weighted_order w f this,
        coeff_of_lt_weighted_order w g (lt_trans this H), add_zero]
    rw [← hn, coe_lt_coe]; exact hb

/-- The weighted_order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem weightedOrder_add_of_weightedOrder_eq {f g : MvPowerSeries σ α}
    (h : f.weightedOrder w ≠ g.weightedOrder w) :
    weightedOrder w (f + g) = weightedOrder w f ⊓ weightedOrder w g :=
  by
  refine' le_antisymm _ (le_weighted_order_add w _ _)
  by_cases H₁ : f.weighted_order w < g.weighted_order w
  · simp only [le_inf_iff, weighted_order_add_of_weighted_order_lt.aux w H₁]
    exact ⟨le_rfl, le_of_lt H₁⟩
  · by_cases H₂ : g.weighted_order w < f.weighted_order w
    · simp only [add_comm f g, le_inf_iff, weighted_order_add_of_weighted_order_lt.aux w H₂]
      exact ⟨le_of_lt H₂, le_rfl⟩
    · exact absurd (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁)) h
#align mv_power_series.weighted_order_add_of_weighted_order_eq MvPowerSeries.weightedOrder_add_of_weightedOrder_eq

/-- The weighted_order of the product of two formal power series
 is at least the sum of their orders.-/
theorem weightedOrder_mul_ge (f g : MvPowerSeries σ α) :
    f.weightedOrder w + g.weightedOrder w ≤ weightedOrder w (f * g) :=
  by
  apply le_weighted_order
  intro d hd; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases hi : ↑(weight w i) < f.weighted_order w
  · rw [coeff_of_lt_weighted_order w f hi, MulZeroClass.zero_mul]
  · by_cases hj : ↑(weight w j) < g.weighted_order w
    · rw [coeff_of_lt_weighted_order w g hj, MulZeroClass.mul_zero]
    · rw [not_lt] at hi hj 
      simp only [Finsupp.mem_antidiagonal] at hij 
      exfalso
      apply ne_of_lt (lt_of_lt_of_le hd <| add_le_add hi hj)
      rw [← hij, map_add, Nat.cast_add]
#align mv_power_series.weighted_order_mul_ge MvPowerSeries.weightedOrder_mul_ge

/-- The weighted_order of the monomial `a*X^d` is infinite if `a = 0` and `weight w d` otherwise.-/
theorem weightedOrder_monomial (d : σ →₀ ℕ) (a : α) [Decidable (a = 0)] :
    weightedOrder w (monomial α d a) = if a = 0 then ⊤ else weight w d :=
  by
  split_ifs with h
  · rw [h, weighted_order_eq_top_iff, LinearMap.map_zero]
  · rw [weighted_order_eq_nat]
    constructor
    · use d; simp only [coeff_monomial_same, eq_self_iff_true, Ne.def, true_and_iff]; exact h
    · intro b hb; rw [coeff_monomial, if_neg]
      intro h; simpa only [h, lt_self_iff_false] using hb
#align mv_power_series.weighted_order_monomial MvPowerSeries.weightedOrder_monomial

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem weightedOrder_monomial_of_ne_zero (d : σ →₀ ℕ) (a : α) (h : a ≠ 0) :
    weightedOrder w (monomial α d a) = weight w d := by rw [weighted_order_monomial, if_neg h]
#align mv_power_series.weighted_order_monomial_of_ne_zero MvPowerSeries.weightedOrder_monomial_of_ne_zero

/-- If `weight w d` is strictly smaller than the weighted_order of `g`, then the `d`th coefficient 
of its product with any other power series is `0`. -/
theorem coeff_mul_of_lt_weightedOrder (f : MvPowerSeries σ α) {g : MvPowerSeries σ α} {d : σ →₀ ℕ}
    (h : ↑(weight w d) < g.weightedOrder w) : coeff α d (f * g) = 0 :=
  by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  refine' mul_eq_zero_of_right (coeff α i f) _
  refine' coeff_of_lt_weighted_order w g (lt_of_le_of_lt _ h)
  simp only [Finsupp.mem_antidiagonal] at hij 
  simp only [coe_le_coe, ← hij, map_add, le_add_iff_nonneg_left, zero_le']
#align mv_power_series.coeff_mul_of_lt_weighted_order MvPowerSeries.coeff_mul_of_lt_weightedOrder

theorem coeff_mul_one_sub_of_lt_weightedOrder {α : Type _} [CommRing α] {f g : MvPowerSeries σ α}
    (d : σ →₀ ℕ) (h : ↑(weight w d) < g.weightedOrder w) : coeff α d (f * (1 - g)) = coeff α d f :=
  by simp only [coeff_mul_of_lt_weighted_order w f h, mul_sub, mul_one, _root_.map_sub, sub_zero]
#align mv_power_series.coeff_mul_one_sub_of_lt_weighted_order MvPowerSeries.coeff_mul_one_sub_of_lt_weightedOrder

theorem coeff_mul_prod_one_sub_of_lt_weightedOrder {α ι : Type _} [CommRing α] (d : σ →₀ ℕ)
    (s : Finset ι) (f : MvPowerSeries σ α) (g : ι → MvPowerSeries σ α) :
    (∀ i ∈ s, ↑(weight w d) < weightedOrder w (g i)) →
      coeff α d (f * ∏ i in s, (1 - g i)) = coeff α d f :=
  by
  apply Finset.induction_on s
  · simp only [imp_true_iff, Finset.prod_empty, mul_one, eq_self_iff_true]
  · intro a s ha ih t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t 
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm,
      coeff_mul_one_sub_of_lt_weighted_order w _ t.1]
    exact ih t.2
#align mv_power_series.coeff_mul_prod_one_sub_of_lt_weighted_order MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder

end WeightedOrder

section Order

variable (f : MvPowerSeries σ α)

/-- The degree of a monomial -/
def degree : (σ →₀ ℕ) →+ ℕ :=
  weight fun i => 1
#align mv_power_series.degree MvPowerSeries.degree

theorem degree_apply (d : σ →₀ ℕ) : degree d = d.Sum fun x => id :=
  by
  simp only [degree, weight_apply]
  apply congr_arg
  ext x
  simp only [one_mul, id.def]
#align mv_power_series.degree_apply MvPowerSeries.degree_apply

theorem degree_eq_zero_iff (d : σ →₀ ℕ) : degree d = 0 ↔ d = 0 :=
  by
  simp only [degree, weight, one_mul, AddMonoidHom.coe_mk]
  simp only [Finsupp.sum, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, not_imp_self]
  simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]
#align mv_power_series.degree_eq_zero_iff MvPowerSeries.degree_eq_zero_iff

theorem le_degree (x : σ) (d : σ →₀ ℕ) : d x ≤ degree d :=
  by
  convert le_weight _ x _ d
  exact NeZero.ne 1
#align mv_power_series.le_degree MvPowerSeries.le_degree

theorem finite_of_degree_le [Finite σ] (n : ℕ) : {f : σ →₀ ℕ | degree f ≤ n}.Finite :=
  by
  refine' finite_of_weight_le (Function.const σ 1) _ n
  simp only [Ne.def, Nat.one_ne_zero, not_false_iff, imp_true_iff]
#align mv_power_series.finite_of_degree_le MvPowerSeries.finite_of_degree_le

theorem exists_coeff_ne_zero_of_degree_iff_ne_zero :
    (∃ n : ℕ, ∃ d : σ →₀ ℕ, degree d = n ∧ coeff α d f ≠ 0) ↔ f ≠ 0 :=
  exists_coeff_ne_zero_of_weight_iff_ne_zero (fun i => 1) f
#align mv_power_series.exists_coeff_ne_zero_of_degree_iff_ne_zero MvPowerSeries.exists_coeff_ne_zero_of_degree_iff_ne_zero

/-- The order of a mv_power_series -/
def order (f : MvPowerSeries σ α) : ℕ∞ :=
  weightedOrder (fun i => 1) f
#align mv_power_series.order MvPowerSeries.order

@[simp]
theorem order_zero : (0 : MvPowerSeries σ α).order = ⊤ :=
  weightedOrder_zero _
#align mv_power_series.order_zero MvPowerSeries.order_zero

theorem order_finite_iff_ne_zero : ↑(toNat f.order) = f.order ↔ f ≠ 0 :=
  weightedOrder_finite_iff_ne_zero _ f
#align mv_power_series.order_finite_iff_ne_zero MvPowerSeries.order_finite_iff_ne_zero

/-- If the order of a formal power series `f` is finite,
then some coefficient of degree the order of `f` is nonzero.-/
theorem exists_coeff_ne_zero_of_order (h : ↑(toNat f.order) = f.order) :
    ∃ d : σ →₀ ℕ, ↑(degree d) = f.order ∧ coeff α d f ≠ 0 :=
  exists_coeff_ne_zero_of_weightedOrder _ f h
#align mv_power_series.exists_coeff_ne_zero_of_order MvPowerSeries.exists_coeff_ne_zero_of_order

/-- If the `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`. -/
theorem order_le (d : σ →₀ ℕ) (h : coeff α d f ≠ 0) : f.order ≤ degree d :=
  weightedOrder_le _ f h
#align mv_power_series.order_le MvPowerSeries.order_le

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_order (d : σ →₀ ℕ) (h : ↑(degree d) < f.order) : coeff α d f = 0 :=
  coeff_of_lt_weightedOrder _ f h
#align mv_power_series.coeff_of_lt_order MvPowerSeries.coeff_of_lt_order

/-- The `0` power series is the unique power series with infinite order.-/
@[simp]
theorem order_eq_top {f : MvPowerSeries σ α} : f.order = ⊤ ↔ f = 0 :=
  weightedOrder_eq_top_iff _
#align mv_power_series.order_eq_top MvPowerSeries.order_eq_top

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
theorem nat_le_order {f : MvPowerSeries σ α} {n : ℕ} (h : ∀ d, degree d < n → coeff α d f = 0) :
    ↑n ≤ f.order :=
  nat_le_weightedOrder _ h
#align mv_power_series.nat_le_order MvPowerSeries.nat_le_order

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
theorem le_order {f : MvPowerSeries σ α} {n : ℕ∞}
    (h : ∀ d : σ →₀ ℕ, ↑(degree d) < n → coeff α d f = 0) : n ≤ f.order :=
  le_weightedOrder _ h
#align mv_power_series.le_order MvPowerSeries.le_order

/-- The order of a formal power series is exactly `n` some coefficient 
of degree `n` is nonzero, 
and the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
theorem order_eq_nat {f : MvPowerSeries σ α} {n : ℕ} :
    f.order = n ↔ (∃ d, degree d = n ∧ coeff α d f ≠ 0) ∧ ∀ d, degree d < n → coeff α d f = 0 :=
  weightedOrder_eq_nat _
#align mv_power_series.order_eq_nat MvPowerSeries.order_eq_nat

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
theorem le_order_add (f g : MvPowerSeries σ α) : min f.order g.order ≤ (f + g).order :=
  le_weightedOrder_add _ f g
#align mv_power_series.le_order_add MvPowerSeries.le_order_add

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem order_add_of_order_eq {f g : MvPowerSeries σ α} (h : f.order ≠ g.order) :
    order (f + g) = order f ⊓ order g :=
  weightedOrder_add_of_weightedOrder_eq _ h
#align mv_power_series.order_add_of_order_eq MvPowerSeries.order_add_of_order_eq

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
theorem order_mul_ge (f g : MvPowerSeries σ α) : f.order + g.order ≤ order (f * g) :=
  weightedOrder_mul_ge _ f g
#align mv_power_series.order_mul_ge MvPowerSeries.order_mul_ge

/-- The order of the monomial `a*X^d` is infinite if `a = 0` and `degree d` otherwise.-/
theorem order_monomial (d : σ →₀ ℕ) (a : α) [Decidable (a = 0)] :
    order (monomial α d a) = if a = 0 then ⊤ else degree d :=
  weightedOrder_monomial _ d a
#align mv_power_series.order_monomial MvPowerSeries.order_monomial

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem order_monomial_of_ne_zero (d : σ →₀ ℕ) {a : α} (h : a ≠ 0) :
    order (monomial α d a) = degree d :=
  weightedOrder_monomial_of_ne_zero _ d a h
#align mv_power_series.order_monomial_of_ne_zero MvPowerSeries.order_monomial_of_ne_zero

/-- If `degree d` is strictly smaller than the order of `g`, then the `d`th coefficient of its 
product with any other power series is `0`. -/
theorem coeff_mul_of_lt_order {f g : MvPowerSeries σ α} {d : σ →₀ ℕ} (h : ↑(degree d) < g.order) :
    coeff α d (f * g) = 0 :=
  coeff_mul_of_lt_weightedOrder _ f h
#align mv_power_series.coeff_mul_of_lt_order MvPowerSeries.coeff_mul_of_lt_order

theorem coeff_mul_one_sub_of_lt_order {α : Type _} [CommRing α] {f g : MvPowerSeries σ α}
    (d : σ →₀ ℕ) (h : ↑(degree d) < g.order) : coeff α d (f * (1 - g)) = coeff α d f :=
  coeff_mul_one_sub_of_lt_weightedOrder _ d h
#align mv_power_series.coeff_mul_one_sub_of_lt_order MvPowerSeries.coeff_mul_one_sub_of_lt_order

theorem coeff_mul_prod_one_sub_of_lt_order {α ι : Type _} [CommRing α] (d : σ →₀ ℕ) (s : Finset ι)
    (f : MvPowerSeries σ α) (g : ι → MvPowerSeries σ α) :
    (∀ i ∈ s, ↑(degree d) < order (g i)) → coeff α d (f * ∏ i in s, (1 - g i)) = coeff α d f :=
  coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g
#align mv_power_series.coeff_mul_prod_one_sub_of_lt_order MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order

end Order

section HomogeneousComponent

variable (w : σ → ℕ)

/-- Given an `mv_power_series f`, it returns the homogeneous component of degree `p`. -/
def homogeneousComponent (p : ℕ) : MvPowerSeries σ α →ₗ[α] MvPowerSeries σ α
    where
  toFun f d := ite (weight w d = p) (coeff α d f) 0
  map_add' f g := by
    ext d
    simp only [coeff_apply, Pi.add_apply]
    split_ifs
    rfl
    rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [coeff_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_ite,
      MulZeroClass.mul_zero]
#align mv_power_series.homogeneous_component MvPowerSeries.homogeneousComponent

theorem coeff_homogeneousComponent (p : ℕ) (d : σ →₀ ℕ) (f : MvPowerSeries σ α) :
    coeff α d (homogeneousComponent w p f) = ite (weight w d = p) (coeff α d f) 0 :=
  rfl
#align mv_power_series.coeff_homogeneous_component MvPowerSeries.coeff_homogeneousComponent

end HomogeneousComponent

end MvPowerSeries

