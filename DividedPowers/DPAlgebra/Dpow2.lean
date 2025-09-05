import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.Padic
import DividedPowers.SubDPIdeal
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology

/-! # Construction of the divided power structure on the divided power algebra
-/

namespace Localization

variable {R : Type*} [CommRing R] {M : Submonoid R}

theorem r_iff_of_le_nonZeroDivisors (hM : M ≤ nonZeroDivisors R)
    (a c : R) (b d : M) :
    Localization.r _ (a, b) (c, d) ↔ a * d = b * c  := by
  simp only [Localization.r_eq_r', Localization.r', Subtype.exists, exists_prop, Con.rel_mk]
  constructor
  · rintro ⟨u, hu, h⟩
    have hu' : u ∈ nonZeroDivisors R := hM hu
    simp only [mem_nonZeroDivisors_iff, mul_comm] at hu'
    rw [← sub_eq_zero]
    apply hu'
    rwa [mul_sub, sub_eq_zero, mul_comm a]
  · intro h
    exact ⟨1, Submonoid.one_mem M,
      by simpa only [one_mul, mul_comm a] using h⟩

instance {R : Type*} [CommRing R] [DecidableEq R] :
    DecidableEq (FractionRing R) := by
  intro x y
  apply recOnSubsingleton₂ x y (r := fun x y ↦ Decidable (x = y))
  intro a c b d
  simp only [mk_eq_mk_iff, r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

end Localization

section

namespace Nat

open Finset

theorem multinomial_congr_of_sdiff
    {α : Type*} [DecidableEq α] {f g : α → ℕ} {s t : Finset α}
    (hst : s ⊆ t) (H1 : ∀ a ∈ t \ s, g a = 0) (H2 : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial t g := by
  rw [← Nat.mul_right_inj (a := ∏ a ∈ t, (g a)!), multinomial_spec,
    ← sum_subset_zero_on_sdiff hst H1 H2, ← multinomial_spec s f]
  · apply congr_arg₂ _ _ rfl
    symm
    apply prod_subset_one_on_sdiff hst
    · intro x hx
      rw [H1 x hx, factorial_zero]
    · intro x hx
      rw [H2 x hx]
  · simp only [ne_eq, prod_eq_zero_iff, not_exists, not_and]
    intro x hx
    exact factorial_ne_zero (g x)

end Nat

namespace Finset

open Sym

theorem prod_smul' {α β ι : Type*}
    [CommMonoid β] [CommMonoid α] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β]
    (s : Finset ι) (b : ι → α) (f : ι → β) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using cons_induction_on with
  | empty =>  simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

lemma sym_map {α β : Type*} [DecidableEq α] [DecidableEq β] {n : ℕ}
  (g : α ↪ β) (s : Finset α) :
    (s.map g).sym n = (s.sym n).map ⟨Sym.map g, Sym.map_injective g.injective _⟩ := by
  ext d
  simp only [mem_sym_iff, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hd
    let g' : {x // x ∈ d} → α := fun ⟨x, hx⟩ ↦ (hd x hx).choose
    let h : Sym {x // x ∈ d} n → Sym α n := fun p ↦ Sym.map g' p
    use h d.attach
    constructor
    · simp only [Sym.mem_map, Sym.mem_attach, true_and, Subtype.exists, forall_exists_index, h, g']
      intro i e he hi
      rw [← hi]
      exact (hd e he).choose_spec.1
    · simp only [Sym.map_map, Function.comp_apply, h, g']
      convert Sym.attach_map_coe d with ⟨x, hx⟩ hx'
      exact (hd x hx).choose_spec.2
  · rintro ⟨b, hb, rfl⟩ d hd
    simp only [Sym.mem_map] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    refine ⟨a, hb a ha, rfl⟩

end Finset

namespace Sym

open Finset

theorem sum_eq_val_sum {ι : Type*} [DecidableEq ι] {n : ℕ}
    (k : Sym (ι →₀ ℕ) n) {s : Finset (ι →₀ ℕ)} (hk : k ∈ s.sym n) :
    ∑ d ∈ s, Multiset.count d k • d = k.val.sum := by
  induction n with
  | zero =>
    simp only [sym_zero, mem_singleton] at hk
    have : ↑k = 0 := by
      simp [hk]; rfl
    simp [this]
  | succ n hrec =>
    simp only [sym_succ, Nat.succ_eq_add_one, mem_sup, mem_image, mem_sym_iff] at hk
    obtain ⟨a, hat, k, hk, rfl⟩ := hk
    simp [Sym.val_eq_coe, Nat.succ_eq_add_one, Sym.coe_cons, Multiset.count_cons, add_smul]
    rw [Finset.sum_add_distrib]
    nth_rewrite 2 [Finset.sum_eq_single a]
    · rw [if_pos rfl, add_comm]
      apply congr_arg₂ _ rfl
      apply hrec
      rwa [mem_sym_iff]
    · intro b hb hab
      rw [if_neg hab]
    · intro has
      exact (has hat).elim

end Sym

namespace DividedPowers

open Finset

variable {R : Type*} [CommSemiring R] {I : Ideal R} (hI : DividedPowers I)

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem dpow_finsupp_sum {ι : Type*} [DecidableEq ι] {x : ι →₀ R} (hx : ∀ i, x i ∈ I)
    {n : ℕ} :
    hI.dpow n (x.sum fun _ r ↦ r) =
      ∑ k ∈ (x.support.sym n), x.prod fun i r ↦ hI.dpow (Multiset.count i k) r := by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ ↦ hx i), Finsupp.prod]

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem dpow_linearCombination {A : Type*} [CommSemiring A] [Algebra R A]
    {I : Ideal A} (hI : DividedPowers I) {ι : Type*} [DecidableEq ι] {b : ι → A} {x : ι →₀ R}
    (hx : ∀ i ∈ x.support, b i ∈ I) {n : ℕ} :
    hI.dpow n (x.sum fun i r ↦ r • (b i)) =
      ∑ k ∈ x.support.sym n,
        x.prod fun i r ↦ r ^ (Multiset.count i k) • hI.dpow (Multiset.count i k) (b i) := by
  rw [Finsupp.sum, hI.dpow_sum (fun i hi ↦ Submodule.smul_of_tower_mem I _ (hx i hi))]
  apply Finset.sum_congr rfl
  intros
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Algebra.smul_def, hI.dpow_mul (hx i hi), ← map_pow, ← Algebra.smul_def]

theorem dpow_prod {I : Ideal R} (hI : DividedPowers I)
  {ι : Type*} [DecidableEq ι] {r : ι → R} {s : Finset ι}
  (hs : s.Nonempty) (hs' : ∀ i ∈ s, r i ∈ I) {n : ℕ} :
    hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i)) := by
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_notMem has, add_tsub_cancel_right,
          nsmul_eq_mul, Nat.cast_pow, Finset.prod_insert has]
        rw [hrec h]
        · simp only [nsmul_eq_mul, Nat.cast_pow, ← mul_assoc]
          apply congr_arg₂ _ _ rfl
          have : #s = #s - 1 + 1 := by
            refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
            exact one_le_card.mpr h
          nth_rewrite 2 [this]
          rw [mul_comm, pow_succ, mul_assoc, hI.factorial_mul_dpow_eq_pow]
          exact hs' a (mem_insert_self a s)
        · intro i hi
          apply hs' i (mem_insert_of_mem hi)
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_prod_diff_singleton_mul hj]
      apply Ideal.mul_mem_left
      apply hs' j (mem_insert_of_mem hj)
    · simp only [not_nonempty_iff_eq_empty] at h
      simp [h]

end DividedPowers

section

open DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

namespace DividedPowerAlgebra

universe u v v₁ v₂ w uA uR uS uM

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

-- variable [DecidableEq R]

variable (x : M) {n : ℕ}

/-- Lemma 2 of Roby 65 : there is at most one divided power structure on the augmentation ideal
  of `DividedPowerAlgebra R M` such that `∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x`. -/
theorem onDPAlgebra_unique [DecidableEq R] (h h' : DividedPowers (augIdeal R M))
    (h1 : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    (h1' : ∀ (n : ℕ) (x : M), h'.dpow n (ι R M x) = dp R n x) : h = h' := by
  apply DividedPowers.dpow_eq_from_gens h' h (augIdeal_eq_span R M)
  rintro n f ⟨q, hq : 0 < q, m, _, rfl⟩
  nth_rw 1 [← h1' q m]
  rw [← h1 q m, h.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m),
    h'.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m), h1 _ m, h1' _ m]

namespace Free

/-- The basis of the graded part of `DividedPowerAlgebra R M` associated with a basis of `M`. -/
noncomputable def basis_grade {ι : Type*} (b : Basis ι R M) (n : ℕ) :
    Basis {d : ι →₀ ℕ // d.degree = n} R (grade R M n) := by
  apply Basis.mk (v := fun ⟨d, hd⟩ ↦
    ⟨d.prod (fun i k ↦ dp R k (b i)), by
      suffices n = d.sum (fun i k ↦ k) by
        simp only [this, Finsupp.sum, Finsupp.prod]
        exact SetLike.prod_mem_graded (grade R M) d
          (fun i ↦ dp R (d i) (b i)) (fun i _ ↦ dp_mem_grade R M (d i) (b i))
      simp only [← hd, Finsupp.degree, Finsupp.sum]⟩)
  sorry
  sorry

theorem isFree_grade [Module.Free R M] (n : ℕ) :
    Module.Free R (grade R M n) :=
  Module.Free.of_basis (basis_grade R M (Module.Free.chooseBasis R M) n)

/-- The basis of the graded part of `DividedPowerAlgebra R M` associated with a basis of `M`. -/
noncomputable def basis {ι : Type*} (b : Basis ι R M) :
    Basis (ι →₀ ℕ) R (DividedPowerAlgebra R M) := by
  apply Basis.mk (v := fun d ↦ d.prod (fun i k ↦ dp R k (b i)))
  sorry
  sorry

theorem isFree [Module.Free R M] : Module.Free R (DividedPowerAlgebra R M) :=
  Module.Free.of_basis (basis R M (Module.Free.chooseBasis R M))

variable {R M} {ι : Type*} (b : Basis ι R M) {n : ℕ}

lemma basis_eq (d : ι →₀ ℕ) :
    basis R M b d = d.prod (fun i k ↦ dp R k (b i)) := by
  simp [basis, Basis.coe_mk]

lemma basis_eq' [DecidableEq ι] {m : M} {n : ℕ} {x : Sym ι n} (hx : x ∈ (b.repr m).support.sym n) :
    ∏ i ∈ (b.repr m).support, dp R (Multiset.count i ↑x) (b i) =
      basis R M b (Multiset.toFinsupp ↑x):= by
  rw [basis_eq, Finsupp.prod_of_support_subset (s := (b.repr m).support)]
  · apply Finset.prod_congr rfl
    simp
  · intro i
    simp only [mem_sym_iff, Finsupp.mem_support_iff, ne_eq] at hx
    simpa using hx i
  · intro i hi
    exact dp_zero R (b i)

lemma basis_zero_eq_one : basis R M b 0 = 1 := by
  simp [basis_eq]

lemma basis_single_eq (i : ι) (n : ℕ) :
    basis R M b (Finsupp.single i n) = dp R n (b i) := by
  simp only [basis_eq]
  rw [Finsupp.prod_of_support_subset (s := {i}) _ Finsupp.support_single_subset]
  · simp [prod_singleton]
  · simp [dp_zero]

lemma basis_single_one_eq (i : ι) :
    basis R M b (Finsupp.single i 1) = DividedPowerAlgebra.ι R M (b i) := by
  rw [basis_single_eq]
  rfl

theorem basis_repr_ι (m : M) (d) [Decidable (∃ i, d = Finsupp.single i 1)] :
    (basis R M b).repr (DividedPowerAlgebra.ι R M m) d =
      if H : ∃ i, d = Finsupp.single i 1 then b.repr m H.choose else 0 := by
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
    have := (Basis.linearCombination_repr b m).symm
    simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  conv_lhs => rw [hm]
  simp [map_finsuppSum]
  simp only [← basis_single_one_eq, Basis.repr_self]
  split_ifs with H
  · obtain ⟨i, rfl⟩ := id H
    rw [Finsupp.sum_eq_single i]
    · simp only [Finsupp.single_eq_same, mul_one]
      apply congr_arg
      rw [← Finsupp.single_left_inj Nat.one_ne_zero]
      exact H.choose_spec
    · intro j hj hji
      rw [Finsupp.single_eq_of_ne, mul_zero]
      rwa [ne_eq, Finsupp.single_left_inj Nat.one_ne_zero]
    · simp
  · convert Finsupp.sum_zero with i r
    rw [Finsupp.single_eq_of_ne, mul_zero]
    exact fun H' ↦ H ⟨i, H'.symm⟩

theorem ι_repr_support_eq (m : M) :
    ((basis R M b).repr (DividedPowerAlgebra.ι R M m)).support
        = (b.repr m).support.map ⟨fun i ↦ Finsupp.single i 1, fun i j ↦ by
            simp [Finsupp.single_left_inj Nat.one_ne_zero]⟩ := by
  classical
  ext d
  rw [Finsupp.mem_support_iff, basis_repr_ι]
  split_ifs with H
  · obtain ⟨i, rfl⟩ := id H
    suffices H.choose = i by
      simp only [this, ne_eq, mem_map, Finsupp.mem_support_iff, Function.Embedding.coeFn_mk]
      constructor
      · intro H'
        exact ⟨i, H', rfl⟩
      · rintro ⟨j, hj, H'⟩
        simp_all [Finsupp.single_left_inj Nat.one_ne_zero]
    rw [← Finsupp.single_left_inj Nat.one_ne_zero, H.choose_spec.symm]
  · simp only [ne_eq, not_true_eq_false, mem_map, Finsupp.mem_support_iff,
    Function.Embedding.coeFn_mk, false_iff, not_exists, not_and]
    exact fun i hi hd ↦ H ⟨i, hd.symm⟩

theorem basis_mul (m n : ι →₀ ℕ) :
    basis R M b m * basis R M b n =
      ((m + n).prod fun i r ↦ r.choose (m i)) • basis R M b (m + n) := by
  classical
  simp only [basis_eq]
  set s := (m + n).support
  have hms : m.support ⊆ s := Finsupp.support_monotone le_self_add
  have hns : n.support ⊆ s := Finsupp.support_monotone le_add_self
  rw [Finsupp.prod_of_support_subset (s := s) m hms]
  · rw [Finsupp.prod_of_support_subset (s := s) n hns]
    · simp only [Finsupp.prod, s, ← Finset.prod_mul_distrib, dp_mul, ← Finset.prod_smul']
      apply Finset.prod_congr rfl
      intros; simp
    · intros; simp [dp_zero]
  · intros; simp [dp_zero]

/-
basis R M b f = ∏ i, (b i) ^[f i]

∏ a ∈ s, basis R M b (f a) = ∏ i, ∏ a, (b i)^[f a i]

Now, ∏ a, (b i)^[f a i] = ?? • (b i)^[∑ f a i]
where ?? is some integer to be determined.
From the formal expressions (valid in a ℚ-algebra)
∏ a, (b i)^[f a i] = ∏ a, (b i) ^ (f a i) / (f a i)!
and
(b i)^[∑ a, f a i] = (b i)^(∑ f a i) / (∑ f a i)!,
we infer that
?? = Nat.multinomial s (fun a ↦ f a i)
-/

theorem basis_prod (α : Type*) (f : α → (ι →₀ ℕ)) (s : Finset α) :
    ∏ a ∈ s, basis R M b (f a) =
      ((∑ a ∈ s, f a).prod fun i _ ↦ Nat.multinomial s (fun a ↦ f a i)) •
        basis R M b (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [basis_zero_eq_one]
  | @insert a s has hrec =>
    rw [Finset.prod_insert has, hrec, mul_smul_comm, basis_mul, ← Finset.sum_insert has]
    simp only [← smul_assoc]
    apply congr_arg₂ _ _ rfl
    have : (∑ x ∈ s, f x).support ⊆ (∑ x ∈ insert a s, f x).support := by
      apply Finsupp.support_monotone
      rw [Finset.sum_insert has]
      exact le_add_self
    simp only [Finsupp.prod]
    simp only [← Finset.prod_sdiff this]
    simp only [smul_eq_mul]
    rw [mul_left_comm]
    apply congr_arg₂
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [mem_sdiff, Finsupp.mem_support_iff, Finsupp.coe_finset_sum, sum_apply, ne_eq,
        sum_eq_zero_iff, mem_insert, forall_eq_or_imp, not_and, not_forall, not_exists, Decidable.not_not] at hi
      rw [Nat.multinomial_insert has]
      simp only [Finset.sum_insert has, Finsupp.coe_add, Finsupp.coe_finset_sum, Pi.add_apply,
        sum_apply]
      symm
      convert mul_one _
      rw [← Nat.mul_right_inj Nat.one_ne_zero, mul_one]
      convert Nat.multinomial_spec _ _
      · symm
        apply Finset.prod_eq_one
        intro x hx
        simp [hi.2 x hx]
      · symm
        convert Nat.factorial_zero
        apply Finset.sum_eq_zero
        intro x hx
        simp [hi.2 x hx]
    · rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.sum_insert has, Nat.multinomial_insert has, mul_comm]


theorem basis_repr_mul [DecidableEq ι] (x y : DividedPowerAlgebra R M) (d : ι →₀ ℕ) :
    (basis R M b).repr (x * y) d =
      ∑ uv ∈ antidiagonal d,
        (d.prod fun a_1 b ↦ (b.choose (uv.1 a_1))) • ((basis R M b).repr x uv.1 * (basis R M b).repr y uv.2) := by
  have h (x : DividedPowerAlgebra R M) :
    x =  (((basis R M b).repr x).sum fun i c ↦ c • (basis R M b) i) := by
    simpa only using (Basis.linearCombination_repr (basis R M b) x).symm
  conv_lhs => rw [h x, h y]
  simp only [Finsupp.sum, Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_smul, Finsupp.coe_finset_sum,
    Finsupp.coe_smul, sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [basis_mul, map_nsmul]
  rw [← Finset.sum_product']
  apply Finset.sum_congr_of_eq_on_inter
  · intro a ha ha'
    convert mul_zero _
    convert mul_zero _
    simp only [Finsupp.prod]
    simp only [Finsupp.coe_add, Pi.add_apply, Basis.repr_self, Finsupp.smul_single, nsmul_eq_mul,
      Nat.cast_prod, mul_one]
    rw [Finsupp.single_eq_of_ne]
    simpa only [mem_antidiagonal] using ha'
  · intro a ha' ha
    simp only [mem_product, Finsupp.notMem_support_iff, not_and_or] at ha
    rcases ha with ha | ha <;> simp [ha]
  · intro a ha ha'
    simp [mem_antidiagonal] at ha'
    simp only [ha', Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same]
    ring

lemma basis_mem_augIdeal [DecidableEq R] {d : ι →₀ ℕ} (hd : d ≠ 0) :
    basis R M b d ∈ augIdeal R M := by
  simp only [mem_augIdeal_iff, basis_eq, map_finsuppProd, algebraMapInv_dp]
  simp only [Finsupp.prod]
  simp only [← Finsupp.support_nonempty_iff] at hd
  obtain ⟨i, hi⟩ := hd
  apply Finset.prod_eq_zero hi
  rw [Finsupp.mem_support_iff] at hi
  rw [if_neg hi]

lemma basis_mem_augIdeal_iff [DecidableEq R] [Nontrivial R] (d : ι →₀ ℕ) :
    basis R M b d ∈ augIdeal R M ↔ d ≠ 0 := by
  refine ⟨?_, basis_mem_augIdeal b⟩
  rw [imp_not_comm]
  rintro ⟨rfl⟩
  rw [basis_zero_eq_one, mem_augIdeal_iff, map_one]
  exact one_ne_zero

lemma eq_of_basis (x : DividedPowerAlgebra R M)  :
    x = ((basis R M b).repr x).sum fun i c ↦ c • (basis R M b) i := by
  conv_lhs => rw [← Basis.linearCombination_repr (basis R M b) x]
  simp [Finsupp.linearCombination, Finsupp.lsum]

lemma mem_augIdeal_iff_of_repr [DecidableEq R] {x : DividedPowerAlgebra R M} :
    x ∈ augIdeal R M ↔ (basis R M b).repr x 0 = 0 := by
  classical
  have H : x = (((basis R M b).repr x).update 0 0).sum (fun i c ↦ c • (basis R M b) i) +
      (fun i c ↦ c • (basis R M b) i) 0 ((basis R M b).repr x 0) := by
    rw [Finsupp.sum_update_add _ _ _ (fun i c ↦ c • (basis R M b) i) (fun _ ↦ zero_smul R _)
      (fun _ _ _ ↦ add_smul _ _ _), zero_smul, add_zero]
    exact eq_of_basis b x
  have hx' : (((basis R M b).repr x).update 0 0).sum (fun i c ↦ c • (basis R M b) i) ∈ augIdeal R M := by
    apply Ideal.sum_mem
    intro c hc
    simp only [Finsupp.support_update_zero, mem_erase, ne_eq, Finsupp.mem_support_iff] at hc
    exact Submodule.smul_of_tower_mem (augIdeal R M) _ (basis_mem_augIdeal b hc.1)
  nth_rewrite 1 [H]
  rw [Submodule.add_mem_iff_right _ hx']
  simp only [basis_zero_eq_one, mem_augIdeal_iff, map_smul, map_one]
  simp [smul_eq_mul]

theorem ne_zero_of_mem_support_of_mem_augIdeal [DecidableEq R]
    {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) {d : ι →₀ ℕ}
    (hd : d ∈ ((basis R M b).repr x).support) : d ≠ 0 := by
  rintro ⟨rfl⟩
  rw [mem_augIdeal_iff_of_repr b] at hx
  rw [Finsupp.mem_support_iff] at hd
  exact hd hx

/- When `M` is free with basis `b` (it would suffice that `b` generates `M`,
then any `x : DividedPowerAlgebra R M` can be written as
 `x = (B.repr x).sum fun d c ↦ c • B d)` :
 `x = ∑ d ∈ (B.repr x).support, B.repr x d • B d`
If `x ∈ augIdeal R M`, then `B.repr x 0 = 0`, and all terms in this
representation belong to `augIdeal R M`.
By the multinomial formula for divided powers, one has
  `dpow n x
    = ∑ d ∈ (B.repr x).support.sym n,
        ∏ i ∈ (B.repr x).support, dpow (d.count i) ((B.repr x i) • B i)
    = ∑ d ∈ (B.repr x).support.sym n,
        ∏ i ∈ (B.repr x).support, (B.repr x i) ^ (d.count i) • dpow (d.count i d) (B i) `
Now, `B i = i.prod (fun j k ↦ dp R k (b j)) = ∏ j ∈ i.support, dp R (i j) (b j)`.
Here, `i ≠ 0`, because `i ∈ (B.repr x).support`.
Consequently, there exists `j` such that `j ∈ i.support`.
dpow m (∏ j ∈ i.support, dp R (i j) (b j))
 = dpow m (dp R (i j) (b j) * ∏ k ≠ j, dp R (i j) (b j))
 = m.uniformBell (i j) * dp (m + i j) (b j) * ∏ k ≠ j, (dp R (i j) (b j))) ^ m
 =  .. `

 dpow m (∏ i ∈ s, r i) =
 * s = ∅ : dpow m 1 = 1 si m = 0, sinon = 0 si 1 ∉ I
 * s ≠ ∅ : s = insert j t
    dpow m (r j * ∏ i ∈ t, r i) = dpow m (r j) * ∏ i ∈ t, r i ^ m
    r i ^ m = m! * dpow m (r i)
    = (m!)^(s.card -1) * ∏ i ∈ s, dpow m (r i)

 -/

open scoped Nat

/- Can one simplify the quantity
 n! ^ (#d.support - 1) * ∏ i ∈ d.support n.uniformBell (d i) ?
-/
theorem dpow_basis_eq [DecidableEq R] (H : DividedPowers (augIdeal R M))
    (hH : ∀ (n : ℕ) (x : M), H.dpow n (DividedPowerAlgebra.ι R M x) = dp R n x)
    {ι : Type*} [DecidableEq ι] (b : Basis ι R M) (n : ℕ)
    (d : ι →₀ ℕ) (hd : d ≠ 0) :
    H.dpow n (basis R M b d) =
      (n ! ^ (#d.support - 1) • ∏ i ∈ d.support, n.uniformBell (d i)) •
        basis R M b (n • d) := by
  rw [basis_eq]
  rw [← Finsupp.support_nonempty_iff] at hd
  classical
  simp only [Finsupp.prod]
  rw [DividedPowers.dpow_prod H hd]
  · have (i) (hx : i ∈ d.support) : H.dpow n (dp R (d i) (b i))
      = (n.uniformBell (d i)) • dp R (n * d i) (b i) := by
      rw [← hH, dpow_comp, hH]
      · simp
      · exact Finsupp.mem_support_iff.mp hx
      · exact ι_mem_augIdeal R M (b i)
    simp only [Finset.prod_congr rfl this, Finset.prod_smul', smul_assoc]
    congr
    rw [basis_eq]
    rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
    · simp
    · exact fun i _ ↦ dp_zero R (b i)
  intro i hi
  simp only [Finsupp.mem_support_iff] at hi
  exact dp_mem_augIdeal R M (Nat.zero_lt_of_ne_zero hi) (b i)

      /-
(∑ d ∈ ((basis R M b).repr x).support, Multiset.count d ↑k • d) =  ??

k = k_1, ... , k_n : unordered n-tuple of (ι →₀ ℕ)
((basis R M b).repr x).support : Finset (ι →₀ ℕ)
∀ a, k_a ∈ ((basis R M b).repr x

Multiset.count d ↑k : how many a are there such that k_a = d
Multiset.count d ↑k • d : ι →₀ ℕ

-/

/-- A combinatorial coefficient that appears in the definition of the divided power structure
of the divided power algebra -/
noncomputable def cK [DecidableEq ι] {n : ℕ} (k : Sym (ι →₀ ℕ) n) (s : Finset (ι →₀ ℕ)) : ℕ :=
  (k.val.sum.prod fun i _ ↦ Nat.multinomial s fun a ↦ (Multiset.count a ↑k • a) i) *
  (∏ d ∈ s, (Multiset.count d ↑k)! ^ (#d.support - 1) • ∏ i ∈ d.support, (Multiset.count d ↑k).uniformBell (d i))

theorem cK_eq_of_subset [DecidableEq ι] {n : ℕ} {k : Sym (ι →₀ ℕ) n}
    {s t : Finset (ι →₀ ℕ)} (hst : s ⊆ t) (hk : k ∈ s.sym n) : cK k s = cK k t := by
  have H0 (d) (hd : d ∉ s) : Multiset.count d ↑k = 0 := by
    -- simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hd
    simp only [mem_sym_iff] at hk
    simp only [Multiset.count_eq_zero, Sym.mem_coe]
    exact fun a ↦ hd (hk d a)
  unfold cK
  apply congr_arg₂
  · simp only [Finsupp.prod]
    apply Finset.prod_congr rfl
    intro i hi
    apply Nat.multinomial_congr_of_sdiff hst
    · intro d hd
      rw [mem_sdiff] at hd
      simp [H0 d hd.2]
    · simp
  · apply Finset.prod_subset_one_on_sdiff hst
    · intro d hd
      rw [mem_sdiff] at hd
      simp [H0 d hd.2, Nat.uniformBell_zero_left]
    · simp

-- Decidability variables needed to define `dpow`
variable [DecidableEq R] [DecidableEq ι]

/-- The `dpow` function on the divided power algebra of a free module -/
noncomputable def dpow (n : ℕ) (x : DividedPowerAlgebra R M) :
    DividedPowerAlgebra R M :=
  if x ∈ augIdeal R M then
    ∑ k ∈ ((basis R M b).repr x).support.sym n,
      cK k ((basis R M b).repr x).support •
        (∏ d ∈ ((basis R M b).repr x).support, ((basis R M b).repr x) d ^ Multiset.count d ↑k) •
            (basis R M b) k.val.sum
  else 0

/- Is there a better formula ? -/
theorem dpow_eq (H : DividedPowers (augIdeal R M))
    (hH : ∀ (n : ℕ) (x : M), H.dpow n (DividedPowerAlgebra.ι R M x) = dp R n x)
    {ι : Type*} [DecidableEq ι] (b : Basis ι R M) {n : ℕ} {x : DividedPowerAlgebra R M} :
    H.dpow n x = dpow b n x := by
  simp only [dpow]
  split_ifs with hx
  · nth_rewrite 1 [eq_of_basis b x]
    classical
    rw [H.dpow_linearCombination
      (fun _ hd ↦ basis_mem_augIdeal b (ne_zero_of_mem_support_of_mem_augIdeal b hx hd))]
    apply Finset.sum_congr rfl (fun k hk ↦ ?_)
    simp only [Finsupp.prod, Finset.prod_smul']
    set A := (∏ i ∈ ((basis R M b).repr x).support, ((basis R M b).repr x) i ^ Multiset.count i k)
    set B := ∏ i ∈ ((basis R M b).repr x).support, H.dpow (Multiset.count i k) ((basis R M b) i)
      with hB
    set C := (basis R M b k.val.sum) with hC
    suffices B = cK k ((basis R M b).repr x).support • C by simp [this]
    have (i) (hi : i ∈ ((basis R M b).repr x).support) :=
      dpow_basis_eq H hH b (Multiset.count i ↑k) i (ne_zero_of_mem_support_of_mem_augIdeal b hx hi)
    simp only [Finset.prod_congr rfl this, Finset.prod_smul', basis_prod,
      k.sum_eq_val_sum hk, ← hC] at hB
    simp only [hB, ← smul_assoc]
    apply congr_arg₂ _ _ rfl
    simp only [smul_eq_mul, Sym.val_eq_coe, Finsupp.coe_smul, Pi.smul_apply, cK]
    rw [mul_comm]
    apply congr_arg₂ _ rfl
    rw [Finset.prod_mul_distrib]
  · exact H.dpow_null hx

theorem dpow_eq_of_support_subset
    {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M)
    {s : Finset (ι →₀ ℕ)} (hs : ((basis R M b).repr x).support ⊆ s) :
    dpow b n x = ∑ k ∈ s.sym n, cK k s •
      (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d ↑k) •
      (basis R M b) k.val.sum := by
  simp only [dpow, if_pos hx]
  have Hs : ((basis R M b).repr x).support.sym n ⊆ s.sym n := fun k hk ↦ by
    simp only [mem_sym_iff] at hk ⊢
    exact fun a ha ↦ hs (hk a ha)
  have H0 (k) (hk : k ∈ ((basis R M b).repr x).support.sym n)
      (d) (hd : d ∉ ((basis R M b).repr x).support) :
      Multiset.count d ↑k = 0 := by
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hd
    simp only [mem_sym_iff, Finsupp.mem_support_iff, ne_eq] at hk
    exact Multiset.count_eq_zero.mpr (fun hd' ↦ hk d hd' hd)
  apply Finset.sum_subset_zero_on_sdiff Hs
  · intro k hk
    suffices (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d ↑k) = 0 by
      simp [this]
    simp [mem_sdiff] at hk
    obtain ⟨d, hd, hd'⟩ := hk.2
    rw [Finset.prod_eq_prod_diff_singleton_mul (hk.left d hd)]
    convert mul_zero _
    simp [hd']
    apply zero_pow
    simpa [Multiset.count_eq_zero]
  · intro k hk
    congr 1
    · apply cK_eq_of_subset hs hk
    congr 1
    apply Finset.prod_subset_one_on_sdiff hs
    · intro d hd
      rw [mem_sdiff] at hd
      rw [H0 k hk d hd.2, pow_zero]
    · intros; rfl

theorem cK_map_single_eq_one {s : Finset ι} {k : Sym ι n} (hk : k  ∈ s.sym n) :
    let g : ι ↪ (ι →₀ ℕ) :=
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective Nat.one_ne_zero⟩
    cK (Sym.map g k) (s.map g) = 1 := by
  intro g
  simp only [cK, Sym.val_eq_coe, Sym.coe_map, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  convert mul_one _
  · apply Finset.prod_eq_one
    intro d hd
    simp only [mem_map] at hd
    obtain ⟨j, hj, rfl⟩ := hd
    rw [Multiset.count_map_eq_count' _ _ g.injective]
    convert mul_one _
    · apply Finset.prod_eq_one
      intro i hi
      have : j = i := by
        by_contra! h
        simp [g, Finsupp.single_eq_of_ne h] at hi
      simp [this, g, Nat.uniformBell_one_right]
    · suffices (g j).support = {j} by simp [this, card_singleton, tsub_self, pow_zero]
      ext i
      simp only [Finsupp.mem_support_iff, ne_eq, mem_singleton, g]
      by_cases h : j = i
      · simp [h]
      · simp [Finsupp.single_eq_of_ne h, Ne.symm h]
  · rw [eq_comm]
    simp only [Finsupp.prod]
    apply Finset.prod_eq_one
    intro i hi
    rw [← Nat.mul_right_inj, mul_one]
    convert Nat.multinomial_spec _ _
    · simp only [g] at hi
      simp only [prod_map, sum_map, Multiset.count_map_eq_count' _ _ g.injective]
      have H (j) (hj : j ≠ i) : Multiset.count j k * (g j) i = 0 := by
        simp [g, Finsupp.single_eq_of_ne hj]
      have H' (hi : i ∉ s) : Multiset.count i k * (g i) i = 0 := by
        convert zero_mul _
        simp only [Multiset.count_eq_zero, Sym.mem_coe]
        rw [mem_sym_iff] at hk
        exact fun a ↦ hi (hk i a)
      rw [Finset.prod_eq_single i _ _ , Finset.sum_eq_single i]
      · exact fun j hj hij ↦ H j hij
      · intro hi; rw [H' hi]
      · intro j hj hij
        rw [H j hij, Nat.factorial_zero]
      · intro hi; rw [H' hi, Nat.factorial_zero]
    · intro H
      rw [Finset.prod_eq_zero_iff] at H
      obtain ⟨j, hj, h⟩ := H
      apply Nat.factorial_ne_zero _ h

 theorem dpow_ι (m : M) :
    dpow b n (DividedPowerAlgebra.ι R M m) = dp R n m := by
  simp only [dpow, if_pos (ι_mem_augIdeal R M m)]
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
    have := (Basis.linearCombination_repr b m).symm
    simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  let g : ι ↪ (ι →₀ ℕ) :=
    ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective Nat.one_ne_zero⟩
  let gg : Sym ι n ↪ Sym (ι →₀ ℕ) n := {
    toFun a := Sym.map g a
    inj' := Sym.map_injective g.injective _ }
  conv_rhs =>
    rw [hm]
    simp only [Finsupp.sum]
    rw [dp_sum _ (b.repr m).support n]
  set s := (b.repr m).support with hs
  set t := ((basis R M b).repr ((DividedPowerAlgebra.ι R M) m)).support with ht
  have hst : t = Finset.map g s := by
    simp only [← hs, ht, ι_repr_support_eq]
    congr
  have hst' : t.sym n = Finset.map gg (s.sym n) := by
    rw [hst]
    apply Finset.sym_map
  rw [hst', Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Function.Embedding.coeFn_mk, Sym.coe_map, Sym.val_eq_coe, gg, hst]
  rw [cK_map_single_eq_one hk, one_smul]
  simp only [prod_map, Multiset.count_map_eq_count' _ _ g.injective]
  have (x) (_ : x ∈ s) :
    ((basis R M b).repr ((DividedPowerAlgebra.ι R M) m)) (g x) ^ Multiset.count x k =
    (b.repr m) x ^ Multiset.count x ↑k := by
    conv_lhs => rw [hm, map_finsuppSum, map_finsuppSum]
    simp only [map_smul, Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      ← basis_single_one_eq, Basis.repr_self]
    rw [Finsupp.sum_eq_single x]
    · simp only [Function.Embedding.coeFn_mk, Finsupp.single_eq_same, mul_one, g]
    · intro i hi hix
      convert mul_zero _
      rw [Finsupp.single_eq_of_ne]
      exact g.injective.ne_iff.mpr hix
    · simp
  rw [Finset.prod_congr rfl this]
  clear this
  have hk':  (Multiset.map g k).sum = Multiset.toFinsupp (k : Multiset ι) := by
    symm
    rw [Multiset.toFinsupp_eq_iff]
    ext i
    simp only [Finsupp.count_toMultiset]
    set p : Multiset ι := ↑k with hp
    induction p using Multiset.induction_on with
    | empty => simp
    | cons j q H =>
      simp only [Multiset.count_cons, H, add_comm, Multiset.map_cons,
        Multiset.sum_cons, Finsupp.coe_add, Pi.add_apply, add_left_inj]
      simp [g, Finsupp.single_apply, eq_comm]
  simp only [hk', dp_smul, Finset.prod_smul']
  apply congr_arg₂ _ rfl
  simp [basis_eq, Finsupp.prod]
  have : (k : Multiset ι).toFinset ⊆ s := by
    intro i hi
    simp only [Multiset.mem_toFinset, Sym.mem_coe] at hi
    rw [mem_sym_iff] at hk
    exact hk i hi
  rw [← Finset.prod_sdiff this, eq_comm]
  convert one_mul _
  rw [Finset.prod_eq_one]
  intro i hi
  simp only [mem_sdiff, Multiset.mem_toFinset, Sym.mem_coe] at hi
  rw [← Sym.mem_coe, ← Multiset.count_eq_zero] at hi
  rw [hi.2, dp_zero]

-- TODO: golf and speed up
omit [DecidableEq R] in
lemma repr_dp_one (m : M) : (basis R M b).repr (dp R 1 m) =
    ∑ x ∈ (b.repr m).support, (((b.repr m) x) • (basis R M b).repr
          ((basis R M b) (Multiset.toFinsupp (Sym.oneEquiv x)))) := by
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
      have := (Basis.linearCombination_repr b m).symm
      simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  simp only [Finsupp.sum] at hm
  conv_lhs =>
    rw [hm, dp_sum]
    simp only [sym_succ, Nat.succ_eq_add_one, Nat.reduceAdd, sym_zero, image_singleton,
      sup_singleton_apply, Finsupp.mem_support_iff, ne_eq, Sym.cons_inj_left, imp_self, implies_true,
      sum_image, map_sum]
    simp only [dp_smul, Finset.prod_smul', map_smul]
  simp only [Sym.cons_inj_left, implies_true, Set.injOn_of_eq_iff_eq, sum_image, Sym.oneEquiv_apply,
    Sym.coe_mk, Multiset.toFinsupp_singleton, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one]
  have hx' (x : ι) : x ::ₛ (∅ : Sym ι 0) = Sym.oneEquiv x := rfl
  calc
    ∑ x ∈ (b.repr m).support,
  (∏ i ∈ (b.repr m).support, (b.repr m) i ^ Multiset.count i ↑(x ::ₛ ∅)) •
    (basis R M b).repr (∏ i ∈ (b.repr m).support, dp R (Multiset.count i ↑(x ::ₛ ∅)) (b i)) =
    ∑ x ∈ (b.repr m).support,
    ((∏ i ∈ (b.repr m).support, (b.repr m) i ^ Multiset.count i ↑(x ::ₛ (∅ : Sym ι 0))) • (basis R M b).repr
    ((basis R M b) (Multiset.toFinsupp ↑(x ::ₛ (∅ : Sym ι 0))))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [basis_eq']
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, sym_succ, sym_zero, image_singleton,
        sup_singleton_apply, hx' x, Sym.oneEquiv_apply, mem_image, Finsupp.mem_support_iff, ne_eq]
      simp only [Finsupp.mem_support_iff, ne_eq] at hx
      use x, hx
      simp only [hx' x, Sym.oneEquiv_apply]
    _ = ∑ x ∈ (b.repr m).support,
        ((∏ i ∈ (b.repr m).support, (b.repr m) i ^ Multiset.count i {x}) • (basis R M b).repr
        ((basis R M b) (Multiset.toFinsupp ↑(x ::ₛ (∅ : Sym ι 0))))) := by congr
    _ = ∑ x ∈ (b.repr m).support, (((b.repr m) x) • (basis R M b).repr
          ((basis R M b) (Multiset.toFinsupp (Sym.oneEquiv x)))) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr
      conv_rhs => rw [← pow_one (b.repr m x), ← Multiset.count_singleton_self x]
      apply Finset.prod_eq_single_of_mem _ hx
      intro y hy hyx
      have hyx' : Multiset.count y {x} = 0 := by rw [Multiset.count_singleton, if_neg hyx]
      rw [hyx', pow_zero]
    _ = _ := by
      simp


theorem dpow_null {n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∉ augIdeal R M) :
    dpow b n x = 0 := by
  simp only [dpow, Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm, ite_eq_right_iff]
  intro hx'
  exfalso
  apply hx
  exact hx'

theorem cK_zero {k : Sym (ι →₀ ℕ) 0} {s : Finset (ι →₀ ℕ)} :
    cK k s = 1 := by
  simp [cK, Subsingleton.eq_zero k, Nat.uniformBell_zero_left]

theorem dpow_zero {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 0 x = 1 := by
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp [dpow, if_pos hx, this, basis_eq, cK_zero]

theorem _root_.Nat.multinomial_single {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (n : ℕ) :
    Nat.multinomial s (Pi.single a n) = 1 := by
  rw [← Nat.mul_right_inj, mul_one, Nat.multinomial_spec]
  · simp only [sum_pi_single']
    split_ifs with ha
    · rw [Finset.prod_eq_single a]
      · simp
      · intro b hb hba
        simp [Pi.single_apply, if_neg hba]
      · simp_all
    · rw [eq_comm, Nat.factorial_zero]
      apply Finset.prod_eq_one
      intro b hb
      rw [Pi.single_apply, if_neg, Nat.factorial_zero]
      exact ne_of_mem_of_not_mem hb ha
  · simp only [ne_eq, prod_eq_zero_iff, not_exists, not_and]
    intro x hx
    apply Nat.factorial_ne_zero

theorem cK_one {s : Finset (ι →₀ ℕ)} {k : Sym (ι →₀ ℕ) 1} :
    cK k s = 1 := by
  let d := Sym.oneEquiv.symm k
  have : k = Sym.oneEquiv d := by simp [d]
  have kval : (k : Multiset (ι →₀ ℕ)) = {d} := by simp [this]
  unfold cK
  rw [kval, Finset.prod_eq_single d]
  · simp
    constructor
    · apply Finset.prod_eq_one
      intro i hi
      have : Pi.single d (d i) = fun a ↦ if a = d then a i else 0 := by
        ext a
        split_ifs with h <;> simp [Pi.single_apply, h]
      simp [Multiset.nodup_singleton, Multiset.count_singleton, ← this, Nat.multinomial_single]
    · simp [Nat.uniformBell_one_left]
  · intro c hc hcd
    simp [Multiset.count_singleton, if_neg hcd, Nat.uniformBell_zero_left]
  · intros
    simp [Nat.uniformBell_one_left]

theorem dpow_one {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 1 x = x := by
  classical
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp only [dpow, if_pos hx]
  conv_rhs => rw [eq_of_basis b x]
  simp only [sym_succ, Nat.succ_eq_add_one, sym_zero, this, image_singleton, sup_singleton_apply,
    Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm, Sym.cons_inj_left, implies_true,
    Set.injOn_of_eq_iff_eq, sum_image, Sym.coe_cons, Sym.toMultiset_zero, Multiset.cons_zero,
    Multiset.count_singleton, pow_ite, pow_one, pow_zero, prod_ite_eq', Finsupp.mem_support_iff,
    ne_eq, ite_not, Multiset.sum_singleton, ite_smul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [cK_one, Nat.cast_one, one_mul, ite_eq_right_iff]
  intro h
  simp only [Finsupp.mem_support_iff] at hd
  exact (hd h).elim

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : dpow b n 0 = 0 := by
  simp only [dpow, if_pos (Ideal.zero_mem _)]
  simp [(Finset.sym_eq_empty (s := ∅) (n := n)).mpr ?_, hn]

theorem dpow_mem {n : ℕ} {x : DividedPowerAlgebra R M} (hn : n ≠ 0) (hx : x ∈ augIdeal R M) :
    dpow b n x ∈ augIdeal R M := by
  have hn' : n = n.pred.succ := (Nat.succ_pred_eq_of_ne_zero hn).symm
  simp only [dpow]
  rw [if_pos, hn']
  apply Ideal.sum_mem
  intro k hk
  apply Submodule.smul_of_tower_mem
  obtain ⟨d, s', rfl⟩ := k.exists_eq_cons_of_succ
  simp only [Sym.mem_cons, mem_sym_iff, forall_eq_or_imp] at hk
  apply Submodule.smul_of_tower_mem
  apply basis_mem_augIdeal
  simp [Sym.coe_cons, ne_zero_of_mem_support_of_mem_augIdeal b hx hk.1]
  exact hx

/-- The exponential power series associated with `dpow` -/
noncomputable def dpowExp (x : DividedPowerAlgebra R M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dpow b n x)

open scoped PowerSeries.WithPiTopology

local instance : UniformSpace (DividedPowerAlgebra R M) := ⊥
local instance : DiscreteTopology (DividedPowerAlgebra R M) := by
    exact forall_open_iff_discrete.mp fun s ↦ trivial

/- Could we simplify the RHS further? -/
/-  Would it be easier to prove `dpow_add` by means of `dpowExp`? -/
open scoped Classical in
theorem dpowExp_eq_of_support_subset {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M)
    {s : Finset (ι →₀ ℕ)} (hs : ((basis R M b).repr x).support ⊆ s) :
    dpowExp b x = ∑' (n : ℕ), ∑ k ∈ s.sym n,
      (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d k) •
        (PowerSeries.monomial (DividedPowerAlgebra R M) n)
        ((cK k s) * (basis R M b) (k : Multiset (ι →₀ ℕ)).sum) := by
  rw [PowerSeries.as_tsum (dpowExp b x)]
  simp [dpowExp, dpow_eq_of_support_subset b hx hs, Sym.val_eq_coe, nsmul_eq_mul,
    Algebra.mul_smul_comm, PowerSeries.coeff_mk, map_sum, LinearMap.map_smul_of_tower]


section Compare
/- The previous examples show that it is complicated to expand precisely the formulas
  to check the divided power structure, and in any case, it will end up in verifying
  specific combinatorial relations, which is undesireable.
  The following is another attempt, hopefully easier.
  The given formula for `dpow` is a prerequisite, though.
  It consists in doing *exactly* what one says when one describes the proof orally.
  To define a divided power structure on `DividedPowerAlgebra R M`,
  when `M` is a free `R`-module, we compare `dpow R M b`
  with `dpow S N c`, for a free `S`-module `N` with a basis `c` which is indexed
  by the same type as `b`.
  We have two possibilities
  * We embedd `R ↪ S`, and give ourselves `N` which is free with the “same” basis
    (`N := baseChange S N` could work) so that we know that we have a divided power
    structure on `DividedPowerAlgebra S N`.
    If `R` is an integral domain of characteristic `0`, one can take for `S` its fraction field
    and then the divided power structure exists.
    Since `R` embeds in `S`, the relations for `dpow R M b` follow from that of `dpow S N c`.
  * We view `R` as a quotient of `S`, `S →+* R`,
    and give ourselves `N` which is free with the “same” basis,
    and assume that we know that we have a divided power
    structure on `DividedPowerAlgebra S N`.
    The relations for `dpow S N c` imply that for `dpow R M b`.
  -/

variable {S : Type*} [CommRing S] [Algebra R S]
    {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (c : Basis ι S N) (f : M →ₗ[R] N) (hf : ∀ i, f (b i) = c i)

section basis

omit [DecidableEq R] [DecidableEq ι]

include hf in
lemma compare_basis (d : ι →₀ ℕ) :
    basis S N c d = LinearMap.lift S f (basis R M b d) := by
  simp [basis_eq, map_finsuppProd, LinearMap.lift_apply_dp, hf]

omit [Algebra R S] [IsScalarTower R S N] in
theorem eq_of_repr (x : DividedPowerAlgebra R M) :
    x = (((basis R M b).repr x).sum fun i r ↦ r • basis R M b i) := by
  simpa only [Finsupp.linearCombination, Finsupp.lsum] using
    (Basis.linearCombination_repr (basis R M b) x).symm

include hf in
theorem repr_lift_eq (x : DividedPowerAlgebra R M) (d : ι →₀ ℕ) :
    (basis S N c).repr (LinearMap.lift S f x) d = algebraMap R S ((basis R M b).repr x d) := by
  have : LinearMap.lift S f x =
      ((basis R M b).repr x).sum fun i r ↦ r • basis S N c i := by
    rw [eq_of_repr b x]
    simp [map_finsuppSum, compare_basis b c f hf]
  rw [this, map_finsuppSum, Finsupp.sum_apply, Finsupp.sum_eq_single d]
  · simp [algebra_compatible_smul S]
  · intro e he hed
    simp [algebra_compatible_smul S, Finsupp.single_eq_of_ne hed]
  · simp

include hf in
theorem repr_lift_support_subset (x : DividedPowerAlgebra R M) :
    ((basis S N c).repr (LinearMap.lift S f x)).support ⊆ ((basis R M b).repr x).support := by
  intro d
  simp [Finsupp.mem_support_iff, repr_lift_eq _ _ _ hf, not_imp_not]
  intro H
  rw [H, map_zero]

end basis

include hf in
omit [DecidableEq ι] in
theorem lift_mem_augIdeal [DecidableEq S]
    (x : DividedPowerAlgebra R M) (hx : x ∈ augIdeal R M) :
    LinearMap.lift S f x ∈ augIdeal S N := by
  rw [mem_augIdeal_iff_of_repr c]
  rw [mem_augIdeal_iff_of_repr b] at hx
  simp [repr_lift_eq _ _ _ hf, hx]

variable [DecidableEq S]

include hf in
variable {c b f} in
theorem lift_dpow {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    LinearMap.lift S f (dpow b n x) = dpow c n (LinearMap.lift S f x) := by
  rw [dpow_eq_of_support_subset b hx (subset_refl _)]
  rw [dpow_eq_of_support_subset c (lift_mem_augIdeal b c f hf x hx)
    (repr_lift_support_subset b c f hf x)]
  simp only [nsmul_eq_mul, Algebra.mul_smul_comm]
  simp [algebra_compatible_smul S, repr_lift_eq _ _ _ hf, compare_basis b c f hf]

include hf in
theorem lift_dpow_of_lift_eq_zero
    (x : DividedPowerAlgebra R M) (hx : x ∈ augIdeal R M)
    (hx' : LinearMap.lift S f x = 0) (hn : n ≠ 0) :
    LinearMap.lift S f (dpow b n x) = 0 := by
  rw [lift_dpow hf hx, hx', dpow_eval_zero _ hn]

end Compare

section CharZero

namespace CharZero

variable [CharZero R] [IsDomain R]

variable (R) in

abbrev S := FractionRing R

noncomputable local instance : Algebra ℚ (S R) := RingHom.toAlgebra
  (IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom _) (by
  intro y
  refine IsFractionRing.isUnit_map_of_injective ?_ y
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Int.cast_eq_zero (α := R), ← (FaithfulSMul.algebraMap_injective R (S R)).eq_iff]
  simpa using ha))

variable (ι R) in
abbrev N := ι →₀ (S R)

noncomputable abbrev c : Basis ι (S R) (N R ι) := Finsupp.basisSingleOne

noncomputable abbrev f : M →ₗ[R] (N R ι) := Basis.constr b (S R) c

omit  [DecidableEq ι][CharZero R] [IsDomain R] [DecidableEq R] in
lemma hf (i : ι) : f b (b i) = c i  := by simp [c, f]

local instance : IsScalarTower R (S R) (N R ι) := Finsupp.isScalarTower ι (S R)

omit [DecidableEq R] [DecidableEq ι] [IsDomain R] in
theorem lift_injective :
    Function.Injective (LinearMap.lift (S R) (f b)) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  rw [Basis.ext_elem_iff (basis (S R) (N R ι) c)] at hx
  rw [Basis.ext_elem_iff (basis R M b)]
  intro d
  specialize hx d
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hx ⊢
  simpa [repr_lift_eq b c (f b) (by exact hf b) x] using hx

omit [DecidableEq ι] [CharZero R] [IsDomain R] in
theorem augIdeal_map_lift_eq [DecidableEq (S R)] :
    (augIdeal R M).map (LinearMap.lift (S R) (f b)) = augIdeal (S R) (N R ι) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [mem_augIdeal_iff_of_repr c]
    rw [mem_augIdeal_iff_of_repr b] at hx
    simp [repr_lift_eq b c (f b) (by exact hf b), hx]
  · intro x hx
    rw [mem_augIdeal_iff_of_repr c] at hx
    rw [eq_of_repr c x]
    simp only [Finsupp.sum]
    apply Ideal.sum_mem
    intro d hd
    rw [Finsupp.mem_support_iff] at hd
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_left
    rw [compare_basis b c (f b) (by exact hf b)]
    apply Ideal.mem_map_of_mem
    simp only [mem_augIdeal_iff_of_repr b, Basis.repr_self]
    rw [Finsupp.single_eq_of_ne]
    intro hd'
    apply hd
    rw [hd', hx]

noncomputable
abbrev hSN : DividedPowers (augIdeal (S R) (N R ι)) :=
  RatAlgebra.dividedPowers (augIdeal (S R) (N R ι))

theorem lift_dpow_eq_dpow_lift
    (n : ℕ) {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    LinearMap.lift (S R) (f b) (dpow b n x) =
      hSN.dpow n ((LinearMap.lift (S R) (f b)) x) :=  by
  rw [dpow_eq _ ?_ c]
  apply lift_dpow (hf b) hx -- (by exact hf b) x hx
  intro n x
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ _ (ι_mem_augIdeal _ _ x)]
  simp only [Ring.inverse_eq_inv', DividedPowerAlgebra.ι, LinearMap.coe_mk, AddHom.coe_mk]
  have : Invertible (n ! : ℚ) := invertibleOfNonzero (by simp [Nat.factorial_ne_zero])
  rw [← invOf_eq_inv, invOf_smul_eq_iff, ← natFactorial_mul_dp_eq]
  simp [Algebra.smul_def]

/-- The divided power structure on the divided power algebra of a free module
over a characteristic zero domain -/
noncomputable def dividedPowers : DividedPowers (augIdeal R M) :=
  ofInjective (augIdeal R M) (augIdeal (S R) (N R ι))
    (LinearMap.lift (S R) (f b)) (lift_injective b) (hSN) (augIdeal_map_lift_eq b)
    (fun n x hx ↦ ⟨dpow b n x, fun hn ↦ dpow_mem b hn hx, lift_dpow_eq_dpow_lift _ _ hx⟩)

theorem dpow_eq (x : DividedPowerAlgebra R M) :
    (dividedPowers b).dpow n x = dpow b n x := by
  simp only [CharZero.dividedPowers, ofInjective]
  simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, dite_eq_ite]
  split_ifs with hx
  · rw [← lift_dpow_eq_dpow_lift, ← (lift_injective b).eq_iff]
    · exact Function.apply_invFun_apply
    · exact hx
  · rw [dpow_null b hx]

theorem dpow_ι_eq_dp (n: ℕ) (x : M) :
    (dividedPowers b).dpow n (DividedPowerAlgebra.ι R M x) = dp R n x := by
  rw [dpow_eq, dpow_ι]

end CharZero

end CharZero

section Quotient

noncomputable section

variable (R) in
private def MvPoly_dividedPowers :
    DividedPowers (augIdeal (MvPolynomial R ℤ) (ι →₀ (MvPolynomial R ℤ))) :=
  CharZero.dividedPowers Finsupp.basisSingleOne

local instance : Module (MvPolynomial R ℤ) M :=
  Module.compHom M (MvPolynomial.eval₂Hom (Int.castRingHom R) id)

local instance : Algebra (MvPolynomial R ℤ) R :=
  RingHom.toAlgebra (MvPolynomial.eval₂Hom (Int.castRingHom R) id)

local instance : IsScalarTower (MvPolynomial R ℤ) R M :=
  IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl

private def φ : R → (MvPolynomial R ℤ) := fun r ↦ if r = 0 then 0 else MvPolynomial.X r

lemma algebraMap_φ (r : R) : algebraMap (MvPolynomial R ℤ) R (φ r) = r := by
    simp only [RingHom.algebraMap_toAlgebra, φ]
    split_ifs with hr
    · simp [hr]
    · rw [MvPolynomial.coe_eval₂Hom]; simp

private def toN (x : DividedPowerAlgebra R M) :
    DividedPowerAlgebra (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) :=
  Finsupp.linearCombination (MvPolynomial R ℤ)
    (basis (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) Finsupp.basisSingleOne)
    (((basis R M b).repr x).mapRange φ (by simp [φ]))

omit [DecidableEq ι] in
lemma toN_repr (x : DividedPowerAlgebra R M) (d : ι →₀ ℕ) :
      ((basis (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) Finsupp.basisSingleOne).repr
        (toN b x) d) =  φ ((basis R M b).repr x d) := by
    simp only [toN]
    simp [Finsupp.linearCombination, Finsupp.lsum, map_finsuppSum]

omit [DecidableEq ι] in
lemma toNx (x) (hx : x ∈ augIdeal R M) :
    toN b x ∈ augIdeal  (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) := by
  rw [mem_augIdeal_iff_of_repr Finsupp.basisSingleOne]
  rw [mem_augIdeal_iff_of_repr b] at hx
  simp [toN_repr, hx, φ]

private def f : (ι →₀ MvPolynomial R ℤ) →ₗ[MvPolynomial R ℤ] M :=
  Finsupp.linearCombination (MvPolynomial R ℤ) (fun i ↦ b i)

omit [DecidableEq R] [DecidableEq ι] in
private lemma f_apply (i : ι) : (f b) (Finsupp.basisSingleOne i) = b i := by
    simp only [f]
    rw [Finsupp.coe_basisSingleOne, Finsupp.linearCombination_single, one_smul]

omit [DecidableEq R] [DecidableEq ι] in
private lemma lift_f (d : ι →₀ ℕ) :
    (LinearMap.lift R (f b))
      (basis (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) Finsupp.basisSingleOne d) =
    basis R M b d := by
  simp only [basis_eq, map_finsuppProd, LinearMap.lift_apply_dp]
  apply Finsupp.prod_congr
  intros; rw [f_apply]

omit [DecidableEq ι] in
private lemma id_eq_lift_toN (x : DividedPowerAlgebra R M) :
    x = LinearMap.lift R (f b) (toN b x) := by
  apply Basis.ext_elem (basis R M b)
  intro d
  simp only [toN, Finsupp.linearCombination, Finsupp.coe_lsum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, map_finsuppSum, map_smul, Finsupp.sum_apply]
  simp only [lift_f, algebra_compatible_smul R, Algebra.algebraMap_self, RingHomCompTriple.comp_apply,
    map_smul, Basis.repr_self, Finsupp.coe_smul, Pi.smul_apply]
  rw [Finsupp.sum_eq_single d]
  · simp only [Finsupp.mapRange_apply, Finsupp.single_eq_same,φ]
    split_ifs with hd
    · simp [hd]
    · simp [RingHom.algebraMap_toAlgebra]
  · intro _ _ hed; simp [Finsupp.single_eq_of_ne hed]
  · simp

-- TODO: golf
lemma lift_dpow_eq_of_lift_eq
    {u v : DividedPowerAlgebra (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ)}
    (hu : u ∈ augIdeal (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ))
    (hv : v ∈ augIdeal (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ))
    (huv : LinearMap.lift R (f b) u = LinearMap.lift R (f b) v) :
    LinearMap.lift R (f b) (dpow Finsupp.basisSingleOne n u) =
      LinearMap.lift R (f b) (dpow Finsupp.basisSingleOne n v) := by
  rw [lift_dpow (f_apply b) hu, lift_dpow (f_apply b) hv, huv]

--#count_heartbeats in
--set_option profiler true in
theorem dpow_add {x y : DividedPowerAlgebra R M}
    (hx : x ∈ augIdeal R M) (hy : y ∈ augIdeal R M) :
    dpow b n (x + y) = ∑ k ∈ Finset.antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
  classical
  -- set S := MvPolynomial R ℤ
  -- let N := ι →₀ S
  -- let f : N →ₗ[S] M := Finsupp.linearCombination S (fun i ↦ b i)
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, id_eq_lift_toN b y, ← map_add,
    ← lift_dpow (f_apply b) (Ideal.add_mem _ (toNx b x hx) (toNx b y hy)),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.dpow_add _ (toNx b x hx) (toNx b y hy)]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [dpow_eq _ (CharZero.dpow_ι_eq_dp c) c]
  rw [lift_dpow (f_apply b) (toNx b x hx), ← id_eq_lift_toN b x,
    lift_dpow (f_apply b) (toNx b y hy), ← id_eq_lift_toN b y]

theorem dpow_sum {α : Type*} [DecidableEq α] (x : α → DividedPowerAlgebra R M) {s : Finset α}
  (hx : ∀ a ∈ s, x a ∈ augIdeal R M) :
    dpow b n (∑ a ∈ s, x a) =
      ∑ k ∈ s.sym n, ∏ d ∈ s, dpow b (Multiset.count d ↑k) (x d) :=
  DividedPowers.dpow_sum' (dpow b) (fun a ↦ dpow_zero b a) (fun a a_1 ↦ dpow_add b a a_1)
    (fun a ↦ dpow_eval_zero b a) hx

theorem dpow_mul {a x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b n (a * x) = a ^ n * dpow b n x := by
  classical
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b a, id_eq_lift_toN b x, ← map_mul,
    ← lift_dpow (f_apply b) (Ideal.mul_mem_left _ _ (toNx b x hx)),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.dpow_mul _ (toNx b x hx), map_mul,
    map_pow, dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, ← id_eq_lift_toN b a,
    lift_dpow (f_apply b) (toNx b x hx), ← id_eq_lift_toN b x]

theorem mul_dpow {m n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b m x * dpow b n x = ↑((m + n).choose m) * dpow b (m + n) x := by
  classical
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, ← lift_dpow (f_apply b) (toNx b x hx),
    ← lift_dpow (f_apply b) (toNx b x hx), ← map_mul, ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c,
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.mul_dpow _ (toNx b x hx),
    map_mul, map_natCast, dpow_eq _ (CharZero.dpow_ι_eq_dp c) c,
    lift_dpow (f_apply b) (toNx b x hx)]

theorem dpow_comp {m n : ℕ} {x : DividedPowerAlgebra R M} (hn : n ≠ 0) (hx : x ∈ augIdeal R M) :
    dpow b m (dpow b n x) = ↑(m.uniformBell n) * dpow b (m * n) x := by
  classical
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, ← lift_dpow (f_apply b) (toNx b x hx),
    ← lift_dpow (f_apply b) (dpow_mem _ hn ((toNx b x hx))),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c,
    DividedPowers.dpow_comp _ hn (toNx b x hx), map_mul, map_natCast,
    dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, lift_dpow (f_apply b) (toNx b x hx)]

def dividedPowers : DividedPowers (augIdeal R M) where
  dpow := dpow b
  dpow_null := dpow_null b
  dpow_zero := dpow_zero b
  dpow_one := dpow_one b
  dpow_mem := dpow_mem b
  dpow_add := dpow_add b
  dpow_mul := dpow_mul b
  mul_dpow := mul_dpow b
  dpow_comp := dpow_comp b

theorem dpow_eq_dp (n : ℕ) (x : M) :
    (dividedPowers b).dpow n (DividedPowerAlgebra.ι R M x) = dp R n x := by
  simp only [dividedPowers, dpow_ι]

end

end Quotient

end Free

section General

variable {M}
variable {L : Type*} [AddCommGroup L] [Module R L] [Module.Free R L]
variable {f : L →ₗ[R] M}

-- This is a difficult theorem, proved in [Roby-1963], Prop. IV.8
theorem LinearMap.ker_lift_of_surjective (hf : Function.Surjective f) :
    RingHom.ker (LinearMap.lift R f) =
      Ideal.span (Set.range fun (nm : PNat × (LinearMap.ker f)) ↦ dp R nm.1 (nm.2 : L)) := by
  apply le_antisymm
  · sorry
  · -- This inclusion is easy, I prove it at once, as a safety check
    rw [span_le]
    rintro _ ⟨⟨n, ⟨q, hq⟩⟩, rfl⟩
    simp only [LinearMap.mem_ker] at hq
    simp [SetLike.mem_coe, RingHom.mem_ker, LinearMap.lift_apply_dp, hq, dp_null]

theorem isSubDPIdeal_of_free
    [DecidableEq R]
    {L : Type*} [AddCommGroup L] [Module R L] [Module.Free R L]
    (hL : DividedPowers (augIdeal R L))
    (dpow_eq_dp : ∀ (n : ℕ) (x : L), hL.dpow n (ι R L x) = dp R n x)
    (f : L →ₗ[R] M)
    (hf : Function.Surjective f) :
    hL.IsSubDPIdeal (RingHom.ker (LinearMap.lift R f)) := by
  rw [LinearMap.ker_lift_of_surjective R hf, hL.span_isSubDPIdeal_iff]
  · rintro n hn _ ⟨⟨⟨q, hq⟩, ⟨l, hl⟩⟩, rfl⟩
    simp only [PNat.mk_coe]
    rw [← dpow_eq_dp, hL.dpow_comp (Nat.ne_zero_of_lt hq) (ι_mem_augIdeal R L l)]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    rw [dpow_eq_dp]
    exact ⟨(⟨n * q, Nat.mul_pos (Nat.zero_lt_of_ne_zero hn) hq⟩,
      ⟨l, hl⟩), rfl⟩
  · rintro _ ⟨⟨⟨q, hq⟩, ⟨l, hl⟩⟩, rfl⟩
    simp only [PNat.mk_coe, SetLike.mem_coe]
    exact dp_mem_augIdeal R L hq l


noncomputable section

variable (M) in
/-- A presentation of a module by a free module with a basis -/
structure Presentation where
    s : Set M
    L : Type*
    dec_s : DecidableEq s
    acgL : AddCommGroup L
    mRL : Module R L
    b : Basis s R L
    f : L →ₗ[R] M
    surj : Function.Surjective f

variable (M) in
/-- The basic presentation of a module -/
def presentation [DecidableEq M] : Presentation R M where
  s := (Set.univ : Set M)
  L := Set.univ →₀ R
  dec_s := inferInstance
  acgL := inferInstance
  mRL := inferInstance
  b := Finsupp.basisSingleOne
  f := Finsupp.linearCombination R (fun m ↦ (m : M))
  surj := fun m ↦ ⟨Finsupp.single ⟨m, Set.mem_univ m⟩ 1, by
    simp [Finsupp.linearCombination_single]⟩

namespace Presentation

variable [DecidableEq R] (hL : DividedPowers (augIdeal R L))


variable (p : Presentation R M)

private instance : AddCommGroup p.L := p.acgL

private instance : Module R p.L := p.mRL

private instance : Module.Free R p.L := Module.Free.of_basis p.b

private instance : DecidableEq p.s := p.dec_s

theorem isSubDPIdeal (p : Presentation R M) :
    IsSubDPIdeal (Free.dividedPowers p.b)
      (RingHom.ker (LinearMap.lift R p.f).toRingHom ⊓ augIdeal R p.L) := by
  apply IsSubDPIdeal.mk
  · simp
  · intro n hn x hx
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_inf, RingHom.mem_ker, RingHom.coe_coe] at hx
    constructor
    · exact (isSubDPIdeal_of_free R (Free.dividedPowers p.b) (Free.dpow_eq_dp p.b) p.f p.surj).dpow_mem n hn hx.1
    · apply DividedPowers.dpow_mem _ hn hx.2

variable {R} in
def dividedPowers (p : Presentation R M) :
    DividedPowers (augIdeal R M) := by
  letI _ : AddCommGroup p.L := p.acgL
  letI _ : Module R p.L := p.mRL
  exact DividedPowers.Quotient.OfSurjective.dividedPowers
    (Free.dividedPowers p.b) (augIdeal R M)
    (LinearMap.lift_surjective_of p.surj)
    (LinearMap.augIdeal_map_lift R p.L p.f p.surj).symm
    p.isSubDPIdeal

variable {R} in
theorem dpow_eq_dp (p : Presentation R M) (n : ℕ) (x : M) :
    (dividedPowers p).dpow n (ι R M x) = dp R n x := by
  simp only [dividedPowers]
  obtain ⟨y, rfl⟩ := p.surj x
  rw [← LinearMap.lift_ι_apply]
  erw [Quotient.OfSurjective.dpow_apply
    (Free.dividedPowers p.b) (augIdeal R M)
    (LinearMap.lift_surjective_of p.surj)
    (LinearMap.augIdeal_map_lift R p.L p.f p.surj).symm
    p.isSubDPIdeal (ι_mem_augIdeal _ _ y) (n := n)]
  simp [Free.dpow_eq_dp p.b, LinearMap.lift_apply_dp]

end Presentation

variable [DecidableEq R] [DecidableEq M]

variable (M) in
/-- The canonical divided powers structure on a divided power algebra -/
def dividedPowers : DividedPowers (augIdeal R M) :=
  (presentation R M).dividedPowers

theorem dpow_eq_dp (n : ℕ) (x : M) :
    (dividedPowers R M).dpow n (ι R M x) = dp R n x :=
  (presentation R M).dpow_eq_dp n x

end

end General

end DividedPowerAlgebra
