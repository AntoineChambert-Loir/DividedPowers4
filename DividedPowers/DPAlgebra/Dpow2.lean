import DividedPowers.DPAlgebra.Graded.GradeZero
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.PowerSeries.PiTopology

/-! # Construction of the divided power structure on the divided power algebra
-/

section

open DividedPowers

variable {R : Type*} [CommSemiring R] {I : Ideal R} (hI : DividedPowers I)

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem DividedPowers.dpow_finsupp_sum {ι : Type*} [DecidableEq ι] {x : ι →₀ R} (hx : ∀ i, x i ∈ I)
    {n : ℕ} :
    hI.dpow n (x.sum fun _ r ↦ r) =
      ∑ k ∈ (x.support.sym n), x.prod fun i r ↦ hI.dpow (Multiset.count i k) r := by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ ↦ hx i), Finsupp.prod]

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem DividedPowers.dpow_linearCombination {A : Type*} [CommSemiring A] [Algebra R A]
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

end

noncomputable section

open DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

namespace DividedPowerAlgebra

universe u v v₁ v₂ w uA uR uS uM

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

-- variable [DecidableEq R]

variable (x : M) (n : ℕ)

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

section Free

/-- The basis of the graded part of `DividedPowerAlgebra R M` associated with a basis of `M`. -/
def basis_grade {ι : Type*} (b : Basis ι R M) (n : ℕ) :
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
def basis {ι : Type*} (b : Basis ι R M) :
    Basis (ι →₀ ℕ) R (DividedPowerAlgebra R M) := by
  apply Basis.mk (v := fun d ↦ d.prod (fun i k ↦ dp R k (b i)))
  sorry
  sorry

theorem isFree [Module.Free R M] : Module.Free R (DividedPowerAlgebra R M) :=
  Module.Free.of_basis (basis R M (Module.Free.chooseBasis R M))

variable {R M} {ι : Type*} (b : Basis ι R M)

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
  · simp [prod_singleton, Finsupp.single_eq_same]
  · simp [mem_singleton, forall_eq, dp_zero]

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
  simp [map_finsupp_sum]
  simp only [← basis_single_one_eq, Basis.repr_self, Finsupp.single_apply]
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

lemma basis_mem_augIdeal [DecidableEq R] {d : ι →₀ ℕ} (hd : d ≠ 0) :
    basis R M b d ∈ augIdeal R M := by
  simp only [mem_augIdeal_iff, basis_eq, map_finsupp_prod, algebraMapInv_dp]
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
  simp only [basis_zero_eq_one, Finsupp.mem_support_iff, ne_eq, gt_iff_lt,
    mem_augIdeal_iff, map_smul, map_one]
  simp [smul_eq_mul, mul_one]

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

theorem _root_.Finset.prod_smul' {α β ι : Type*}
    [CommMonoid β] [CommMonoid α] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β]
    (s : Finset ι) (b : ι → α) (f : ι → β) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on with
  | h₁ =>  simp
  | h₂ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

theorem _root_.DividedPowers.dpow_prod {I : Ideal R} (hI : DividedPowers I)
  {ι : Type*} [DecidableEq ι] {r : ι → R} {s : Finset ι}
  (hs : s.Nonempty) (hs' : ∀ i ∈ s, r i ∈ I) {n : ℕ} :
    hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i)) := by
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_not_mem has, add_tsub_cancel_right,
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
      simp only [h, prod_empty, mul_one, insert_emptyc_eq, card_singleton, tsub_self, pow_zero,
        prod_singleton, one_smul]

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
        sum_eq_zero_iff, mem_insert, forall_eq_or_imp, not_and, not_forall, Classical.not_imp,
        not_exists, Decidable.not_not] at hi
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

      /-
(∑ d ∈ ((basis R M b).repr x).support, Multiset.count d ↑k • d) =  ??

k = k_1, ... , k_n : unordered n-tuple of (ι →₀ ℕ)
((basis R M b).repr x).support : Finset (ι →₀ ℕ)
∀ a, k_a ∈ ((basis R M b).repr x

Multiset.count d ↑k : how many a are there such that k_a = d
Multiset.count d ↑k • d : ι →₀ ℕ

-/

theorem _root_.Sym.sum_eq_val_sum {ι : Type*} [DecidableEq ι] {n : ℕ}
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

/-- A combinatorial coefficient that appears in the definition of the divided power structure
of the divided power algebra -/
def cK [DecidableEq ι] {n : ℕ} (k : Sym (ι →₀ ℕ) n) (s : Finset (ι →₀ ℕ)) : ℕ :=
  (k.val.sum.prod fun i _ ↦ Nat.multinomial s fun a ↦ (Multiset.count a ↑k • a) i) *
  (∏ d ∈ s, (Multiset.count d ↑k)! ^ (#d.support - 1) • ∏ i ∈ d.support, (Multiset.count d ↑k).uniformBell (d i))

theorem _root_.Nat.multinomial_congr_of_sdiff
    {α : Type*} [DecidableEq α] {f g : α → ℕ} {s t : Finset α}
    (hst : s ⊆ t) (H1 : ∀ a ∈ t \ s, g a = 0) (H2 : ∀ a ∈ s, f a = g a) :
    Nat.multinomial s f = Nat.multinomial t g := by
  rw [← Nat.mul_right_inj (a := ∏ a ∈ t, (g a)!), Nat.multinomial_spec,
    ← Finset.sum_subset_zero_on_sdiff hst H1 H2, ← Nat.multinomial_spec s f]
  · apply congr_arg₂ _ _ rfl
    symm
    apply Finset.prod_subset_one_on_sdiff hst
    · intro x hx
      rw [H1 x hx, Nat.factorial_zero]
    · intro x hx
      rw [H2 x hx]
  · simp only [ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and]
    intro x hx
    exact Nat.factorial_ne_zero (g x)

theorem cK_eq_of_subset [DecidableEq ι] {n : ℕ} {k : Sym (ι →₀ ℕ) n}
    {s t : Finset (ι →₀ ℕ)} (hst : s ⊆ t) (hk : k ∈ s.sym n) : cK k s = cK k t := by
  have H0 (d) (hd : d ∉ s) : Multiset.count d ↑k = 0 := by
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hd
    simp only [mem_sym_iff, Finsupp.mem_support_iff, ne_eq] at hk
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

/- Is there a better formula ? -/
theorem dpow_eq [DecidableEq R] (H : DividedPowers (augIdeal R M))
    (hH : ∀ (n : ℕ) (x : M), H.dpow n (DividedPowerAlgebra.ι R M x) = dp R n x)
    {ι : Type*} [DecidableEq ι] (b : Basis ι R M) {n : ℕ} {x : DividedPowerAlgebra R M}
    (hx : x ∈ augIdeal R M) :
    H.dpow n x =
      ∑ k ∈ ((basis R M b).repr x).support.sym n,
        cK k ((basis R M b).repr x).support •
          (∏ d ∈ ((basis R M b).repr x).support, ((basis R M b).repr x) d ^ Multiset.count d ↑k) •
            (basis R M b) k.val.sum := by
  nth_rewrite 1 [eq_of_basis b x]
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

/-- The `dpow` function on the divided power algebra of a free module -/
def dpow {ι : Type*} (b : Basis ι R M) (n : ℕ) (x : DividedPowerAlgebra R M) :
    DividedPowerAlgebra R M := by
  classical
  exact
    if x ∈ augIdeal R M then
      ∑ k ∈ ((basis R M b).repr x).support.sym n,
        cK k ((basis R M b).repr x).support •
          (∏ d ∈ ((basis R M b).repr x).support, ((basis R M b).repr x) d ^ Multiset.count d ↑k) •
              (basis R M b) k.val.sum
    else 0

open scoped Classical in
theorem dpow_eq_of_support_subset {ι : Type*} (b : Basis ι R M) (n : ℕ)
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

theorem dpow_ι (n : ℕ) (m : M) :
    dpow b n (DividedPowerAlgebra.ι R M m) = dp R n m := by
  classical
  simp only [dpow, if_pos (ι_mem_augIdeal R M m)]
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
    have := (Basis.linearCombination_repr b m).symm
    simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  let g (n) : Sym ι n ↪ Sym (ι →₀ ℕ) n := {
    toFun a := Sym.map (fun i ↦ Finsupp.single i 1) a
    inj' := by
      apply Sym.map_injective
      intro i j h
      rwa [Finsupp.single_left_inj Nat.one_ne_zero] at h }
  conv_rhs =>
    rw [hm]
    simp only [Finsupp.sum]
    rw [dp_sum _ (b.repr m).support n]
  rw [← Finset.sum_fiberwise_of_maps_to (g := g n)]
  apply Finset.sum_congr rfl
  · intro k hk
    set s := (b.repr m).support with hs
    simp only [ι_repr_support_eq, ← hs] at hk ⊢
    simp only [mem_sym_iff, mem_map, Finsupp.mem_support_iff, ne_eq,
      Function.Embedding.coeFn_mk] at hk
    sorry
  · intro k hk
    simp only [g]
    rw [mem_sym_iff]
    intro d
    simp only [Function.Embedding.coeFn_mk, Sym.mem_map, Finsupp.mem_support_iff, basis_repr_ι,
      ne_eq, dite_eq_right_iff, forall_exists_index, not_forall, and_imp, g]
    intro i hi hd
    use i
    use hd.symm
    intro H
    simp only [mem_sym_iff, Finsupp.mem_support_iff] at hk
    apply hk i hi
    rw [← H]
    apply congr_arg
    have : ∃ i, d = Finsupp.single i 1 := ⟨i, hd.symm⟩
    rw [← Finsupp.single_left_inj Nat.one_ne_zero, ← this.choose_spec, hd]
/-    simp only [Function.Embedding.coeFn_mk, Sym.mem_map, Finsupp.mem_support_iff, ne_eq,
      forall_exists_index, and_imp, g]
    simp only [Sym.mem_map, g]
    rintro ⟨i, hi, rfl⟩
    simp only [Finsupp.mem_support_iff, ne_eq, g]
    rw [hm, map_finsupp_sum, map_finsupp_sum]
    intro h
    simp only [map_smul, Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, g] at h
    simp only [mem_sym_iff, Finsupp.mem_support_iff, ne_eq, g] at hk
    apply hk i hi
    rw [Finsupp.sum_eq_single i] at h
    · rw [← h, eq_comm]
      convert mul_one _
      rw [← basis_single_one_eq, Basis.repr_self, Finsupp.single_eq_same]
    · intro j hj hji
      rw [← basis_single_one_eq, Basis.repr_self, Finsupp.single_eq_of_ne, mul_zero]
      rw [ne_eq, Finsupp.single_left_inj Nat.one_ne_zero]
      exact hji
    · simp -/

-- TODO: golf and speed up
open Classical in
lemma repr_dp_one /- [ DecidableEq ι] -/ (m : M) : (basis R M b).repr (dp R 1 m) =
    ∑ x ∈ (b.repr m).support, (((b.repr m) x) • (basis R M b).repr
          ((basis R M b) (Multiset.toFinsupp (Sym.oneEquiv x)))) := by
  classical
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
      have := (Basis.linearCombination_repr b m).symm
      simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  simp only [Finsupp.sum] at hm
  conv_lhs =>
    rw [hm, dp_sum]
    simp only [sym_succ, Nat.succ_eq_add_one, Nat.reduceAdd, sym_zero, image_singleton,
      sup_singleton'', Finsupp.mem_support_iff, ne_eq, Sym.cons_inj_left, imp_self, implies_true,
      sum_image, map_sum]
    simp only [dp_smul, Finset.prod_smul', map_smul]
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
        sup_singleton'', hx' x, Sym.oneEquiv_apply, mem_image, Finsupp.mem_support_iff, ne_eq]
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
      simp [hyx']


theorem dpow_null {n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∉ augIdeal R M) :
    dpow b n x = 0 := by
  simp [dpow, if_neg hx]

theorem cK_zero [DecidableEq ι] {k : Sym (ι →₀ ℕ) 0} {s : Finset (ι →₀ ℕ)} :
    cK k s = 1 := by
  simp [cK, Subsingleton.eq_zero k, Nat.uniformBell_zero_left]

theorem dpow_zero {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 0 x = 1 := by
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp [dpow, if_pos hx, this, Nat.uniformBell_zero_left, basis_eq, cK_zero]

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

theorem cK_one [DecidableEq ι] {s : Finset (ι →₀ ℕ)} {k : Sym (ι →₀ ℕ) 1} :
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
    · simp [kval, Nat.uniformBell_one_left]
  · intro c hc hcd
    simp [Multiset.count_singleton, if_neg hcd, Nat.uniformBell_zero_left, kval]
  · intros
    simp [Multiset.count_singleton, Nat.uniformBell_one_left]

theorem dpow_one {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 1 x = x := by
  classical
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp only [dpow, if_pos hx]
  conv_rhs => rw [eq_of_basis b x]
  simp only [sym_succ, Nat.succ_eq_add_one, Nat.reduceAdd, sym_zero, this, image_singleton,
    sup_singleton'', Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm, Finsupp.mem_support_iff,
    ne_eq, Sym.cons_inj_left, imp_self, implies_true, sum_image, Sym.coe_cons, Sym.toMultiset_zero,
    Multiset.cons_zero, Multiset.nodup_singleton, Multiset.count_singleton, pow_ite, pow_one,
    pow_zero, prod_ite_eq', ite_not, Multiset.sum_singleton, ite_smul, one_smul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [cK_one, Nat.cast_one, one_mul, ite_eq_right_iff]
  intro h
  simp only [Finsupp.mem_support_iff] at hd
  exact (hd h).elim

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : dpow b n 0 = 0 := by
  simp only [dpow, if_pos (Ideal.zero_mem _)]
  simp [(Finset.sym_eq_empty (s := ∅) (n := n)).mpr ?_, hn]

theorem dpow_mem [DecidableEq R] {n : ℕ} {x : DividedPowerAlgebra R M} (hn : n ≠ 0) (hx : x ∈ augIdeal R M) :
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

def dpowExp (x : DividedPowerAlgebra R M) : PowerSeries (DividedPowerAlgebra R M) :=
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
  simp [dpowExp, dpow_eq_of_support_subset b _ hx hs, Sym.val_eq_coe, nsmul_eq_mul,
    Algebra.mul_smul_comm, PowerSeries.coeff_mk, map_sum, LinearMap.map_smul_of_tower]

theorem dpow_add {n : ℕ} {x y : DividedPowerAlgebra R M}
    (hx : x ∈ augIdeal R M) (hy : y ∈ augIdeal R M) :
    dpow b n (x + y) = ∑ k ∈ Finset.antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
  classical
  set s := ((basis R M b).repr x).support ∪ ((basis R M b).repr y).support with hs
  calc dpow b n (x + y)
    _ = ∑ k ∈ s.sym n, cK k s • (∏ d ∈ s, ((basis R M b).repr (x + y)) d ^ Multiset.count d ↑k) •
      (basis R M b) (k :  Multiset (ι →₀ ℕ)).sum := by
      rw [dpow_eq_of_support_subset (s := s) b n (Ideal.add_mem _ hx hy)
       (fun d ↦ by
        simp only [map_add, Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
          ne_eq, hs, mem_union, ← not_and_or, not_imp_not]
        rintro ⟨hx', hy'⟩
        rw [hx', hy', add_zero])]; rfl
    _ = ∑ x_1 ∈ (antidiagonal n).sigma fun a ↦ s.sym a.2 ×ˢ s.sym a.1,
          cK x_1.snd.2 s •
              (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d x_1.snd.2) •
              (basis R M b) (x_1.snd.2 : Multiset (ι →₀ ℕ)).sum * cK x_1.snd.1 s •
              (∏ d ∈ s, ((basis R M b).repr y) d ^ Multiset.count d x_1.snd.1) •
              (basis R M b) (x_1.snd.1 : Multiset (ι →₀ ℕ)).sum := by
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, add_pow, nsmul_eq_mul,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      sorry
    _ = ∑ k ∈ antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
      conv_rhs => rw [Finset.sum_congr rfl (fun k hk ↦ congr_arg₂ HMul.hMul
          (dpow_eq_of_support_subset (s := s) b k.1 hx subset_union_left)
          (dpow_eq_of_support_subset (s := s) b k.2 hy subset_union_right))]
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_product', Finset.sum_sigma']
      rfl

-- Copied from Bhavik's PR
lemma _root_.antidiagonal_eq_filter {A : Type*} [OrderedAddCommMonoid A] [CanonicallyOrderedAdd A]
    [LocallyFiniteOrder A] [DecidableEq A] [HasAntidiagonal A] (n : A) :
    antidiagonal n = (Iic n ×ˢ Iic n).filter (fun x : A × A ↦ x.1 + x.2 = n) := by
  ext ⟨i, j⟩
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_Iic, iff_and_self]
  rintro rfl
  simp

nonrec lemma _root_.Nat.antidiagonal_eq_filter (n : ℕ) :
    antidiagonal n = (Icc 0 n ×ˢ Icc 0 n).filter (fun x : ℕ × ℕ ↦ x.1 + x.2 = n) := by
  rw [antidiagonal_eq_filter, Iic_eq_Icc, bot_eq_zero]

  /- What is needed:
    * expand `(basis R M b).repr (x + y) d ^ Multiset.count d ↑k`
    using the multinomial formula
    * distribute in the product, here, one needs a formula of the type
     `Finset.prod_add_distrib`, this gives a sum of a mul of two products
    * the two products naturally decompose `k` as a sum `k1 + k2`
-/

theorem dpow_add'' {n : ℕ} {x y : DividedPowerAlgebra R M}
    (hx : x ∈ augIdeal R M) (hy : y ∈ augIdeal R M) :
    dpow b n (x + y) = ∑ k ∈ Finset.antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
  classical
  set s := ((basis R M b).repr x).support ∪ ((basis R M b).repr y).support with hs
  calc dpow b n (x + y)
  _ = ∑ k ∈ s.sym n, cK k s • (∏ d ∈ s, ((basis R M b).repr (x + y)) d ^ Multiset.count d ↑k) •
      (basis R M b) (k : Multiset (ι →₀ ℕ)).sum := by
      rw [dpow_eq_of_support_subset (s := s) b n (Ideal.add_mem _ hx hy)
       (fun d ↦ by
        simp only [map_add, Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
          ne_eq, hs, mem_union, ← not_and_or, not_imp_not]
        rintro ⟨hx', hy'⟩
        rw [hx', hy', add_zero])]; rfl
  _ = ∑ x_1 ∈ s.sym n, (∏ x_2 ∈ s, ∑ m ∈ range (Multiset.count x_2 ↑x_1 + 1),
          ((basis R M b).repr x) x_2 ^ m * ((basis R M b).repr y) x_2 ^
            (Multiset.count x_2 ↑x_1 - m) * ↑((Multiset.count x_2 ↑x_1).choose m)) •
        ((cK x_1 s) * (basis R M b) (x_1 : Multiset (ι →₀ ℕ)).sum) := by
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, add_pow, nsmul_eq_mul,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  _ = ∑ p ∈ Icc 0 n, ∑ q ∈ Icc 0 n,
        if p + q = n then dpow b p x * dpow b q y else 0 := by sorry
  _ = ∑ k ∈ antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
    rw [Nat.antidiagonal_eq_filter, sum_filter, sum_product]

theorem dpow_add' {n : ℕ} {x y : DividedPowerAlgebra R M}
    (hx : x ∈ augIdeal R M) (hy : y ∈ augIdeal R M) :
    dpow b n (x + y) = ∑ k ∈ Finset.antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
  classical
  set s := ((basis R M b).repr x).support ∪ ((basis R M b).repr y).support with hs
  rw [dpow_eq_of_support_subset (s := s) b n (Ideal.add_mem _ hx hy)
    (fun d ↦ by
      simp only [map_add, Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply,
        ne_eq, hs, mem_union, ← not_and_or, not_imp_not]
      rintro ⟨hx', hy'⟩
      rw [hx', hy', add_zero])]
  rw [Finset.sum_congr rfl (fun k hk ↦ congr_arg₂ HMul.hMul
    (dpow_eq_of_support_subset (s := s) b k.1 hx subset_union_left)
    (dpow_eq_of_support_subset (s := s) b k.2 hy subset_union_right))]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_product']
  simp only [Finset.sum_sigma']

  sorry

open Classical in
theorem dpow_sum {α : Type*} (x : α → DividedPowerAlgebra R M) {s : Finset α}
  (hx : ∀ a ∈ s, x a ∈ augIdeal R M) (n : ℕ) :
    dpow b n (∑ a in s, x a) =
      ∑ k ∈ s.sym n, ∏ d ∈ s, dpow b (Multiset.count d ↑k) (x d) := by
  apply DividedPowers.dpow_sum' (dpow b)
  · exact fun {x} a ↦ dpow_zero b a
  · exact fun {n} {x y} a a_1 ↦ dpow_add'' b a a_1
  · exact fun {n} a ↦ dpow_eval_zero b a
  · exact hx


example (α : Type*) [DecidableEq α] (n : ℕ) (s : Finset α) :
    (antidiagonal n).sigma (fun k ↦ s.sym k.2 ×ˢ s.sym k.1) ≃ s.sym n := sorry
 -- ∑ x_1 ∈ (antidiagonal n).sigma fun a ↦ s.sym a.2 ×ˢ s.sym a.1,

example (a b c d : ℕ) (h : a = c) (k : b = d) : a + b = c + d := by
  apply congr_arg₂ _ h k

theorem dpow_mul {n : ℕ} {a x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b n (a * x) = a ^ n * dpow b n x := by
  classical
  set s :=  ((basis R M b).repr (a * x)).support  ∪ ((basis R M b).repr x).support with hs
  rw [dpow_eq_of_support_subset (s := s) b n (mul_mem_left _ a hx) subset_union_left,
    dpow_eq_of_support_subset (s := s) b n hx subset_union_right, mul_sum]
  congr
  ext m
  simp only [← nsmul_eq_mul, Algebra.mul_smul_comm]
  congr 1
  rw [← Algebra.mul_smul_comm]
  sorry

theorem mul_dpow {m n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b m x * dpow b n x = ↑((m + n).choose m) * dpow b (m + n) x := by
  classical
  simp only [dpow, if_pos hx]
  rw [Finset.sum_mul_sum, ← Finset.sum_product', mul_sum]
  simp only [Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  simp only [← smul_assoc]
  simp only [← Finset.prod_smul']
  simp only [smul_eq_mul, ← pow_add]


  sorry


theorem dpow_mul' {n : ℕ} {a x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b n (a * x) = a ^ n * dpow b n x := by
  induction a using DividedPowerAlgebra.induction_on generalizing n x with
  | h_C r =>
    rw [dpow_eq_of_support_subset b n ?_ (s := ((basis R M b).repr x).support)]
    · simp only [dpow, if_pos hx, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [← smul_assoc]
      simp only [algHom_C, ← Algebra.smul_def, map_smul, ← map_pow]
      classical
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Sym.val_eq_coe]
      simp only [mul_pow, Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      suffices ∑ i in  ((basis R M b).repr x).support,
        Multiset.count i ↑k = n by
        rw [this, ← mul_assoc, mul_comm _ (r ^ n), mul_assoc]
        simp [Algebra.smul_def]
        ring
      conv_rhs => rw [← Sym.card_coe (s := k)]
      rw [Multiset.sum_count_eq_card]
      simpa only [mem_sym_iff] using hk
    · intro d
      simp only [Finsupp.mem_support_iff, ne_eq, not_imp_not]
      intro hd
      simp [algHom_C, ← Algebra.smul_def, hd]
    · exact mul_mem_left (augIdeal R M) (mk (C r)) hx
  | h_add f g hf hg =>
    rw [add_mul, dpow_add, (Commute.all f g).add_pow', Finset.sum_mul]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hf hx, hg hx]
      simp only [mem_antidiagonal] at hk
      rw [mul_mul_mul_comm, mul_dpow b hx, hk]
      ring
    · exact mul_mem_left (augIdeal R M) f hx
    · exact mul_mem_left (augIdeal R M) g hx
    --simp_rw [dpow_eq]
    /- simp only [dpow, Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm, mul_ite, ite_mul,
      zero_mul, mul_zero, sum_ite_irrel, sum_const_zero] -/
    --rw [mem_augIdeal_iff_of_repr] at hx
  | h_dp f p m hf =>
    classical
    rw [mul_assoc, hf, mul_pow, mul_assoc]
    apply congr_arg₂ _ rfl
    have : m = ((b.repr m).sum fun i c ↦ c • b i) := by
      have := (Basis.linearCombination_repr b m).symm
      simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
    simp only [Finsupp.sum] at this
    rw [this, dp_sum, Finset.sum_mul, dpow_sum]
    rw [dpow_eq_of_support_subset b n ?_ (s := ((basis R M b).repr x).support)]
    simp only [dpow, if_pos hx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    conv_rhs => rw [mul_comm]
    simp only [smul_mul_assoc]
    apply congr_arg₂ _ rfl

    suffices dpow b n (f * dp R p m * x) = (dp R p m * f) ^ n * dpow b n x by
      rw [this]; ring
    rw [mul_assoc, hf]
    sorry

example (p : ℕ) (m : M) (x : DividedPowerAlgebra R M) (d : ι →₀ ℕ) :
    ((basis R M b).repr (dp R p m * x)) d = 0 := by
  classical
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
    have := (Basis.linearCombination_repr b m).symm
    simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  have (x) (hx : x ∈ (b.repr m).support.sym p) := basis_eq' b hx
  have hx := eq_of_basis b x
  have : dp R p m = dpow b p (DividedPowerAlgebra.ι R M m) := sorry
  simp only [Finsupp.sum] at hm hx
  rw [hm]
  rw [dp_sum]
  simp_rw [dp_smul, Finset.prod_smul']

  rw [hx, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  -- simp_rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_comm]
  simp [dp_smul]
  simp only [Finset.prod_smul']
  simp [Finset.sum_congr (s₁ := (b.repr m).support.sym p) rfl
    (fun x hx ↦ by
      sorry)]
  simp_rw [← this]
  sorry


theorem dpow_mul'' {n : ℕ} {a x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b n (a * x) = a ^ n * dpow b n x := by
  classical
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    rw [dpow_zero b (mul_mem_left _ a hx), dpow_zero b hx]
  | succ n hn =>
    set s :=  ((basis R M b).repr (a * x)).support  ∪ ((basis R M b).repr x).support with hs
    rw [dpow_eq_of_support_subset (s := s) b _ (mul_mem_left _ a hx) subset_union_left,
      dpow_eq_of_support_subset (s := s) b _ hx subset_union_right] at hn ⊢
    simp only [dpow, if_pos (mul_mem_left _ a hx), if_pos hx, sym_succ] at hn ⊢
    simp only [Nat.succ_eq_add_one, Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm,
    Finset.mul_sum] at hn ⊢
    rw [@sup_eq_biUnion]
    /- rw [Finset.sum_biUnion] -- I don't think this can be applied
    rw [Finset.sum_biUnion]
    simp only [mem_sym_iff, Sym.cons_inj_right, imp_self, implies_true, sum_image]
    simp only [Sym.cons, Nat.succ_eq_add_one, Sym.val_eq_coe, Sym.coe_mk, Multiset.sum_cons]
    simp only [Multiset.count_cons]
    simp only [pow_add, pow_ite, pow_one, pow_zero, mul_ite, mul_one]
    simp only [prod_ite]
    sorry

    · -- Indeed, not true (required for Finset.sum_biUnion)
      simp only [Set.PairwiseDisjoint, Set.Pairwise, mem_coe, ne_eq]
      intro x hx y hy hxy
      refine disjoint_iff_ne.mpr ?_
      intro b' hb c' hc
      simp only [mem_image, mem_sym_iff] at hb hc
      obtain ⟨b, hb, rfl⟩ := hb
      obtain ⟨c, hc, rfl⟩ := hc
      sorry -/
    sorry

theorem dpow_comp {m n : ℕ} {x : DividedPowerAlgebra R M} (hn : n ≠ 0)
    (hx : x ∈ augIdeal R M) :
    dpow b m (dpow b n x) = ↑(m.uniformBell n) * dpow b (m * n) x := by
  classical
  set s :=  ((basis R M b).repr (dpow b n x)).support ∪ ((basis R M b).repr x).support with hs
  rw [dpow_eq_of_support_subset (s := s) b m (dpow_mem b hn hx) subset_union_left,
    dpow_eq_of_support_subset (s := s) b n hx subset_union_right,
    dpow_eq_of_support_subset (s := s) b (m * n) hx subset_union_right, mul_sum]
  simp only [Sym.val_eq_coe, nsmul_eq_mul, Algebra.mul_smul_comm, map_sum, map_smul,
    Finsupp.coe_finset_sum, Finsupp.coe_smul, sum_apply, Pi.smul_apply, smul_eq_mul]

  sorry
