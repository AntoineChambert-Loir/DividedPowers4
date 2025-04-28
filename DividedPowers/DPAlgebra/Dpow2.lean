import Mathlib.Algebra.Order.Antidiag.Pi
import DividedPowers.DPAlgebra.Graded.GradeZero
-- import DividedPowers.DPAlgebra.PolynomialLaw
import DividedPowers.SubDPIdeal
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Data.Finsupp.Weight

/-! # Construction of the divided power struction on the divided power algebra
-/

section

open DividedPowers

variable {R : Type*} [CommSemiring R] {I : Ideal R} (hI : DividedPowers I)

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem DividedPowers.dpow_finsupp_sum
    {ι : Type*} [DecidableEq ι] {x : ι →₀ R} (hx : ∀ i, x i ∈ I) {n : ℕ} :
    hI.dpow n (x.sum fun _ r ↦ r) =
      ∑ k ∈ (x.support.sym n),
        x.prod fun i r ↦ hI.dpow (Multiset.count i k) r := by
  simp only [Finsupp.sum, hI.dpow_sum (fun i _ ↦ hx i), Finsupp.prod]

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem DividedPowers.dpow_linearCombination
    {A : Type*} [CommSemiring A] [Algebra R A] {I : Ideal A} (hI : DividedPowers I)
    {ι : Type*} [DecidableEq ι] {b : ι → A} {x : ι →₀ R}
    (hx : ∀ i ∈ x.support, b i ∈ I) {n : ℕ} :
    hI.dpow n (x.sum fun i r ↦ r • (b i)) =
      ∑ k  ∈ x.support.sym n,
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

variable [DecidableEq R]

variable (x : M) (n : ℕ)

/-- Lemma 2 of Roby 65 : there is at most one divided power structure on the augmentation ideal
  of `DividedPowerAlgebra R M` such that `∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x`. -/
theorem onDPAlgebra_unique (h h' : DividedPowers (augIdeal R M))
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

omit [DecidableEq R] in
theorem isFree_grade [Module.Free R M] (n : ℕ) :
    Module.Free R (grade R M n) :=
  Module.Free.of_basis (basis_grade R M (Module.Free.chooseBasis R M) n)

/-- The basis of the graded part of `DividedPowerAlgebra R M` associated with a basis of `M`. -/
def basis {ι : Type*} (b : Basis ι R M) :
    Basis (ι →₀ ℕ) R (DividedPowerAlgebra R M) := by
  apply Basis.mk (v := fun d ↦
    d.prod (fun i k ↦ dp R k (b i)))
  sorry
  sorry

omit [DecidableEq R] in
theorem isFree [Module.Free R M] : Module.Free R (DividedPowerAlgebra R M) :=
  Module.Free.of_basis (basis R M (Module.Free.chooseBasis R M))


variable {R M} {ι : Type*} (b : Basis ι R M)

omit [DecidableEq R] in
lemma basis_eq (d : ι →₀ ℕ) :
    basis R M b d = d.prod (fun i k ↦ dp R k (b i)) := by
  simp only [basis, Basis.coe_mk]

omit [DecidableEq R] in
lemma basis_zero_eq_one : basis R M b 0 = 1 := by
  simp [basis_eq]

omit [DecidableEq R] in
lemma basis_single_eq (i : ι) (n : ℕ) :
    basis R M b (Finsupp.single i n) = dp R n (b i) := by
  simp only [basis_eq]
  rw [Finsupp.prod_of_support_subset (s := {i}) _ Finsupp.support_single_subset]
  · simp only [prod_singleton, Finsupp.single_eq_same]
  · simp only [mem_singleton, forall_eq, dp_zero]

lemma basis_mem_augIdeal {d : ι →₀ ℕ} (hd : d ≠ 0) :
    basis R M b d ∈ augIdeal R M := by
  simp only [mem_augIdeal_iff, basis_eq, map_finsupp_prod, algebraMapInv_dp]
  simp only [Finsupp.prod]
  simp only [← Finsupp.support_nonempty_iff] at hd
  obtain ⟨i, hi⟩ := hd
  apply Finset.prod_eq_zero hi
  rw [Finsupp.mem_support_iff] at hi
  rw [if_neg hi]

lemma basis_mem_augIdeal_iff [Nontrivial R] (d : ι →₀ ℕ) :
    basis R M b d ∈ augIdeal R M ↔ d ≠ 0 := by
  refine ⟨?_, basis_mem_augIdeal b⟩
  rw [imp_not_comm]
  rintro ⟨rfl⟩
  rw [basis_zero_eq_one, mem_augIdeal_iff, map_one]
  exact one_ne_zero

omit [DecidableEq R] in
lemma eq_of_basis (x : DividedPowerAlgebra R M)  :
    x = ((basis R M b).repr x).sum fun i c ↦ c • (basis R M b) i := by
   conv_lhs => rw [← Basis.linearCombination_repr (basis R M b) x]
   simp [Finsupp.linearCombination, Finsupp.lsum]

lemma mem_augIdeal_iff_of_repr {x : DividedPowerAlgebra R M} :
    x ∈ augIdeal R M ↔ (basis R M b).repr x 0 = 0 := by
  classical
  have H : x = (((basis R M b).repr x).update 0 0).sum (fun i c ↦ c • (basis R M b) i)
    + (fun i c ↦ c • (basis R M b) i) 0 ((basis R M b).repr x 0) := by
    rw [Finsupp.sum_update_add, zero_smul, add_zero]
    · exact eq_of_basis b x
    · exact fun _ ↦ zero_smul R _
    · exact fun _ _ _ ↦ add_smul _ _ _
  have hx' : (((basis R M b).repr x).update 0 0).sum (fun i c ↦ c • (basis R M b) i) ∈ augIdeal R M := by
    apply Ideal.sum_mem
    intro c hc
    simp only [Finsupp.support_update_zero, mem_erase, ne_eq, Finsupp.mem_support_iff] at hc
    apply Submodule.smul_of_tower_mem (augIdeal R M)
    apply basis_mem_augIdeal b hc.1
  nth_rewrite 1 [H]
  rw [Submodule.add_mem_iff_right _ hx']
  simp only [basis_zero_eq_one, Finsupp.mem_support_iff, ne_eq, gt_iff_lt,
    mem_augIdeal_iff, map_smul, map_one]
  simp only [smul_eq_mul, mul_one]

/- When `M` is free with basis `b` (it would suffice that `b` generates `M`,
then any `x : DividedPowerAlgebra R M` can be written as
 `x = (B.repr x).sum  fun d c ↦ c • B d)` :
 `x = ∑ d ∈ (B.repr x).support, B.repr x d • B d`
If `x ∈ augIdeal R M`, then `B.repr x 0 = 0`, and all terms in this
representation belong to `augIdeal R M`.
By the multinomial formula for divided powers, one has
  `dpow n x
    = ∑ d ∈ (B.repr x).support.sym n,
      ∏ i ∈ (B.repr x).support, dpow (d.count i) ((B.repr x i) • B i)
    = ∑ d ∈ (B.repr x).support.sym n,
      ∏ i ∈ (B.repr x).support,
        (B.repr x i) ^ (d.count i) • dpow (d.count i d) (B i) `
Now, `B i = i.prod (fun j k ↦ dp R k (b j)) = ∏ j ∈ i.support, dp R (i j) (b j)`.
Here, `i ≠ 0`, because `i ∈ (B.repr x).support`.
Consequently, there exists `j` such that `j ∈ i.support`.
dpow m (∏ j ∈ i.support, dp R (i j) (b j))
 = dpow m (dp R (i j) (b j) * ∏ k ≠ j, dp R (i j) (b j))
 = m.uniformBell (i j) * dp (m + i j) (b j) *
    ∏ k ≠ j, (dp R (i j) (b j))) ^ m
 =  `

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

omit [DecidableEq R] in
theorem _root_.DividedPowers.dpow_prod {I : Ideal R} (hI : DividedPowers I)
  {ι : Type*} [DecidableEq ι] {r : ι → R} {s : Finset ι}
  (hs : s.Nonempty) (hs' : ∀ i ∈ s, r i ∈ I) {n : ℕ} :
    hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) •
      (∏ i ∈ s, hI.dpow n (r i)) := by
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
 n! ^ (#d.support - 1) * ∏ i ∈ d.support n.uniformBall (d i) ?
-/
theorem dpow_basis_eq (H : DividedPowers (augIdeal R M))
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

omit [DecidableEq R] in
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

/- The coefficient in the formula below might be incorrect. -/
theorem basis_prod (α : Type*) (f : α → (ι →₀ ℕ)) (s : Finset α) :
    ∏ a ∈ s, basis R M b (f a) =
      ((∑ a ∈ s, f a).prod fun i r ↦ Nat.multinomial s (fun a ↦ f a i)) •
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
      sorry


    · rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi

      sorry



/- (m + n + k).choose (m + n) * (m + n).choose n
  = (m + n + k)! / (m + n)! k! * (m + n)!/n! m!
  = (m + n + k)! / m! n! k!
  = multinomial (m
-/

theorem dpow_eq (H : DividedPowers (augIdeal R M))
    (hH : ∀ (n : ℕ) (x : M), H.dpow n (DividedPowerAlgebra.ι R M x) = dp R n x)
    {ι : Type*} [DecidableEq ι] (b : Basis ι R M) (n : ℕ) (x : DividedPowerAlgebra R M)
    (hx : x ∈ augIdeal R M) :
    H.dpow n x = ∑ k ∈ ((basis R M b).repr x).support.sym n,
      (∏ d ∈ ((basis R M b).repr x).support,
        ((basis R M b).repr x d) ^ (Multiset.count d k)) •
      (∏ d ∈ ((basis R M b).repr x).support,
        (((Multiset.count d k) ! ^ (#d.support - 1) • ∏ i ∈ d.support, (Multiset.count d k).uniformBell (d i)))) •
      (∏ d ∈ ((basis R M b).repr x).support,
        basis R M b ((Multiset.count d k) • d)) := by
  nth_rewrite 1 [eq_of_basis b x]
  classical
  rw [H.dpow_linearCombination]
  · simp only [← Finset.prod_smul']
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finsupp.prod] -- , Finset.prod_smul']
    apply Finset.prod_congr rfl
    intro d hd
    rw [dpow_basis_eq H hH]
    simp only [mem_augIdeal_iff_of_repr b] at hx
    rintro ⟨rfl⟩
    simp only [Finsupp.mem_support_iff, ne_eq] at hd
    exact hd hx
  · intro d hd
    apply basis_mem_augIdeal
    rw [mem_augIdeal_iff_of_repr b] at hx
    rintro ⟨rfl⟩
    rw [Finsupp.mem_support_iff] at hd
    exact hd hx

open scoped Classical in
def dpow {ι : Type*} (b : Basis ι R M) (n : ℕ) (x : DividedPowerAlgebra R M) :
    DividedPowerAlgebra R M :=
  if x ∈ augIdeal R M then
    ∑ k ∈ ((basis R M b).repr x).support.sym n,
      (∏ d ∈ ((basis R M b).repr x).support, ((basis R M b).repr x d) ^ (Multiset.count d k)) •
      ∏ d ∈ ((basis R M b).repr x).support,
      ((Multiset.count d k) ! ^ (#d.support - 1) • ∏ i ∈ d.support, (Multiset.count d k).uniformBell (d i)) •
        basis R M b ((Multiset.count d k) • d)
  else 0

open scoped Classical in
theorem dpow_eq_of_support_subset {ι : Type*} (b : Basis ι R M) (n : ℕ)
    {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M)
    {s : Finset (ι →₀ ℕ)} (hs : ((basis R M b).repr x).support ⊆ s) :
    dpow b n x = ∑ k ∈ s.sym n,
      (∏ d ∈ s, ((basis R M b).repr x d) ^ (Multiset.count d k)) •
      ∏ d ∈ s, ((Multiset.count d k) ! ^ (#d.support - 1) • ∏ i ∈ d.support, (Multiset.count d k).uniformBell (d i)) •
      ∏ d ∈ s, basis R M b ((Multiset.count d k) • d) := by
  simp only [dpow, if_pos hx]
  have Hs : ((basis R M b).repr x).support.sym n ⊆ s.sym n := fun k hk ↦ by
    simp only [mem_sym_iff] at hk ⊢
    exact fun a ha ↦ hs (hk a ha)
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
    simp only [← Finset.prod_smul']
    apply Finset.prod_subset_one_on_sdiff hs
    · intro d hd
      suffices Multiset.count d ↑k = 0 by
        simp [this, basis_zero_eq_one, Nat.uniformBell_zero_left]
      rw [mem_sym_iff] at hk
      simp only [mem_sdiff] at hd
      rw [Multiset.count_eq_zero]
      exact fun hd' ↦ hd.right (hk d hd')
    · intros; rfl

theorem dpow_null {n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∉ augIdeal R M) :
    dpow b n x = 0 := by
  simp only [dpow, if_neg hx]

theorem dpow_zero {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 0 x = 1 := by
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp [dpow, if_pos hx, sym_zero, this, Nat.uniformBell_zero_left, basis_eq]

theorem dpow_one {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 1 x = x := by
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp only [dpow, if_pos hx]
  conv_rhs => rw [eq_of_basis b x]
  simp [Sym.coe_cons, Multiset.count_cons, this, Multiset.count_singleton]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finsupp.mem_support_iff] at hd
  simp only [if_neg hd]
  apply congr_arg₂ _ rfl
  rw [Finset.prod_eq_single d]
  · simp only [↓reduceIte, Nat.factorial_one, Nat.cast_one, one_pow, one_mul]
    convert one_mul _
    apply Finset.prod_eq_one
    intro i hi
    simp [Nat.uniformBell_one_left]
  · intro k hk hkd
    simp [if_neg hkd, Nat.uniformBell_zero_left, basis_zero_eq_one]
  · simp only [← Finsupp.mem_support_iff] at hd
    intro hd'
    exfalso; exact hd' hd

theorem dpow_mem {n : ℕ} {x : DividedPowerAlgebra R M}
    (hn : n ≠ 0) (hx : x ∈ augIdeal R M) :
    dpow b n x ∈ augIdeal R M := by
  classical
  simp only [dpow, if_pos hx]
  apply Ideal.sum_mem
  intro k hk
  apply Submodule.smul_of_tower_mem
  have : ∃ d ∈ ((basis R M b).repr x).support, Multiset.count d ↑k ≠ 0 := by
    simp only [mem_sym_iff, Finsupp.mem_support_iff, ne_eq] at hk
    by_contra! hd
    suffices (k : Multiset (ι →₀ ℕ)) = 0 by
      apply hn
      rw [← k.prop]
      convert Multiset.card_zero
    ext d
    simp only [Multiset.not_mem_zero, not_false_eq_true, Multiset.count_eq_zero_of_not_mem,
      Multiset.count_eq_zero, Sym.mem_coe]
    intro hd'
    apply hk d hd'
    by_contra! hd''
    rw [← Finsupp.mem_support_iff] at hd''
    have := hd d hd''
    simp only [Multiset.count_eq_zero, Sym.mem_coe] at this
    exact this hd'
  obtain ⟨d, hd, hd'⟩ := this
  rw [Finset.prod_eq_prod_diff_singleton_mul hd]
  apply Ideal.mul_mem_left
  apply Submodule.smul_of_tower_mem
  apply basis_mem_augIdeal
  simp only [ne_eq, smul_eq_zero, hd', false_or]
  rw [mem_augIdeal_iff_of_repr b] at hx
  rintro ⟨rfl⟩
  simp only [Finsupp.mem_support_iff] at hd
  exact hd hx

def dpowExp (x : DividedPowerAlgebra R M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dpow b n x)

open scoped PowerSeries.WithPiTopology

open scoped Classical in
theorem dpowExp_eq_of_support_subset
    {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M)
    {s : Finset (ι →₀ ℕ)} (hs : ((basis R M b).repr x).support ⊆ s) :
    dpowExp b x = 0 := by
  letI : UniformSpace (DividedPowerAlgebra R M) := ⊥
  haveI : DiscreteTopology (DividedPowerAlgebra R M) := by
    exact forall_open_iff_discrete.mp fun s ↦ trivial
  rw [PowerSeries.as_tsum (dpowExp b x)]
  simp only [dpowExp, PowerSeries.coeff_mk,
    dpow_eq_of_support_subset b _ hx hs]
  simp only [← Finset.prod_smul']
  simp only [map_sum]
  sorry

theorem dpow_add {n : ℕ} {x y : DividedPowerAlgebra R M}
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
  simp only [← Finset.prod_smul']
  rw [Finset.sum_congr rfl (fun k hk ↦ congr_arg₂ HMul.hMul
    (dpow_eq_of_support_subset (s := s) b k.1 hx subset_union_left)
    (dpow_eq_of_support_subset (s := s) b k.2 hy subset_union_right))]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_product']
  simp only [Finset.sum_sigma']
  sorry

example (α : Type*) [DecidableEq α] (n : ℕ) (s : Finset α) :
    (antidiagonal n).sigma (fun k ↦ s.sym k.2 ×ˢ s.sym k.1) ≃ s.sym n := sorry
  ∑ x_1 ∈ (antidiagonal n).sigma fun a ↦ s.sym a.2 ×ˢ s.sym a.1,

example (a b c d : ℕ) (h : a = c) (k : b = d) : a + b = c + d := by
  apply congr_arg₂ _ h k

theorem dpow_mul {n : ℕ} {a x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b n (a * x) = a ^ n * dpow b n x :=
  sorry

theorem mul_dpow {m n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b m x * dpow b n x = ↑((m + n).choose m) * dpow b (m + n) x :=
  sorry

theorem dpow_comp {m n : ℕ} {x : DividedPowerAlgebra R M} (hn : n ≠ 0)
    (hx : x ∈ augIdeal R M) :
    dpow b m (dpow b n x) = ↑(m.uniformBell n) * dpow b (m * n) x :=
  sorry

