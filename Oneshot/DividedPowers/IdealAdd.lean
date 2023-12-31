import Oneshot.DividedPowers.RatAlgebra
import Oneshot.BasicLemmas

open Finset

namespace DividedPowers

variable {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)

namespace IdealAdd

/-- Some complicated numerical coefficients for the proof of ideal_add.dpow_comp -/
private def cnik := fun (n i : ℕ) (k : Multiset ℕ) =>
  ite (i = 0) (mchoose (Multiset.count i k) n)
    (ite (i = n) (mchoose (Multiset.count i k) n)
      ((Multiset.count i k).factorial * mchoose (Multiset.count i k) i *
        mchoose (Multiset.count i k) (n - i)))

/-- Divided power function on a sup of two ideals -/
noncomputable def dpow {J : Ideal A} (hJ : DividedPowers J) : ℕ → A → A := fun n =>
  Function.extend (fun ⟨a, b⟩ => (a : A) + (b : A) : I × J → A)
    (fun ⟨a, b⟩ =>
      Finset.sum (Finset.range (n + 1)) fun k => hI.dpow k (a : A) * hJ.dpow (n - k) (b : A))
    fun a : A => 0
#align divided_powers.ideal_add.dpow DividedPowers.IdealAdd.dpow

/-- Independence on choices for `dpow` -/
theorem dpow_eq_aux {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ) {a} (ha : a ∈ I ⊓ J), hI.dpow n a = hJ.dpow n a) (n : ℕ) {a} (ha : a ∈ I) {b}
    (hb : b ∈ J) {a'} (ha' : a' ∈ I) {b'} (hb' : b' ∈ J) (H : a + b = a' + b') :
    (Finset.sum (Finset.range (n + 1)) fun k => hI.dpow k a * hJ.dpow (n - k) b) =
      Finset.sum (Finset.range (n + 1)) fun k => hI.dpow k a' * hJ.dpow (n - k) b' :=
  by
  let c := a - a'
  suffices haa' : a = a' + c
  suffices hbb' : b' = b + c
  have hcI : c ∈ I := sub_mem ha ha'
  suffices hcJ : c ∈ J
  rw [haa', hbb']
  have Ha'c :
    ((Finset.range (n + 1)).Sum fun k : ℕ => hI.dpow k (a' + c) * hJ.dpow (n - k) b) =
      (Finset.range (n + 1)).Sum fun k : ℕ =>
        (Finset.range (k + 1)).Sum fun l : ℕ =>
          hI.dpow l a' * hJ.dpow (n - k) b * hI.dpow (k - l) c :=
    by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hI.dpow_add k ha' hcI]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [Ha'c]
  rw [Finset.sum_sigma']
  have Hbc :
    ((Finset.range (n + 1)).Sum fun k : ℕ => hI.dpow k a' * hJ.dpow (n - k) (b + c)) =
      (Finset.range (n + 1)).Sum fun k : ℕ =>
        (Finset.range (n - k + 1)).Sum fun l : ℕ =>
          hI.dpow k a' * hJ.dpow l b * hJ.dpow (n - k - l) c :=
    by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hJ.dpow_add (n - k) hb hcJ]
    rw [Finset.mul_sum]; ring_nf
  rw [Hbc]
  rw [Finset.sum_sigma']
  let s := (Finset.range (n + 1)).Sigma fun a : ℕ => Finset.range (a + 1)
  let i : ∀ x : Σ i : ℕ, ℕ, x ∈ s → Σ i : ℕ, ℕ := fun ⟨k, m⟩ h => ⟨m, n - k⟩
  let t := (Finset.range (n + 1)).Sigma fun a : ℕ => Finset.range (n - a + 1)
  let j : ∀ y : Σ i : ℕ, ℕ, y ∈ t → Σ i : ℕ, ℕ := fun ⟨k, m⟩ h => ⟨n - m, k⟩
  rw [Finset.sum_bij' i _ _ j _ _]
  · rintro ⟨k, m⟩ h
    change i ⟨n - m, k⟩ _ = _
    change (⟨k, n - (n - m)⟩ : Σ i : ℕ, ℕ) = _
    simp only [eq_self_iff_true, heq_iff_eq, true_and_iff]
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    apply Nat.sub_sub_self; apply le_trans h.2; apply Nat.sub_le
  · rintro ⟨k, m⟩ h
    change (⟨m, n - k⟩ : Σ i : ℕ, ℕ) ∈ t
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h ⊢
    apply And.intro (le_trans h.2 h.1)
    apply tsub_le_tsub_left h.2
  · rintro ⟨u, v⟩ h
    -- split all factors
    apply congr_arg₂
    apply congr_arg₂
    -- a' : no problemo
    rfl
    -- b : more difficult
    apply congr_arg₂;
    rfl; rfl
    -- c :
    rw [hIJ _ ⟨hcI, hcJ⟩]
    apply congr_arg₂
    change u - v = n - v - (n - u)
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    rw [tsub_tsub_tsub_cancel_left h.1]
    rfl
  · rintro ⟨k, m⟩ h
    change (⟨n - m, k⟩ : Σ i : ℕ, ℕ) ∈ s
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h ⊢
    apply And.intro (Nat.sub_le _ _)
    rw [Nat.le_sub_iff_right (le_trans h.2 (Nat.sub_le n k))]
    rw [add_comm]
    rw [← Nat.le_sub_iff_right h.1]
    exact h.2
  · rintro ⟨k, m⟩ h
    change j ⟨m, n - k⟩ _ = _
    change (⟨n - (n - k), m⟩ : Σ i : ℕ, ℕ) = _
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    simp only [heq_iff_eq, eq_self_iff_true, and_true_iff]
    exact Nat.sub_sub_self h.1
  · rw [← sub_eq_iff_eq_add'.mpr hbb']; exact sub_mem hb' hb
  · rw [← sub_eq_iff_eq_add'] at H ; rw [← H]; rw [haa']; ring
  · simp only [c]; ring
#align divided_powers.ideal_add.dpow_eq_aux DividedPowers.IdealAdd.dpow_eq_aux

theorem dpow_eq {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n) {a} (ha : a ∈ I) {b}
    (hb : b ∈ J) :
    dpow hI hJ n (a + b) =
      Finset.sum (Finset.range (n + 1)) fun k => hI.dpow k a * hJ.dpow (n - k) b :=
  by
  simp only [dpow]
  convert Function.extend_apply_first _ _ _ _ (⟨(⟨a, ha⟩ : I), (⟨b, hb⟩ : J)⟩ : I × J)
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
  intro H
  refine' dpow_eq_aux hI hJ _ n ha hb ha' hb' H
  · intro n a; exact hIJ n a
#align divided_powers.ideal_add.dpow_eq DividedPowers.IdealAdd.dpow_eq

theorem dpow_eq_of_mem_left {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) {x : A} (hx : x ∈ I) :
    dpow hI hJ n x = hI.dpow n x := by
  rw [← add_zero x]
  rw [dpow_eq]
  · rw [Finset.sum_eq_single n]
    · simp only [Nat.sub_self, add_zero, hJ.dpow_zero]
      rw [hJ.dpow_zero J.zero_mem, mul_one]
    · intro b hb hb'
      rw [hJ.dpow_eval_zero, MulZeroClass.mul_zero]
      intro h; apply hb'
      rw [Finset.mem_range, Nat.lt_succ_iff] at hb 
      rw [← Nat.sub_add_cancel hb, h, zero_add]
    · intro hn; exfalso; apply hn; rw [Finset.mem_range]
      exact lt_add_one n
  exact hIJ; exact hx; exact J.zero_mem
#align divided_powers.ideal_add.dpow_eq_of_mem_left DividedPowers.IdealAdd.dpow_eq_of_mem_left

theorem dpow_eq_of_mem_right {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) {x : A} (hx : x ∈ J) :
    dpow hI hJ n x = hJ.dpow n x := by
  rw [← zero_add x]
  rw [dpow_eq]
  · rw [Finset.sum_eq_single 0]
    · simp only [Nat.sub_zero, zero_add, hI.dpow_zero I.zero_mem, one_mul]
    · intro b hb hb'
      rw [hI.dpow_eval_zero, MulZeroClass.zero_mul]; exact hb'
    · intro hn; exfalso; apply hn; rw [Finset.mem_range]
      exact NeZero.pos (n + 1)
  exact hIJ; exact I.zero_mem; exact hx
#align divided_powers.ideal_add.dpow_eq_of_mem_right DividedPowers.IdealAdd.dpow_eq_of_mem_right

theorem dpow_zero {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    ∀ (x : A) (hx : x ∈ I + J), dpow hI hJ 0 x = 1 :=
  by
  intro x
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [dpow_eq hI hJ hIJ (0 : ℕ) ha hb]
  simp only [Finset.range_one, zero_tsub, Finset.sum_singleton]
  rw [hI.dpow_zero ha, hJ.dpow_zero hb, mul_one]
#align divided_powers.ideal_add.dpow_zero DividedPowers.IdealAdd.dpow_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem dpow_mul {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ) (a : A), a ∈ I ⊓ J → hI.dpow n a = hJ.dpow n a) (m n : ℕ) {x : A} :
    x ∈ I + J → dpow hI hJ m x * dpow hI hJ n x = ↑((m + n).choose m) * dpow hI hJ (m + n) x :=
  by
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [dpow_eq hI hJ hIJ m ha hb]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => hI.dpow i a * hJ.dpow j b]
  rw [dpow_eq hI hJ hIJ n ha hb]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l => hI.dpow k a * hJ.dpow l b]
  rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  have hf :
    ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      hI.dpow x.fst.fst a * hJ.dpow x.fst.snd b * (hI.dpow x.snd.fst a * hJ.dpow x.snd.snd b) =
        (x.fst.fst + x.snd.fst).choose x.fst.fst * (x.fst.snd + x.snd.snd).choose x.fst.snd *
            hI.dpow (x.fst.fst + x.snd.fst) a *
          hJ.dpow (x.fst.snd + x.snd.snd) b :=
    by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    dsimp
    rw [mul_assoc]; rw [← mul_assoc (hJ.dpow j b) _ _]; rw [mul_comm (hJ.dpow j b)]
    rw [mul_assoc]; rw [hJ.dpow_mul j l hb]
    rw [← mul_assoc]; rw [hI.dpow_mul i k ha]
    ring
  rw [Finset.sum_congr rfl fun x hx => hf x]
  let s : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := fun x => ⟨x.fst.fst + x.snd.fst, x.fst.snd + x.snd.snd⟩
  have hs :
    ∀ x ∈ Finset.Nat.antidiagonal m ×ˢ Finset.Nat.antidiagonal n,
      s x ∈ Finset.Nat.antidiagonal (m + n) :=
    by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ h; dsimp [s]
    simp only [Finset.Nat.mem_antidiagonal, Finset.mem_product] at h ⊢
    rw [add_assoc, ← add_assoc k j l, add_comm k _, add_assoc, h.2, ← add_assoc, h.1]
  rw [← Finset.sum_fiberwise_of_maps_to hs]
  have hs' :
    ((Finset.Nat.antidiagonal (m + n)).Sum fun y : ℕ × ℕ =>
        (Finset.filter (fun x : (ℕ × ℕ) × ℕ × ℕ => (fun x : (ℕ × ℕ) × ℕ × ℕ => s x) x = y)
              (Finset.Nat.antidiagonal m ×ˢ Finset.Nat.antidiagonal n)).Sum
          fun x : (ℕ × ℕ) × ℕ × ℕ =>
          ↑((x.fst.fst + x.snd.fst).choose x.fst.fst) *
                ↑((x.fst.snd + x.snd.snd).choose x.fst.snd) *
              hI.dpow (x.fst.fst + x.snd.fst) a *
            hJ.dpow (x.fst.snd + x.snd.snd) b) =
      (Finset.Nat.antidiagonal (m + n)).Sum fun y : ℕ × ℕ =>
        ((Finset.filter (fun x : (ℕ × ℕ) × ℕ × ℕ => (fun x : (ℕ × ℕ) × ℕ × ℕ => s x) x = y)
                  (Finset.Nat.antidiagonal m ×ˢ Finset.Nat.antidiagonal n)).Sum
              fun x : (ℕ × ℕ) × ℕ × ℕ => ↑(y.fst.choose x.fst.fst) * ↑(y.snd.choose x.fst.snd)) *
            hI.dpow y.fst a *
          hJ.dpow y.snd b :=
    by
    apply Finset.sum_congr rfl; rintro ⟨u, v⟩ hy
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hx
    simp [s] at hx 
    dsimp
    rw [hx.2.1]; rw [hx.2.2]
  rw [hs']
  rw [dpow_eq hI hJ hIJ (m + n) ha hb]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => hI.dpow i a * hJ.dpow j b]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; rintro ⟨u, v⟩ h
  -- simp only [nat.cast_sum, nat.cast_mul],
  -- rw finset.sum_mul, simp_rw finset.mul_sum,
  simp only [Prod.mk.inj_iff]
  rw [← mul_assoc]
  apply congr_arg₂ _ _ rfl
  apply congr_arg₂ _ _ rfl
  simp only [← Nat.cast_sum, ← Nat.cast_mul]
  apply congr_arg
  simp only [Finset.Nat.mem_antidiagonal] at h 
  rw [rewriting_4_fold_sums h.symm (fun x => u.choose x.fst * v.choose x.snd) rfl _]
  · rw [← Nat.add_choose_eq]; rw [h]
  · intro x h
    cases' h with h h <;>
      · simp only [Nat.choose_eq_zero_of_lt h, MulZeroClass.zero_mul, MulZeroClass.mul_zero]
#align divided_powers.ideal_add.dpow_mul DividedPowers.IdealAdd.dpow_mul

theorem dpow_mem {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    ∀ {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I + J), dpow hI hJ n x ∈ I + J :=
  by
  intro n hn x
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [dpow_eq hI hJ hIJ _ ha hb]
  apply Submodule.sum_mem (I ⊔ J)
  intro k hk
  by_cases hk0 : k = 0
  · rw [hk0]
    --rw tsub_zero,
    apply Submodule.mem_sup_right;
    apply Ideal.mul_mem_left
    exact hJ.dpow_mem hn hb
  · apply Submodule.mem_sup_left; apply Ideal.mul_mem_right
    exact hI.dpow_mem hk0 ha
#align divided_powers.ideal_add.dpow_mem DividedPowers.IdealAdd.dpow_mem

theorem dpow_smul {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    ∀ (n : ℕ) {c x : A} (hx : x ∈ I + J), dpow hI hJ n (c * x) = c ^ n * dpow hI hJ n x :=
  by
  intro n c x
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [dpow_eq hI hJ hIJ n ha hb]
  rw [mul_add]
  rw [dpow_eq hI hJ hIJ n (Ideal.mul_mem_left I c ha) (Ideal.mul_mem_left J c hb)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk 
  rw [hI.dpow_smul]; rw [hJ.dpow_smul]
  simp only [← mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  rw [mul_comm, ← mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  rw [← pow_add, Nat.sub_add_cancel hk]
  exact hb
  exact ha
#align divided_powers.ideal_add.dpow_smul DividedPowers.IdealAdd.dpow_smul

theorem dpow_add {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    ∀ (n : ℕ) {x y : A} (hx : x ∈ I + J) (hy : y ∈ I + J),
      dpow hI hJ n (x + y) =
        Finset.sum (Finset.range (n + 1)) fun k => dpow hI hJ k x * dpow hI hJ (n - k) y :=
  by
  intro n x y
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [Submodule.mem_sup]
  rintro ⟨a', ha', b', hb', rfl⟩
  rw [add_add_add_comm a b a' b']
  rw [dpow_eq hI hJ hIJ n (Submodule.add_mem I ha ha') (Submodule.add_mem J hb hb')]
  let f : ℕ × ℕ × ℕ × ℕ → A := fun ⟨i, j, k, l⟩ =>
    hI.dpow i a * hI.dpow j a' * hJ.dpow k b * hJ.dpow l b'
  have hf1 :
    ∀ k ∈ Finset.range (n + 1),
      hI.dpow k (a + a') * hJ.dpow (n - k) (b + b') =
        (Finset.range (k + 1)).Sum fun i =>
          (Finset.range (n - k + 1)).Sum fun l =>
            hI.dpow i a * hI.dpow (k - i) a' * hJ.dpow l b * hJ.dpow (n - k - l) b' :=
    by
    intro k hk
    rw [hI.dpow_add k ha ha']; rw [hJ.dpow_add (n - k) hb hb']
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [Finset.sum_congr rfl hf1]
  have hf2 :
    ∀ k ∈ Finset.range (n + 1),
      dpow hI hJ k (a + b) * dpow hI hJ (n - k) (a' + b') =
        (Finset.range (k + 1)).Sum fun i =>
          (Finset.range (n - k + 1)).Sum fun l =>
            hI.dpow i a * hI.dpow l a' * hJ.dpow (k - i) b * hJ.dpow (n - k - l) b' :=
    by
    intro k hk
    rw [dpow_eq hI hJ hIJ k ha hb]
    rw [dpow_eq hI hJ hIJ (n - k) ha' hb']
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [Finset.sum_congr rfl hf2]
  convert Finset.sum_4_rw f n
#align divided_powers.ideal_add.dpow_add DividedPowers.IdealAdd.dpow_add

/- si on développe, on obtient une somme indexée par
  les c : fin (n+1) → ℕ  de somme m 
  de  ∏   (hI.dpow k a)^(c k) (hJ.dpow (n-k) b)^(c k) 
  sans coefficients multinomiaux !
    par récurrence, en utilisant dpow_mul,
    a^[k] a^[k'] = (k + k')!/k! k'! a^ [k + k']
    a^[k] a^[k'] a^[k''] = (k+k'+k'')!/k!k'!k''!
   ∏ (hI.dpow k a)^(c k) = multinomial (k ^ (c k)) hI.dpow (∑ k (c k)) a
    tandis que Π (hJ.dpow (n-k) b)^(c k)
     = multinomial ((n-k)^ (c k)) hJ.dpow (∑ (n-k) c k) b
    la puissance est n∑ c k - ∑ k (c k) = n m - ∑ k (c k)
    = N!/∏ k!^(c k) * (nm - N)!/∏ (n-k)!^(c k) * a^[N] * b^[nm -N]
    
    Lorsqu'on somme sur les c de somme m et de poids N,
    il faudra trouver (mchoose m n)…
    Il est probable que le plus facile est d'identifier
    ce qui se passe pour Q[a,b] avec sa structure de puissances divisées canonique.


  -/
/-- Prove the `dpow_comp` axiom for the ideal `I ⊔ J`, assuming agreement on `I ⊓ J` , -/
theorem dpow_comp_aux {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (m : ℕ) {n : ℕ} (hn : n ≠ 0) {a : A}
    (ha : a ∈ I) {b : A} (hb : b ∈ J) :
    dpow hI hJ m (dpow hI hJ n (a + b)) =
      Finset.sum (Finset.range (m * n + 1)) fun p : ℕ =>
        ((Finset.filter
                  (fun l : Sym ℕ m =>
                    ((Finset.range (n + 1)).Sum fun i => Multiset.count i ↑l * i) = p)
                  ((Finset.range (n + 1)).Sym m)).Sum
              fun x : Sym ℕ m =>
              (((Finset.range (n + 1)).Prod fun i : ℕ => cnik n i ↑x) *
                  Nat.multinomial (Finset.range (n + 1)) fun i : ℕ => Multiset.count i ↑x * i) *
                Nat.multinomial (Finset.range (n + 1)) fun i : ℕ => Multiset.count i ↑x * (n - i)) *
            hI.dpow p a *
          hJ.dpow (m * n - p) b :=
  by
  rw [dpow_eq hI hJ hIJ n ha hb]
  rw [dpow_sum_aux (dpow hI hJ) (dpow_zero hI hJ hIJ) (dpow_add hI hJ hIJ)]
  /- i ≠0, n : 
     (a^[i]*b^[n-i])^[c i] 
      = a^[i]^ (c i) * (b^[n-i])^[c i]
      = (c i)! a^[i])^[c i] * b^[n-i]^[c i]
      = (c i)! * mchoose (i, c i) * mchoose (n-i, c i) 
      * a^[i * c i] * b^[(n-i) * c i]
    i = 0 : 
      (a^[0] * b^[n])^[c i]
       = b^[n]^[c i] = mchoose (c i) n * b ^[n * c i]
    i = n : 
      (a^[n] * b^[0]) ^[c i]
       = a^[n]^[c i] = mchoose (c i) n * a^[n * c i]
    -/
  have L1 :
    ∀ (k : Sym ℕ m) (i : ℕ) (hi : i ∈ Finset.range (n + 1)),
      dpow hI hJ (Multiset.count i ↑k) (hI.dpow i a * hJ.dpow (n - i) b) =
        cnik n i ↑k * hI.dpow (Multiset.count i ↑k * i) a *
          hJ.dpow (Multiset.count i ↑k * (n - i)) b :=
    by
    intro k i hi
    simp only [cnik]
    by_cases hi2 : i = n
    · rw [hi2]; rw [Nat.sub_self]
      rw [if_neg hn]; rw [if_pos rfl]
      simp only [mchoose_zero', mul_one, Nat.cast_one, MulZeroClass.mul_zero, hJ.dpow_zero hb]
      rw [dpow_eq_of_mem_left hI hJ hIJ _ (hI.dpow_mem hn ha)]
      rw [hI.dpow_comp _ hn ha]
    have hi2' : n - i ≠ 0 := by
      intro h; apply hi2
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi 
      rw [← Nat.sub_add_cancel hi, h, zero_add]
    by_cases hi1 : i = 0
    · rw [hi1]; rw [mchoose_zero']; rw [hI.dpow_zero ha]; rw [Nat.sub_zero]; rw [one_mul]
      rw [if_pos rfl]
      rw [dpow_eq_of_mem_right hI hJ hIJ _ (hJ.dpow_mem hn hb)]
      rw [hJ.dpow_comp _ hn hb]
      rw [MulZeroClass.mul_zero]
      rw [hI.dpow_zero ha]
      simp only [Nat.cast_one, one_mul, mul_one]
    -- i ≠ 0  and i ≠ n
    · rw [if_neg hi1]; rw [if_neg hi2]
      rw [mul_comm, dpow_smul hI hJ hIJ, mul_comm]
      rw [dpow_eq_of_mem_left hI hJ hIJ _ (hI.dpow_mem hi1 ha)]
      rw [← hJ.factorial_mul_dpow_eq_pow (Multiset.count i k)]
      rw [hI.dpow_comp _ hi1 ha]
      rw [hJ.dpow_comp _ hi2' hb]
      simp only [← mul_assoc]; apply congr_arg₂ _ _ rfl
      simp only [mul_assoc]; rw [mul_comm (hI.dpow _ a)]
      simp only [← mul_assoc]
      apply congr_arg₂ _ _ rfl
      rw [mul_comm ↑(mchoose _ i)]
      simp only [Nat.cast_mul]
      exact hJ.dpow_mem hi2' hb
      apply Submodule.mem_sup_left; exact hI.dpow_mem hi1 ha
  let φ : Sym ℕ m → ℕ := fun k => (Finset.range (n + 1)).Sum fun i => Multiset.count i ↑k * i
  suffices hφ : ∀ k : Sym ℕ m, k ∈ (Finset.range (n + 1)).Sym m → φ k ∈ Finset.range (m * n + 1)
  rw [← Finset.sum_fiberwise_of_maps_to hφ _]
  suffices L4 :
    ∀ (p : ℕ) (hp : p ∈ Finset.range (m * n + 1)),
      ((Finset.filter (fun x : Sym ℕ m => (fun k : Sym ℕ m => φ k) x = p)
              ((Finset.range (n + 1)).Sym m)).Sum
          fun x : Sym ℕ m =>
          (Finset.range (n + 1)).Prod fun i : ℕ =>
            dpow hI hJ (Multiset.count i ↑x) (hI.dpow i a * hJ.dpow (n - i) b)) =
        (Finset.filter (fun x : Sym ℕ m => (fun k : Sym ℕ m => φ k) x = p)
              ((Finset.range (n + 1)).Sym m)).Sum
          fun k : Sym ℕ m =>
          ((Finset.range (n + 1)).Prod fun i : ℕ => ↑(cnik n i ↑k)) *
                  ↑(Nat.multinomial (Finset.range (n + 1)) fun i : ℕ => Multiset.count i ↑k * i) *
                ↑(Nat.multinomial (Finset.range (n + 1)) fun i : ℕ =>
                    Multiset.count i ↑k * (n - i)) *
              hI.dpow p a *
            hJ.dpow (m * n - p) b
  rw [Finset.sum_congr rfl L4]
  simp_rw [Finset.sum_mul]
  · -- L4
    intro p hp
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk 
    rw [Finset.prod_congr rfl (L1 k)]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_mul_distrib]
    rw [hI.prod_dpow_self _ ha]
    rw [hJ.prod_dpow_self _ hb]
    simp only [mul_assoc]; apply congr_arg₂ _ rfl
    apply congr_arg₂ _ rfl
    rw [sum_range_sym_mul_compl hk.1]
    simp only [← mul_assoc]
    simp only [← hk.2, φ]; apply congr_arg₂ _ _ rfl
    rw [mul_comm]
  · -- hφ
    intro k hk
    simp only [φ, Finset.mem_range, Nat.lt_succ_iff]
    exact range_sym_weighted_sum_le k hk
  · intro n hn
    rw [dpow_eq_of_mem_left hI hJ hIJ n I.zero_mem]
    exact dpow_eval_zero hI hn
  · intro i hi
    by_cases hi0 : i = 0
    · rw [hi0]
      apply Submodule.mem_sup_right; apply Ideal.mul_mem_left
      exact hJ.dpow_mem hn hb
    · apply Submodule.mem_sup_left; apply Ideal.mul_mem_right
      exact hI.dpow_mem hi0 ha
#align divided_powers.ideal_add.dpow_comp_aux DividedPowers.IdealAdd.dpow_comp_aux

open Polynomial

open scoped Classical

theorem Polynomial.inv_c_eq_c_inv {R : Type _} [CommRing R] (a : R) :
    Ring.inverse (C a) = C (Ring.inverse a) :=
  by
  simp only [Ring.inverse]
  by_cases ha : IsUnit a
  · simp only [dif_pos ha]
    have hCa : IsUnit (C a) := by
      rw [← IsUnit.unit_spec ha]
      exact RingHom.isUnit_map C ha
    rw [dif_pos hCa]
    apply IsUnit.mul_right_cancel hCa
    rw [← map_mul]
    simp only [IsUnit.val_inv_mul, map_one]
  · simp only [Ring.inverse, dif_neg ha, map_zero]
    rw [dif_neg]
    intro hCa; apply ha
    rw [isUnit_iff_exists_inv] at hCa ⊢
    obtain ⟨b, hb⟩ := hCa
    use b.coeff 0
    convert congr_arg₂ coeff hb rfl
    rw [Polynomial.coeff_C_mul]
    simp only [coeff_one_zero]
#align divided_powers.ideal_add.polynomial.inv_C_eq_C_inv DividedPowers.IdealAdd.Polynomial.inv_c_eq_c_inv

theorem dpow_comp_coeffs {m n p : ℕ} (hn : n ≠ 0) (hp : p ≤ m * n) :
    mchoose m n =
      (Finset.filter
            (fun l : Sym ℕ m =>
              ((Finset.range (n + 1)).Sum fun i : ℕ => Multiset.count i ↑l * i) = p)
            ((Finset.range (n + 1)).Sym m)).Sum
        fun x : Sym ℕ m =>
        ((Finset.range (n + 1)).Prod fun i : ℕ => cnik n i ↑x) *
          ((Nat.multinomial (Finset.range (n + 1)) fun i : ℕ => Multiset.count i ↑x * i) *
            Nat.multinomial (Finset.range (n + 1)) fun i : ℕ => Multiset.count i ↑x * (n - i)) :=
  by
  rw [← mul_left_inj' (pos_iff_ne_zero.mp (Nat.choose_pos hp))]
  have : Function.Injective (coe : ℕ → ℚ) := Nat.cast_injective
  apply this
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_prod, Nat.cast_eq_zero]
  conv_lhs => rw [← Polynomial.coeff_X_add_one_pow ℚ (m * n) p]
  let A := Polynomial ℚ
  --   let X : A :=  1 1,
  let I : Ideal A := ⊤
  let hI : DividedPowers I := rat_algebra.divided_powers ⊤
  let hII : ∀ (n : ℕ) (a : A), a ∈ I ⊓ I → hI.dpow n a = hI.dpow n a := fun n a ha => rfl
  let h1 : (1 : A) ∈ I := Submodule.mem_top
  let hX : X ∈ I := Submodule.mem_top
  suffices hdpow : ∀ (k : ℕ) (a : A) (ha : a ∈ I), hI.dpow k a = C (1 / ↑k.factorial) * a ^ k
  rw [← hI.factorial_mul_dpow_eq_pow (m * n) (X + 1) Submodule.mem_top]
  rw [← Polynomial.coeff_C_mul]
  rw [← mul_assoc, mul_comm (C ↑(mchoose m n)), mul_assoc]
  simp only [C_eq_nat_cast]
  rw [← hI.dpow_comp m hn Submodule.mem_top]
  rw [← dpow_eq_of_mem_left hI hI hII n Submodule.mem_top, ←
    dpow_eq_of_mem_left hI hI hII m Submodule.mem_top]
  rw [dpow_comp_aux hI hI hII m hn hX h1]
  rw [← C_eq_nat_cast]
  simp only [Finset.mul_sum]
  -- simp only [← C_eq_nat_cast, ← ring_hom.map_sum, ← ring_hom.map_prod],
  -- simp only [← ring_hom.map_sum, ← ring_hom.map_prod],
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [finset_sum_coeff]
  rw [Finset.sum_eq_single p]
  · simp only [hdpow _ _ Submodule.mem_top, one_pow, mul_one, one_mul]
    simp_rw [Polynomial.coeff_C_mul]
    simp only [← C_eq_nat_cast, ← RingHom.map_prod]
    simp_rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C]
    simp only [coeff_X_pow_self p]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm]
    simp only [mul_assoc]
    apply congr_arg₂ (· * ·) rfl
    apply congr_arg₂ (· * ·) rfl
    apply congr_arg₂ (· * ·) rfl
    rw [← Nat.choose_mul_factorial_mul_factorial hp]
    simp only [one_div, Nat.cast_mul, one_mul]
    rw [mul_comm]; simp only [mul_assoc]; rw [mul_comm ↑(m * n - p).factorial]
    rw [mul_comm]; simp only [mul_assoc]
    convert mul_one _
    rw [← mul_assoc]
    convert mul_one _
    · rw [mul_inv_cancel]
      simp only [Ne.def, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero _
    · rw [mul_inv_cancel]
      simp only [Ne.def, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero _
  · intro k hk hk'
    rw [Finset.sum_eq_zero]
    intro x hx
    simp only [hdpow _ _ Submodule.mem_top, one_pow, mul_one, one_mul]
    simp_rw [Polynomial.coeff_C_mul]
    simp only [← C_eq_nat_cast, ← RingHom.map_prod]
    simp_rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C]
    simp only [Polynomial.coeff_X_pow, if_neg (Ne.symm hk')]
    simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  · intro hp
    convert Finset.sum_empty
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    simp only [Finset.mem_filter] at hx 
    apply hp
    rw [Finset.mem_range, Nat.lt_succ_iff]
    rw [← hx.2]
    exact range_sym_weighted_sum_le x hx.1
  · intro k a ha
    simp only [rat_algebra.divided_powers_dpow_apply, rat_algebra.dpow,
      of_invertible_factorial.dpow, dif_pos ha, one_div]
    simp only [← C_eq_nat_cast]
    rw [polynomial.inv_C_eq_C_inv]
    simp only [Ring.inverse_eq_inv']
#align divided_powers.ideal_add.dpow_comp_coeffs DividedPowers.IdealAdd.dpow_comp_coeffs

theorem dpow_comp {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (m : ℕ) {n : ℕ} (hn : n ≠ 0) {x : A}
    (hx : x ∈ I + J) : dpow hI hJ m (dpow hI hJ n x) = ↑(mchoose m n) * dpow hI hJ (m * n) x :=
  by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx 
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_comp_aux hI hJ hIJ m hn ha hb]
  rw [dpow_add hI hJ hIJ _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [dpow_eq_of_mem_left hI hJ hIJ _ ha]
  rw [dpow_eq_of_mem_right hI hJ hIJ _ hb]
  simp only [mul_assoc]; apply congr_arg₂ (· * ·) _ rfl
  -- it remains to check coefficients
  rw [dpow_comp_coeffs hn (nat.lt_succ_iff.mp (finset.mem_range.mp hp))]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_prod]
#align divided_powers.ideal_add.dpow_comp DividedPowers.IdealAdd.dpow_comp

-- MOVE dpow_null and dpow_one outside of the definition
noncomputable def dividedPowers {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) : DividedPowers (I + J)
    where
  dpow := dpow hI hJ
  dpow_null := by
    intro n x hx
    simp only [dpow]
    rw [Function.extend_apply']
    rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, h⟩; apply hx
    rw [← h]
    --  change a + b ∈ I + J,
    exact Submodule.add_mem_sup ha hb
  dpow_zero := dpow_zero hI hJ hIJ
  dpow_one := by
    intro x
    rw [Ideal.add_eq_sup, Submodule.mem_sup]
    rintro ⟨a, ha, b, hb, rfl⟩
    rw [dpow_eq hI hJ hIJ _ ha hb]
    suffices : Finset.range (1 + 1) = {0, 1}; rw [this]
    simp only [Finset.sum_insert, Finset.mem_singleton, Nat.zero_ne_one, not_false_iff, tsub_zero,
      Finset.sum_singleton, tsub_self]
    rw [hI.dpow_zero ha, hI.dpow_one ha, hJ.dpow_zero hb, hJ.dpow_one hb]
    ring
    · rw [Finset.range_succ, Finset.range_one]; ext k; simp; exact or_comm
  dpow_mem n := dpow_mem hI hJ hIJ
  dpow_add := dpow_add hI hJ hIJ
  dpow_smul := dpow_smul hI hJ hIJ
  dpow_mul := dpow_mul hI hJ hIJ
  dpow_comp := dpow_comp hI hJ hIJ
#align divided_powers.ideal_add.divided_powers DividedPowers.IdealAdd.dividedPowers

theorem dpow_unique {J : Ideal A} (hJ : DividedPowers J) (hsup : DividedPowers (I + J))
    (hI' : ∀ (n : ℕ), ∀ a ∈ I, hI.dpow n a = hsup.dpow n a)
    (hJ' : ∀ (n : ℕ), ∀ b ∈ J, hJ.dpow n b = hsup.dpow n b) :
    let hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a := fun n a ha => by
      simp only [hI' n a (submodule.mem_inf.mp ha).1, hJ' n a (submodule.mem_inf.mp ha).2]
    hsup = dividedPowers hI hJ hIJ :=
  by
  intro hIJ
  apply eq_of_eq_on_ideal
  intro n x hx
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx 
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp only [DividedPowers, dpow_eq hI hJ hIJ n ha hb]
  rw [hsup.dpow_add n (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb)]
  apply Finset.sum_congr rfl
  intro k hk
  apply congr_arg₂ (· * ·) (hI' _ a ha).symm (hJ' _ b hb).symm
#align divided_powers.ideal_add.dpow_unique DividedPowers.IdealAdd.dpow_unique

end IdealAdd

end DividedPowers

