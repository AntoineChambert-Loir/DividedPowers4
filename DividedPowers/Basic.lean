/- ACL and MIdFF, Lean 2022 meeting at Icerm
! This file was ported from Lean 3 source module divided_powers.basic
-/
import DividedPowers.ForMathlib.Bell
import Mathlib.RingTheory.PowerSeries.Basic


/-! # Divided powers

Let `A` be a commutative (semi)ring and `I` be an ideal of `A`.
A *divided power structure* on `I` is the datum of operations `dpow : ℕ → I → A` satisfying
relations that model the intuitive formula `dpow n a = a ^ n / n.factorial` and
collected by the structure `DividedPowers`.
To avoid coercions, we rather consider `dpow : ℕ → A → A`, extended by 0.

## References

* P. Berthelot (1974), *Cohomologie cristalline des schémas de caractéristique $p$ > 0*,
Lectures notes in mathematics 407, Springer-Verlag.

* P. Berthelot and A. Ogus (1978), *Notes on crystalline cohomology*,
Princeton University Press.

* N. Roby (1963). « Lois polynomes et lois formelles en théorie des modules ».
Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348.
https://doi.org/10.24033/asens.1124.

* N. Roby (1968), *Construction de certaines algèbres à puissances divisées*,
Bulletin de la Société Mathématique de France, Tome 96, p. 97-113.
doi: https://doi.org/10.24033/bsmf.1661

* N. Roby (1966), *Sur l'algèbre des puissances divisées d'un module et le module de ses
différentielles*, Annales scientifiques de l'École Normale Supérieure, Série 3, Tome 83,no. 2,
p. 75-89.
doi: https://doi.org/10.24033/asens.1148

-/

section DividedPowersDefinition

open Finset Nat

/-- A divided power structure on an ideal `I` of a commutative (semi)ring `A` is a collection of
operations `dpow : ℕ → I → A` satisfying relations that model the intuitive formula
`dpow n a = a ^ n / n.factorial` -/
@[ext]
structure DividedPowers {A : Type*} [CommSemiring A] (I : Ideal A) where
  /-- The underlying family of maps. -/
  dpow : ℕ → A → A
  dpow_null : ∀ {n x} (_ : x ∉ I), dpow n x = 0
  dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1
  dpow_one : ∀ {x} (_ : x ∈ I), dpow 1 x = x
  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ I), dpow n x ∈ I
  dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
    dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y
  dpow_smul : ∀ (n) {a : A} {x} (_ : x ∈ I), dpow n (a * x) = a ^ n * dpow n x
  dpow_mul : ∀ (m n) {x} (_ : x ∈ I), dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
  dpow_comp : ∀ (m) {n x} (_ : n ≠ 0) (_ : x ∈ I),
    dpow m (dpow n x) = uniformBell m n * dpow (m * n) x

/-- The divided power structure on the ideal `0`.-/
def dividedPowersBot (A : Type*) [CommSemiring A] [DecidableEq A] : DividedPowers (⊥ : Ideal A)
    where
  dpow n a := ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    dsimp only
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero {a} ha := by simp only [Ideal.mem_bot.mp ha, and_self, ↓reduceIte]
  dpow_one {a} ha := by simp only [Ideal.mem_bot.mp ha, one_ne_zero, and_false, ↓reduceIte]
  dpow_mem {n a} hn _ := by
    simp only [Ideal.mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a => False.elim (hn a)
  dpow_add n a b ha hb := by
    rw [Ideal.mem_bot.mp ha, Ideal.mem_bot.mp hb, add_zero]
    simp only [true_and, ge_iff_le, tsub_eq_zero_iff_le, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · apply symm
      refine sum_eq_zero (fun i hi ↦ ?_)
      split_ifs with h2 h1
      · rw [mem_antidiagonal, h1, h2, add_zero] at hi
        exact absurd hi.symm h
      · rfl
      · rfl
  dpow_smul n {a x} hx := by
    simp only [Ideal.mem_bot.mp hx, mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  dpow_mul m n {x} hx := by
    simp only [Ideal.mem_bot.mp hx, true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg (not_and_of_not_right (m = 0) hn)]
  dpow_comp m {n a} hn ha := by
    simp only [Ideal.mem_bot.mp ha, true_and, ite_eq_else, mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm: m = 0
    · simp only [hm, and_true, true_or, ite_true, uniformBell_zero, cast_one,
        if_pos (fun h => False.elim (hn h))]
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]

instance {A : Type*} [CommSemiring A] [DecidableEq A] : Inhabited (DividedPowers (⊥ : Ideal A)) :=
  ⟨dividedPowersBot A⟩

instance {A : Type*} [CommSemiring A] (I : Ideal A) :
    CoeFun (DividedPowers I) fun _ => ℕ → A → A := ⟨fun hI => hI.dpow⟩

/-- The data of a triple `(A, I, γ)` consisting of a commutative (semi)ring `A`, an `A`-ideal `I`,
  and a divided power structure `γ` on `I`. -/
structure DPRing (A : Type*) extends CommSemiring A where
  /-- The ideal `I`.-/
  dpIdeal : Ideal A
  /-- The divided power structure `γ`. -/
  dividedPowers : DividedPowers dpIdeal

instance {A : Type*} [CommSemiring A] [DecidableEq A] : Inhabited (DPRing A) :=
  ⟨{toCommSemiring := inferInstance
    dpIdeal := ⊥
    dividedPowers := dividedPowersBot A }⟩

end DividedPowersDefinition

namespace DividedPowers

open Finset

section BasicLemmas

variable {A : Type*} [CommSemiring A] {I : Ideal A}

lemma dpow_add' (hI : DividedPowers I) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    hI.dpow n (x + y) = (range (n + 1)).sum fun k => hI.dpow k x * hI.dpow (n - k) y := by
  rw [hI.dpow_add n hx hy, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The power series `∑ (hI.dpow n a) * x^n`. -/
def dpowExp (hI : DividedPowers I) (a : A) := PowerSeries.mk fun n => hI.dpow n a

theorem dpowExp_add (hI : DividedPowers I) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    hI.dpowExp (a + b) = hI.dpowExp a * hI.dpowExp b := by
  ext n
  simp only [dpowExp, PowerSeries.coeff_mk, PowerSeries.coeff_mul, hI.dpow_add n ha hb,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem eq_of_eq_on_ideal (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : ∀ (n : ℕ) {x : A} (_ : x ∈ I), hI.dpow n x = hI'.dpow n x) : hI = hI' := by
  ext n x
  by_cases hx : x ∈ I
  · exact h_eq n hx
  · rw [hI.dpow_null hx, hI'.dpow_null hx]

variable (hI : DividedPowers I)

-- Rewriting lemmas

theorem dpow_smul' (n : ℕ) (a : A) {x : A} (hx : x ∈ I) :
    hI.dpow n (a • x) = a ^ n • hI.dpow n x := by
  simp only [smul_eq_mul, hI.dpow_smul, hx]

@[simp]
theorem dpow_mul_right {n : ℕ} {a : A} {x : A} (ha : x ∈ I) :
    hI.dpow n (x * a) = hI.dpow n x * a ^ n := by
  rw [mul_comm, hI.dpow_smul n ha, mul_comm]

theorem dpow_smul_right {n : ℕ} {a : A} {x : A} (hx : x ∈ I) :
    hI.dpow n (x • a) = hI.dpow n x • a ^ n := by
  rw [smul_eq_mul, hI.dpow_mul_right hx, smul_eq_mul]

theorem factorial_mul_dpow_eq_pow {n : ℕ} {x : A} (hx : x ∈ I) :
    (n.factorial : A) * hI.dpow n x = x ^ n := by
  induction n with
  | zero => rw [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, hI.dpow_zero hx]
  | succ n ih =>
    rw [Nat.factorial_succ, mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← Nat.choose_symm_add, Nat.cast_mul, mul_assoc,
      ← hI.dpow_mul n 1 hx, ← mul_assoc, ih, hI.dpow_one hx, pow_succ', mul_comm]

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_smul n I.zero_mem,
    zero_pow hn, zero_mul, zero_mul]

/-- Proposition 1.2.7 of [B74], part (i). -/
theorem nilpotent_of_mem_dpIdeal (hI : DividedPowers I) {n : ℕ} (hn : n ≠ 0)
    (hnI : ∀ {y : A} (_ : y ∈ I), n • y = 0) {x : A} (hx : x ∈ I) : x ^ n = 0 := by
  have h_fac : (n.factorial : A) * hI.dpow n x =
    n • ((n - 1).factorial : A) * hI.dpow n x := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_factorial_pred (Nat.pos_of_ne_zero hn)]
  rw [← factorial_mul_dpow_eq_pow hI hx, h_fac, smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1).factorial : A) (hI.dpow_mem hn hx))

/-- If `J` is another ideal of `A` with divided powers, then the divided powers of `I` and `J`
  coincide on `I • J` (Berthelot, 1.6.1 (ii))-/
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : ℕ} {a : A} (ha : a ∈ I • J) :
    hI.dpow n a = hJ.dpow n a := by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [Algebra.id.smul_eq_mul, hJ.dpow_smul n hb, mul_comm a b, hI.dpow_smul n ha,
      ← hJ.factorial_mul_dpow_eq_pow hb, ← hI.factorial_mul_dpow_eq_pow ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add n (Ideal.mul_le_right hx) (Ideal.mul_le_right hy),
      hJ.dpow_add n (Ideal.mul_le_left hx) (Ideal.mul_le_left hy)]
    exact sum_congr rfl (fun _ _ ↦ by rw [hx', hy'])

-- Rob65, formula (III')
/-- A product of divided powers is a multinomial coefficient times the divided power-/
theorem mul_dpow {ι : Type*} {s : Finset ι} (n : ι → ℕ) {a : A} (ha : a ∈ I) :
    (s.prod fun i => hI.dpow (n i) a) = Nat.multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, Nat.multinomial_empty, Nat.cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert hi hrec =>
    rw [prod_insert hi, hrec, ← mul_assoc, mul_comm (hI.dpow (n _) a),
      mul_assoc, dpow_mul _ _ _ ha, ← sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [Nat.multinomial_insert hi, mul_comm, Nat.cast_mul, sum_insert hi]

-- A slightly more general result is below but it is awkward to apply it
-- TODO : can probably be simplified using exponential series
-- Also : can it be used to deduce dpow_comp from the rest?
theorem dpow_sum_aux {dpow : ℕ → A → A} (dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1)
    (dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
      dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dpow n 0 = 0) {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    dpow n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => dpow (Multiset.count i k) (x i) := by
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn, dpow_zero I.zero_mem, sym_zero, card_singleton, Nat.cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← Nat.cast_zero]
      apply congr_arg
      rw [card_eq_zero, sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    have hx' : ∀ i, i ∈ s → x i ∈ I := fun i hi => hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha, dpow_add n (hx a (mem_insert_self a s)) (I.sum_mem fun i => hx' i),
      sum_range, ih hx', mul_sum, sum_sigma']
    apply symm
    apply sum_bij'
      (fun m _ => Sym.filterNe a m)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
        rw [mem_sym_iff]
        intro i hi
        rw [Sym.mem_fill_iff] at hi
        cases hi with
        | inl hi => simp only [ hi.2, mem_insert_self a s]
        | inr hi =>
          simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
          exact mem_insert_of_mem (hm i hi))
      (fun m _ => Sym.fill_filterNe a _ )
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← Sym.fill_filterNe a m, Sym.coe_fill]
      simp only [Multiset.count_add, add_right_eq_self, Multiset.count_eq_zero,
        Sym.mem_coe, Sym.mem_replicate, not_and]
      exact fun _ => ne_of_mem_of_not_mem hi ha
    · intro m hm
      convert sym_filterNe_mem a hm
      rw [erase_insert ha]
    -- adjust once multinomial has been incorporated to mathlib

/-- A generic “multinomial” theorem for divided powers — but without multinomial coefficients
  — using only `dpow_zero`, `dpow_add` and `dpow_eval_zero`  -/
theorem dpow_sum_aux' {M D : Type*} [AddCommMonoid M] [CommSemiring D] {dpow : ℕ → M → D}
    (dpow_zero : ∀ x, dpow 0 x = 1)
    (dpow_add : ∀ n x y, dpow n (x + y) = (antidiagonal n).sum fun (k, l) => dpow k x * dpow l y)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dpow n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → M} (n : ℕ) :
    dpow n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => dpow (Multiset.count i k) (x i) := by
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction_on generalizing n with
  | empty =>
    rw [sum_empty]
    by_cases hn : n = 0
    · rw [hn, dpow_zero, sum_unique_nonempty, prod_empty]
      simp only [Nat.zero_eq, sym_zero, singleton_nonempty]
    · rw [dpow_eval_zero hn, eq_comm]
      convert sum_empty
      rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    simp_rw [sum_insert ha, dpow_add n, sum_range, ih, mul_sum, sum_sigma']
    apply symm
    apply sum_bij'
      (fun m _ => Sym.filterNe a m)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => Finset.mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
          rw [mem_sym_iff]
          intro i hi
          rw [Sym.mem_fill_iff] at hi
          cases hi with
          | inl hi => simp only [hi.2, mem_insert_self]
          | inr hi =>
            simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
            exact mem_insert_of_mem (hm i hi))
        (fun m _ => Sym.fill_filterNe a _)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← Sym.fill_filterNe a m, Sym.coe_fill]
      simp only [Multiset.count_add, add_right_eq_self, Multiset.count_eq_zero,
        Sym.mem_coe, Sym.mem_replicate, not_and]
      exact fun _ => ne_of_mem_of_not_mem hi ha
    · intro m hm
      convert sym_filterNe_mem a hm
      rw [erase_insert ha]
    -- adjust once multinomial has been incorporated to mathlib

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    ∀ n : ℕ, hI.dpow n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => hI.dpow (Multiset.count i k) (x i) := by
  refine dpow_sum_aux hI.dpow_zero (fun n x y hx hy ↦ ?_) (fun hn ↦ hI.dpow_eval_zero hn) hx
  rw [hI.dpow_add n hx hy, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l ↦ hI.dpow k x * hI.dpow l y)]

theorem prod_dpow_self {ι : Type*} {s : Finset ι} {n : ι → ℕ} (a : A) (ha : a ∈ I) :
    (s.prod fun i => hI.dpow (n i) a) = Nat.multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction' s using Finset.induction with i s hi ih
  · rw [prod_empty, sum_empty, hI.dpow_zero ha, Nat.multinomial_empty, Nat.cast_one, mul_one]
  · rw [prod_insert hi, ih, ← mul_assoc, mul_comm (hI.dpow _ a), mul_assoc, hI.dpow_mul _ _ ha,
      ← sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [mul_comm, Nat.multinomial_insert hi, sum_insert hi, Nat.cast_mul]

end BasicLemmas

section Equiv

variable {A B : Type*} [CommRing A] {I : Ideal A} [CommRing B] {J : Ideal B} (e : A ≃+* B)

example : I.map e = I.comap e.symm := Eq.symm (Ideal.comap_symm I e)

theorem _root_.Ideal.symm_mem (h : I.map e = J) (b : B) : e.symm b ∈ I ↔ b ∈ J := by
  simp only [← h, ← Ideal.comap_symm]; rfl

theorem _root_.Ideal.equiv_apply_mem (h : I.map e = J) (a : A) : e a ∈ J ↔ a ∈ I := by
  rw [← Ideal.symm_mem e h]
  simp only [RingEquiv.symm_apply_apply]

/-- Transfer divided powers under a ring isomorphism. -/
def ofRingEquiv (h : I.map e = J) (hI : DividedPowers I) : DividedPowers J where
  dpow n b := e (hI.dpow n (e.symm b))
  dpow_null {n} {x} hx := by
    rw [AddEquivClass.map_eq_zero_iff, hI.dpow_null]
    rwa [Ideal.symm_mem e h]
  dpow_zero {x} hx := by
    rw [MulEquivClass.map_eq_one_iff, hI.dpow_zero]
    rwa [Ideal.symm_mem e h]
  dpow_one {x} hx := by
    simp only
    rw [dpow_one, RingEquiv.apply_symm_apply]
    rwa [Ideal.symm_mem e h]
  dpow_mem {n} {x} hn hx := by
    simp only [Ideal.equiv_apply_mem e h]
    apply hI.dpow_mem hn
    rw [Ideal.symm_mem e h]
    exact hx
  dpow_add n {x y} hx hy:= by
    simp only [map_add, hI.dpow_add n ((Ideal.symm_mem e h x).mpr hx)
      ((Ideal.symm_mem e h y).mpr hy), map_sum, map_mul]
  dpow_smul n {a x} hx := by
    simp only [map_mul, hI.dpow_smul n ((Ideal.symm_mem e h x).mpr hx), map_pow,
      RingEquiv.apply_symm_apply]
  dpow_mul m n {x} hx := by
    simp only
    rw [← map_mul, hI.dpow_mul, map_mul]
    simp only [map_natCast]
    exact (Ideal.symm_mem e h x).mpr hx
  dpow_comp m {n x} hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp _ hn, map_mul, map_natCast]
    exact (Ideal.symm_mem e h x).mpr hx

@[simp]
theorem ofRingEquiv_eq (h : I.map e = J) (hI : DividedPowers I) (n : ℕ) (b : B) :
    (ofRingEquiv e h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

theorem ofRingEquiv_eq' (h : I.map e = J) (hI : DividedPowers I) (n : ℕ) (a : A) :
    (ofRingEquiv e h hI).dpow n (e a) = e (hI.dpow n a) := by
  simp only [ofRingEquiv_eq, RingEquiv.symm_apply_apply]

/-- Transfer divided powers under a ring isomorphism (Equiv version) -/
def equiv (h : I.map e = J) : DividedPowers I ≃ DividedPowers J where
  toFun := ofRingEquiv e h
  invFun := ofRingEquiv e.symm (by
    rw [← h]
    change Ideal.map e.symm.toRingHom (I.map e.toRingHom) = I
    rw [Ideal.map_map]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, Ideal.map_id])
  left_inv  := fun hI ↦ by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ ↦ by ext n b; simp [ofRingEquiv]

lemma equiv_apply (h : I.map e = J) (hI : DividedPowers I) (n : ℕ) (b : B) :
    (equiv e h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

lemma equiv_apply' (h : I.map e = J) (hI : DividedPowers I) (n : ℕ) (a : A) :
    (equiv e h hI).dpow n (e a) = e (hI.dpow n a) :=
  ofRingEquiv_eq' e h hI n a

end Equiv

end DividedPowers
