/- ACL and MIdFF, Lean 2022 meeting at Icerm 
! This file was ported from Lean 3 source module divided_powers.basic
-/
import Mathbin.RingTheory.PowerSeries.Basic
import Oneshot.AlgebraLemmas
import Oneshot.CombinatoricsLemmas
import Mathbin.Data.Nat.Choose.Multinomial

/-! # Divided powers 

Let `A` be a commutative ring and `I` be an ideal of `A`. 
A *divided power* structure on `I` is the datum of operations `div_pow : ℕ → I → A` 
satisfying relations that model the intuitive formula `div_pow n a = a ^ n / n.factorial` and
collected by the structure `divided_powers`.
To avoid coercions, we rather consider `div_pow : ℕ → A → A`, extended by 0.

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

/-- The divided power structure on an ideal I of a commutative ring A -/
@[ext]
structure DividedPowers {A : Type _} [CommRing A] (I : Ideal A) where
  dpow : ℕ → A → A
  dpow_null : ∀ {n x} (hx : x ∉ I), dpow n x = 0
  dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1
  dpow_one : ∀ {x} (hx : x ∈ I), dpow 1 x = x
  dpow_mem : ∀ {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow n x ∈ I
  dpow_add :
    ∀ (n) {x y} (hx : x ∈ I) (hy : y ∈ I),
      dpow n (x + y) = Finset.sum (Finset.range (n + 1)) fun k => dpow k x * dpow (n - k) y
  dpow_smul : ∀ (n) {a : A} {x} (hx : x ∈ I), dpow n (a * x) = a ^ n * dpow n x
  dpow_mul : ∀ (m n) {x} (hx : x ∈ I), dpow m x * dpow n x = Nat.choose (m + n) m * dpow (m + n) x
  dpow_comp :
    ∀ (m) {n} (hn : n ≠ 0) {x} (hx : x ∈ I), dpow m (dpow n x) = mchoose m n * dpow (m * n) x
#align divided_powers DividedPowers

def dividedPowersBot (A : Type _) [CommRing A] [DecidableEq A] : DividedPowers (⊥ : Ideal A)
    where
  dpow n a := ite (a = 0) (ite (n = 0) 1 0) 0
  dpow_null n a ha := if_neg ha
  dpow_zero a ha := if_pos ha
  dpow_one a ha := by simp only [Nat.one_ne_zero, if_false, if_t_t, ha.symm]
  dpow_mem n hn a ha := by
    simp only [Ideal.mem_bot, ite_eq_right_iff]
    exact fun ha' hn' => False.ndrec _ (hn hn')
  dpow_add n a b ha hb :=
    by
    rw [ideal.mem_bot.mp ha, ideal.mem_bot.mp hb, add_zero, if_pos rfl]
    simp only [eq_self_iff_true, if_true, tsub_eq_zero_iff_le, boole_mul, Finset.sum_ite_eq',
      Finset.mem_range, add_pos_iff, Nat.lt_one_iff, or_true_iff, le_zero_iff]
  dpow_smul n a x hx :=
    by
    rw [ideal.mem_bot.mp hx, MulZeroClass.mul_zero, if_pos rfl, mul_ite, MulZeroClass.mul_zero,
      mul_one]
    by_cases hn : n = 0
    rw [if_pos hn, hn, pow_zero, if_pos rfl]
    simp only [if_neg hn]
  dpow_mul m n x hx :=
    by
    simp only [mul_ite, mul_boole, MulZeroClass.mul_zero, add_eq_zero_iff]
    apply congr_arg₂ _ _ rfl
    by_cases hm : m = 0
    simp only [hm, eq_self_iff_true, if_true, true_and_iff, Nat.choose_zero_right,
      algebraMap.coe_one]
    apply congr_arg₂ _ _ rfl
    rw [ideal.mem_bot.mp hx, if_pos rfl]
    simp only [if_neg hm, if_t_t]
    rw [if_neg fun h : m = 0 ∧ n = 0 => hm h.1]
  dpow_comp m n hn a ha := by
    rw [if_neg hn, ideal.mem_bot.mp ha, if_pos rfl]
    simp only [eq_self_iff_true, if_true, Nat.mul_eq_zero, mul_boole]
    by_cases hm : m = 0
    simp only [hm, mchoose_zero, eq_self_iff_true, true_or_iff, algebraMap.coe_one]
    rw [if_neg hm]
    rw [if_neg]; intro h
    cases' h with h h
    exact hm h; exact hn h
#align divided_powers_bot dividedPowersBot

instance {A : Type _} [CommRing A] [DecidableEq A] : Inhabited (DividedPowers (⊥ : Ideal A)) :=
  ⟨dividedPowersBot A⟩

instance {A : Type _} [CommRing A] (I : Ideal A) : CoeFun (DividedPowers I) fun _ => ℕ → A → A :=
  ⟨fun hI => hI.dpow⟩

theorem coe_to_fun_apply {A : Type _} [CommRing A] (I : Ideal A) (hI : DividedPowers I) (n : ℕ)
    (a : A) : hI n a = hI.dpow n a :=
  rfl
#align coe_to_fun_apply coe_to_fun_apply

structure PdRing (A : Type _) extends CommRing A where
  pdIdeal : Ideal A
  DividedPowers : DividedPowers pd_ideal
#align pd_ring PdRing

instance {A : Type _} [CommRing A] [DecidableEq A] : Inhabited (PdRing A)
    where default :=
    { toCommRing := inferInstance
      pdIdeal := ⊥
      DividedPowers := dividedPowersBot A }

end DividedPowersDefinition

namespace DividedPowers

section BasicLemmas

variable {A : Type _} [CommRing A] {I : Ideal A}

def dpowExp (hI : DividedPowers I) (a : A) :=
  PowerSeries.mk fun n => hI.dpow n a
#align divided_powers.dpow_exp DividedPowers.dpowExp

theorem add_dpowExp (hI : DividedPowers I) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    hI.dpowExp (a + b) = hI.dpowExp a * hI.dpowExp b :=
  by
  ext
  simp only [dpow_exp, PowerSeries.coeff_mk, PowerSeries.coeff_mul, hI.dpow_add n ha hb,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
#align divided_powers.add_dpow_exp DividedPowers.add_dpowExp

theorem eq_of_eq_on_ideal (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : ∀ (n : ℕ) {x : A} (hx : x ∈ I), hI.dpow n x = hI'.dpow n x) : hI = hI' :=
  by
  ext n x
  by_cases hx : x ∈ I
  · exact h_eq n hx
  · rw [hI.dpow_null hx, hI'.dpow_null hx]
#align divided_powers.eq_of_eq_on_ideal DividedPowers.eq_of_eq_on_ideal

/- noncomputable
def dpow_of_dpow_exp (I : ideal A) (ε : I → power_series A) : 
  ℕ → A → A := λ n,
  function.extend 
    (λ (a : I), a.val) 
    (λ a, power_series.coeff A n (ε a))
    (λ (a :A) , (0 : A))

-- Golfed version of definition
noncomputable def dpow_of_dpow_exp (I : ideal A) (ε : I → power_series A) : ℕ → A → A := 
λ n, function.extend (λ (a : I), (a : A)) (λ (a : I), power_series.coeff A n (ε a)) 0

def divided_powers_of_dpow_exp (I : ideal A) (ε : I → power_series A)
  (hε_add : ∀ (a b : I), ε(a + b) = ε(a) * ε(b))
  (hε_zero : ε(0) = 1) -/
variable (hI : DividedPowers I)

-- Rewriting lemmas
theorem dpow_smul' (n : ℕ) (a : A) {x : A} (hx : x ∈ I) : hI.dpow n (a • x) = a ^ n • hI.dpow n x :=
  by simp only [smul_eq_mul, hI.dpow_smul, hx]
#align divided_powers.dpow_smul' DividedPowers.dpow_smul'

theorem dpow_mul_right (n : ℕ) {a : A} (ha : a ∈ I) (x : A) :
    hI.dpow n (a * x) = hI.dpow n a * x ^ n := by rw [mul_comm, hI.dpow_smul n ha, mul_comm]
#align divided_powers.dpow_mul_right DividedPowers.dpow_mul_right

theorem dpow_smul_right (n : ℕ) {a : A} (ha : a ∈ I) (x : A) :
    hI.dpow n (a • x) = hI.dpow n a • x ^ n := by
  rw [smul_eq_mul, hI.dpow_mul_right n ha, smul_eq_mul]
#align divided_powers.dpow_smul_right DividedPowers.dpow_smul_right

theorem factorial_mul_dpow_eq_pow (n : ℕ) (x : A) (hx : x ∈ I) :
    (n.factorial : A) * hI.dpow n x = x ^ n :=
  by
  induction' n with n ih
  · rw [Nat.zero_eq, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, hI.dpow_zero hx]
  ·
    rw [Nat.factorial_succ, mul_comm (n + 1), ← (n + 1).choose_one_right, ← Nat.choose_symm_add,
      Nat.cast_mul, Nat.succ_eq_add_one, mul_assoc, ← hI.dpow_mul n 1 hx, ← mul_assoc, ih,
      hI.dpow_one hx, pow_succ']
#align divided_powers.factorial_mul_dpow_eq_pow DividedPowers.factorial_mul_dpow_eq_pow

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_smul n I.zero_mem, zero_pow' n hn,
    MulZeroClass.zero_mul, MulZeroClass.zero_mul]
#align divided_powers.dpow_eval_zero DividedPowers.dpow_eval_zero

/-- Proposition 1.2.7 of [B74], part (i). -/
theorem nilpotent_of_pd_ideal_mem (hI : DividedPowers I) {n : ℕ} (hn : n ≠ 0)
    (hnI : ∀ {y : A} (hy : y ∈ I), n • y = 0) {x : A} (hx : x ∈ I) : x ^ n = 0 :=
  by
  have h_fac : (n.factorial : A) * hI.dpow n x = n • ((n - 1).factorial : A) * hI.dpow n x := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_factorial_pred (Nat.pos_of_ne_zero hn)]
  rw [← factorial_mul_dpow_eq_pow hI _ _ hx, h_fac, smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1).factorial : A) (hI.dpow_mem hn hx))
#align divided_powers.nilpotent_of_pd_ideal_mem DividedPowers.nilpotent_of_pd_ideal_mem

/-- If J is another ideal of A with divided powers, 
then the divided powers of I and J coincide on I • J 
(Berthelot, 1.6.1 (ii))-/
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : ℕ} {a : A} (ha : a ∈ I • J) :
    hI.dpow n a = hJ.dpow n a := by
  revert n
  apply Submodule.smul_induction_on' ha
  · intro a ha b hb n
    rw [Algebra.id.smul_eq_mul, hJ.dpow_smul n hb, mul_comm a b, hI.dpow_smul n ha, ←
      hJ.factorial_mul_dpow_eq_pow n b hb, ← hI.factorial_mul_dpow_eq_pow n a ha]
    ring
  · intro x hx y hy hx' hy' n
    rw [hI.dpow_add n (Ideal.mul_le_right hx) (Ideal.mul_le_right hy),
      hJ.dpow_add n (Ideal.mul_le_left hx) (Ideal.mul_le_left hy)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hx', hy']
#align divided_powers.coincide_on_smul DividedPowers.coincide_on_smul

open Finset

-- Rob65, formula (III')
/-- A product of divided powers is a multinomial coefficient times the divided power-/
theorem mul_dpow {ι : Type _} {s : Finset ι} (n : ι → ℕ) {a : A} (ha : a ∈ I) :
    (s.Prod fun i => hI.dpow (n i) a) = Nat.multinomial s n * hI.dpow (s.Sum n) a := by
  classical
  revert s
  apply Finset.induction
  ·-- case : s = ∅
    simp only [prod_empty, Nat.multinomial_nil, algebraMap.coe_one, sum_empty, one_mul,
      hI.dpow_zero ha]
  · -- inductive step
    intro i s hi hrec
    rw [Finset.prod_insert hi, hrec, ← mul_assoc, mul_comm (hI.dpow (n i) a), mul_assoc,
      dpow_mul _ _ _ ha, ← Finset.sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [Nat.multinomial_insert _ _ hi, mul_comm, Nat.cast_mul, Finset.sum_insert hi]
#align divided_powers.mul_dpow DividedPowers.mul_dpow

-- A slightly more general result is below but it is awkward to apply it 
-- TODO : can probably be simplified using exponential series
-- Also : can it be used to deduce dpow_comp from the rest?
theorem dpow_sum_aux (dpow : ℕ → A → A) (dpow_zero : ∀ {x} (hx : x ∈ I), dpow 0 x = 1)
    (dpow_add :
      ∀ (n) {x y} (hx : x ∈ I) (hy : y ∈ I),
        dpow n (x + y) = Finset.sum (Finset.range (n + 1)) fun k => dpow k x * dpow (n - k) y)
    (dpow_eval_zero : ∀ {n : ℕ} (hn : n ≠ 0), dpow n 0 = 0) {ι : Type _} [DecidableEq ι]
    {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    ∀ n : ℕ,
      dpow n (s.Sum x) =
        (Finset.sym s n).Sum fun k => s.Prod fun i => dpow (Multiset.count i k) (x i) :=
  by
  induction' s using Finset.induction with a s ha ih
  · rw [sum_empty]
    rintro (_ | n)
    · rw [dpow_zero I.zero_mem, sum_unique_nonempty, prod_empty]
      exact univ_nonempty
    · rw [dpow_eval_zero (Nat.succ_ne_zero n), sym_empty, sum_empty]
  · have hx' : ∀ i, i ∈ s → x i ∈ I := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    intro n
    simp_rw [sum_insert ha,
      dpow_add n (hx a (Finset.mem_insert_self a s)) (I.sum_mem fun i => hx' i), sum_range, ih hx',
      mul_sum, sum_sigma']
    refine'
      (sum_bij' (fun m _ => Sym.filterNe a m) (fun m hm => Finset.mem_sigma.2 ⟨mem_univ _, _⟩)
          (fun m hm => _) (fun m _ => m.2.fill a m.1) _ (fun m _ => m.fill_filterNe a) fun m hm =>
          _).symm
    -- explicit arguments above rather than m.fill_filter_ne a
    -- adjust once multinomial has been incorporated to mathlib
    -- #3
    · convert sym_filter_ne_mem a hm; rw [erase_insert ha]
    -- #4
    · dsimp only [Sym.filterNe, Fin.val_mk]
      rw [Finset.prod_insert ha]
      apply congr_arg₂ _ rfl
      apply Finset.prod_congr rfl
      intro i hi; simp only [Subtype.val_eq_coe, Sym.mk_coe]
      apply congr_arg₂ _ _ rfl
      have ha : a ≠ i := by intro hi'; rw [hi'] at ha ; exact ha hi
      rw [Multiset.count_filter, if_pos ha]
    · exact fun m hm => sym_fill_mem a (mem_sigma.1 hm).2
    · exact Sym.filter_ne_fill a m (mt (mem_sym_iff.1 (mem_sigma.1 hm).2 a) ha)
#align divided_powers.dpow_sum_aux DividedPowers.dpow_sum_aux

/-- A generic “multinomial” theorem for divided powers — but without multinomial coefficients 
  — using only dpow_zero, dpow_add and dpow_eval_zero  -/
theorem dpow_sum_aux' {M D : Type _} [AddCommGroup M] [CommRing D] (dp : ℕ → M → D)
    (dpow_zero : ∀ x, dp 0 x = 1)
    (dpow_add :
      ∀ n x y, dp n (x + y) = Finset.sum (Finset.range (n + 1)) fun k => dp k x * dp (n - k) y)
    --  (dpow_smul : ∀ {n a x}, dp n (a • x) = a ^ n • dp n x)
    (dpow_eval_zero : ∀ {n : ℕ} (hn : n ≠ 0), dp n 0 = 0)
    {ι : Type _} [DecidableEq ι] {s : Finset ι} {x : ι → M} :
    ∀ n : ℕ,
      dp n (s.Sum x) =
        (Finset.sym s n).Sum fun k => s.Prod fun i => dp (Multiset.count i k) (x i) :=
  by
  induction' s using Finset.induction with a s ha ih
  · rw [sum_empty]
    rintro (_ | n)
    · rw [dpow_zero, sum_unique_nonempty, prod_empty]
      exact univ_nonempty
    · rw [dpow_eval_zero (Nat.succ_ne_zero n), sym_empty, sum_empty]
  · intro n
    simp_rw [sum_insert ha, dpow_add n, sum_range, ih, mul_sum, sum_sigma']
    refine'
      (sum_bij' (fun m _ => Sym.filterNe a m) (fun m hm => Finset.mem_sigma.2 ⟨mem_univ _, _⟩)
          (fun m hm => _) (fun m _ => m.2.fill a m.1) _ (fun m _ => m.fill_filterNe a) fun m hm =>
          _).symm
    -- explicit arguments above rather than m.fill_filter_ne a
    -- adjust once multinomial has been incorporated to mathlib
    -- #3
    · convert sym_filter_ne_mem a hm; rw [erase_insert ha]
    -- #4
    · dsimp only [Sym.filterNe, Fin.val_mk]
      rw [Finset.prod_insert ha]
      apply congr_arg₂ _ rfl
      apply Finset.prod_congr rfl
      intro i hi; simp only [Subtype.val_eq_coe, Sym.mk_coe]
      apply congr_arg₂ _ _ rfl
      have ha : a ≠ i := by intro hi'; rw [hi'] at ha ; exact ha hi
      rw [Multiset.count_filter, if_pos ha]
    · exact fun m hm => sym_fill_mem a (mem_sigma.1 hm).2
    · exact Sym.filter_ne_fill a m (mt (mem_sym_iff.1 (mem_sigma.1 hm).2 a) ha)
#align divided_powers.dpow_sum_aux' DividedPowers.dpow_sum_aux'

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem dpow_sum {ι : Type _} [DecidableEq ι] {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    ∀ n : ℕ,
      hI.dpow n (s.Sum x) =
        (Finset.sym s n).Sum fun k => s.Prod fun i => hI.dpow (Multiset.count i k) (x i) :=
  dpow_sum_aux hI.dpow (fun x hx => hI.dpow_zero hx) (fun n x y hx hy => hI.dpow_add n hx hy)
    (fun n hn => hI.dpow_eval_zero hn) hx
#align divided_powers.dpow_sum DividedPowers.dpow_sum

/- 
  let x' : s → I := λ i, ⟨x i, hx i i.prop⟩,
  haveI : fintype s, exact fintype_of_option,
  suffices :  s.sum x = coe(finset.univ.sum x'),  rw this,
  intro n,
--  simp only [submodule.coe_sum, submodule.coe_mk],
  have := @dpow_sum_aux I A _ _ (λ (n : ℕ) (a : I), hI.dpow n a) (λ x, hI.dpow_zero x.prop) _ _
    s _ finset.univ x' n,  

  -/
theorem prod_dpow_self {ι : Type _} {s : Finset ι} {n : ι → ℕ} (a : A) (ha : a ∈ I) :
    (s.Prod fun i => hI.dpow (n i) a) = Nat.multinomial s n * hI.dpow (s.Sum n) a := by
  classical
  induction' s using Finset.induction with i s hi ih
  ·
    rw [Finset.prod_empty, Finset.sum_empty, hI.dpow_zero ha, Nat.multinomial_nil, Nat.cast_one,
      mul_one]
  · rw [Finset.prod_insert hi, ih, ← mul_assoc, mul_comm (hI.dpow _ a), mul_assoc,
      hI.dpow_mul _ _ ha, ← Finset.sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [mul_comm, Nat.multinomial_insert s n hi, Finset.sum_insert hi, Nat.cast_mul]
#align divided_powers.prod_dpow_self DividedPowers.prod_dpow_self

end BasicLemmas

section DividedPowersMorphisms

/-- Compatibility of a ring morphism with pd-structures -/
def IsPdMorphism {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  I.map f ≤ J ∧ ∀ (n : ℕ), ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)
#align divided_powers.is_pd_morphism DividedPowers.IsPdMorphism

theorem IsPdMorphism.comp {A B C : Type _} [CommRing A] [CommRing B] [CommRing C] {I : Ideal A}
    {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hcomp : g.comp f = h) :
    IsPdMorphism hJ hK g → IsPdMorphism hI hJ f → IsPdMorphism hI hK h :=
  by
  intro hg hf; rw [← hcomp]
  constructor
  · apply le_trans _ hg.1
    rw [← Ideal.map_map]
    exact Ideal.map_mono hf.1
  · intro n a ha
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← hf.2 n a ha]
    rw [hg.2]
    apply hf.1
    exact Ideal.mem_map_of_mem f ha
#align divided_powers.is_pd_morphism.comp DividedPowers.IsPdMorphism.comp

/-- The structure of a pd_morphism between rings endowed with pd-rings -/
@[ext]
structure PdMorphism {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) where
  toRingHom : A →+* B
  ideal_comp : I.map to_ring_hom ≤ J
  dpow_comp : ∀ (n : ℕ), ∀ a ∈ I, hJ.dpow n (to_ring_hom a) = to_ring_hom (hI.dpow n a)
#align divided_powers.pd_morphism DividedPowers.PdMorphism

def pdMorphismFunLike {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) : FunLike (PdMorphism hI hJ) A fun _x : A => B
    where
  coe h := h.toRingHom
  coe_injective' h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh' ; ext; rw [hh']
#align divided_powers.pd_morphism_fun_like DividedPowers.pdMorphismFunLike

def PdMorphism.isPdMorphism {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    {hI : DividedPowers I} {hJ : DividedPowers J} (f : PdMorphism hI hJ) :
    IsPdMorphism hI hJ f.toRingHom :=
  ⟨f.ideal_comp, f.dpow_comp⟩
#align divided_powers.pd_morphism.is_pd_morphism DividedPowers.PdMorphism.isPdMorphism

-- Roby65, Proposition 2. (TODO: rename?)
/-- The ideal on which two divided power structures on two ideals coincide -/
def pdMorphismIdeal {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) {f : A →+* B} (hf : I.map f ≤ J) : Ideal A
    where
  carrier := {x ∈ I | ∀ n : ℕ, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' x y hx hy :=
    by
    simp only [Set.mem_sep_iff, SetLike.mem_coe] at hx hy ⊢
    refine' ⟨I.add_mem hx.1 hy.1, _⟩
    intro n
    rw [hI.dpow_add _ hx.1 hy.1, map_add,
      hJ.dpow_add _ (hf (Ideal.mem_map_of_mem f hx.1)) (hf (Ideal.mem_map_of_mem f hy.1)), map_sum]
    apply congr_arg
    ext k
    rw [map_mul, hx.2 k, hy.2 (n - k)]
  zero_mem' :=
    by
    simp only [Set.mem_sep_iff, SetLike.mem_coe, Submodule.zero_mem, map_zero, true_and_iff]
    intro n
    cases n
    · rw [hI.dpow_zero I.zero_mem, hJ.dpow_zero J.zero_mem, map_one]
    · rw [hI.dpow_eval_zero n.succ_ne_zero, hJ.dpow_eval_zero n.succ_ne_zero, map_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_sep_iff, SetLike.mem_coe] at hx ⊢
    refine' ⟨I.smul_mem r hx.1, _⟩
    intro n
    rw [smul_eq_mul, hI.dpow_smul _ hx.1, map_mul, map_mul, map_pow,
      hJ.dpow_smul _ (hf (Ideal.mem_map_of_mem f hx.1)), hx.2 n]
#align divided_powers.pd_morphism_ideal DividedPowers.pdMorphismIdeal

-- Roby65, Proposition 3.  (TODO: rename?)
/-- The pd morphism induced by a ring morphism, provided divided powers match on a generating set -/
def pdMorphismFromGens {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) {f : A →+* B} {S : Set A} (hS : I = Ideal.span S)
    (hf : I.map f ≤ J) (h : ∀ (n : ℕ), ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    PdMorphism hI hJ where
  toRingHom := f
  ideal_comp := hf
  dpow_comp n x hx :=
    by
    have hS' : S ⊆ pd_morphism_ideal hI hJ hf :=
      by
      intro y hy
      simp only [SetLike.mem_coe, pd_morphism_ideal, Submodule.mem_mk, Set.mem_sep_iff,
        SetLike.mem_coe]
      exact ⟨by rw [hS]; exact Ideal.subset_span hy, fun n => h n y hy⟩
    rw [← Ideal.span_le, ← hS] at hS' 
    exact ((hS' hx).2 n).symm
#align divided_powers.pd_morphism_from_gens DividedPowers.pdMorphismFromGens

/-- Identity as a pd morphism -/
def PdMorphism.id {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I) : PdMorphism hI hI
    where
  toRingHom := RingHom.id A
  ideal_comp := by simp only [Ideal.map_id, le_refl]
  dpow_comp n a ha := by simp only [RingHom.id_apply]
#align divided_powers.pd_morphism.id DividedPowers.PdMorphism.id

instance {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I) :
    Inhabited (PdMorphism hI hI) :=
  ⟨PdMorphism.id hI⟩

theorem pdMorphismFromGens_coe {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A}
    (hI : DividedPowers I) {J : Ideal B} (hJ : DividedPowers J) {f : A →+* B} {S : Set A}
    (hS : I = Ideal.span S) (hf : I.map f ≤ J)
    (h : ∀ (n : ℕ), ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    (pdMorphismFromGens hI hJ hS hf h).toRingHom = f :=
  rfl
#align divided_powers.pd_morphism_from_gens_coe DividedPowers.pdMorphismFromGens_coe

/- lemma pd_morphism_from_gens_apply {A B : Type*} [comm_ring A] [comm_ring B] {I : ideal A} 
  (hI : divided_powers I) {J : ideal B} (hJ : divided_powers J) {f : A →+* B} {S : set A} 
  (hS : I = ideal.span S) (hf : I.map f ≤ J)
  (h : ∀ (n : ℕ) (x ∈ S), f (hI.dpow n x) = hJ.dpow n (f x)) (a : A) : 
  (pd_morphism_from_gens hI hJ hS hf h) a = f a:=
rfl
-/
-- Bizarre
def pdMorphismOfLe {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type _}
    [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : PdMorphism hI hI) {K : Ideal B}
    (hJK : K ≤ J) : PdMorphism hI hI
    where
  toRingHom := RingHom.id A
  ideal_comp := by simp only [Ideal.map_id, le_refl]
  dpow_comp n a ha := by simp only [RingHom.id_apply]
#align divided_powers.pd_morphism_of_le DividedPowers.pdMorphismOfLe

-- Generalization
theorem isPdMorphism_on_span {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) {S : Set A} (hS : I = Ideal.span S)
    (hS' : ∀ s ∈ S, f s ∈ J) (hdp : ∀ (n : ℕ), ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    IsPdMorphism hI hJ f := by
  suffices : I.map f ≤ J
  apply And.intro this
  let pd_f := pd_morphism_from_gens hI hJ hS this hdp
  intro n a ha
  rw [← pd_morphism_from_gens_coe hI hJ hS this hdp]
  rw [pd_f.dpow_comp n a ha]
  rw [hS]; rw [Ideal.map_span]
  rw [Ideal.span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has
#align divided_powers.is_pd_morphism_on_span DividedPowers.isPdMorphism_on_span

theorem dp_uniqueness {A B : Type _} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) {S : Set A} (hS : I = Ideal.span S)
    (hS' : ∀ s ∈ S, f s ∈ J) (hdp : ∀ (n : ℕ), ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    ∀ (n), ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  (isPdMorphism_on_span hI hJ f hS hS' hdp).2
#align divided_powers.dp_uniqueness DividedPowers.dp_uniqueness

theorem IsPdMorphism.of_comp {A B C : Type _} [CommRing A] [CommRing B] [CommRing C] {I : Ideal A}
    {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hcomp : g.comp f = h) (sf : J = I.map f) :
    IsPdMorphism hI hJ f → IsPdMorphism hI hK h → IsPdMorphism hJ hK g :=
  by
  intro hf hh
  apply is_pd_morphism_on_span; exact sf
  rintro b ⟨a, ha, rfl⟩; rw [← RingHom.comp_apply]; rw [hcomp]
  apply hh.1; apply Ideal.mem_map_of_mem; exact ha
  rintro n b ⟨a, ha, rfl⟩
  rw [← RingHom.comp_apply, hcomp, hh.2 n a ha, ← hcomp, RingHom.comp_apply]
  rw [hf.2 n a ha]
#align divided_powers.is_pd_morphism.of_comp DividedPowers.IsPdMorphism.of_comp

-- Roby65, corollary after proposition 3
/-- Uniqueness of a divided powers given its values on a generating set -/
theorem dp_uniqueness_self {A : Type _} [CommRing A] {I : Ideal A} (hI hI' : DividedPowers I)
    {S : Set A} (hS : I = Ideal.span S) (hdp : ∀ (n : ℕ), ∀ a ∈ S, hI.dpow n a = hI'.dpow n a) :
    hI' = hI := by
  ext n a
  by_cases ha : a ∈ I
  simpa only using hI.dp_uniqueness hI' (RingHom.id A) hS _ _ n a ha
  · simp only [RingHom.id_apply, hS]
    intro s hs; exact Ideal.subset_span hs
  · simpa only [RingHom.id_apply] using hdp
  -- case a ∉ I
  · rw [hI.dpow_null ha, hI'.dpow_null ha]
#align divided_powers.dp_uniqueness_self DividedPowers.dp_uniqueness_self

-- For the moment, the notation does not work
-- notation `p(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := pd_morphism hI hJ
-- Also, we expect a `pd` subscript
-- TODO : identity (done), composition…
end DividedPowersMorphisms

end DividedPowers

/- Comparison with Berthelot, Coho. cristalline

1.1 : done
1.2.1 : follows from 1.2.7 - done (for ℚ-algebras).
1.2.2 (*) : To be added
1.2.4 : To be added if Cohen/Witt vectors rings exist
1.2.7 (M) : done
1.3 (pd -morphism) : done
1.3.1 : To be added (needs colimits of rings)

1.4 : To be added, but difficult
1.5.: depends on 1.4  

1.6 : sub-pd-ideal : done
1.6.1 Done !
1.6.2 : Done : dpow_quot]
1.6.4 (A) : to be added
(should we add the remark on page 33)
1.6.5 (A): to be added

1.7 : tensor product, see Roby

1.8 (M). Done! 


PRs : 
 (M) : ring_inverse, tsub_tsub - DONE
 (A) : submodule_induction, function.extend_apply_first - DONE

Delete obsolete versions
 (A) : rewrite_4_sums -- Done, I think, but how could we simplify these lemmas?

(A) Simplify, 
  remove not_eq_or_aux (see REMOVE or MOVE) -- DONE
  Prove uniqueness of pd-structure when possible
    (ideal_add [Done], dpow_quot [Done])
(M) Complete the lattice structure

-/
example (M : Type _) [AddMonoid M] : AddMonoid (WithTop M) := by refine' WithTop.addMonoid

/- Roby (1965):
 - Pregraded algebra (using mathlib's graded_algebra) - with_top unit (later, if needed)
 - Tensor product of graded algebras is a graded algebra
 - Add III' explicitly.
 - Proposition 1 -- I think this is essentially Lemma 3.6 of [BO].
 - Proposition 2
 - Proposition 3

 I just noticed that we are using dp and pd in different names, we should pick a convention.
-/
/- 
Idea of generalizing the theory to more general divisors systems
modeling x^n/n!, x^n/p^n, etc.
but it is not clear what to consider
Also, not clear it can really be done…

structure divisor_system {R : Type*} [comm_ring R] := 
(dpow_choose : ℕ → ℕ → R)
(dpow_mchoose : ℕ → ℕ → R)
-- (conditions : Prop)
Two options :
1) dpow n x = x^n/(c n)
Examples : c n = n.factorial,  c n = p ^ n
2) dpow n x = x ^ n / (d 1 * d 2 * ... * d n)
Examples : d n = n,  d n = p

dpow n (x + y) = (x+y)^n / c n
 = sum  (n.choose k) x ^(n -k) y ^k / c n
 = sum [(n.choose k) (c k) (c (n-k)) / c n] dpow (n - k) x * dpow k y 

  Case 1 : dpow_choose n k = 1 ;  case 2 : dpow_choose n k = choose

dpow m x * dpow n x = x ^ m * x ^ n / c m * c n
  = dpow (m + n) x * (c (n+m) / c m * c n)

   Case 1 : coeff = (n+m).choose m ; Case 2 :  = 1

dpow m (dpow n x) = (x ^n / c n) ^ m / c m = x ^ (m n) / ((c n ^ m) * c m)
 = [ ] * dpow (m n) x
  with [ ] = c (m n)/ (c n)^m (c m)

  Case 1 : [ ] = mchoose m n, case 2 : p^ (-m)

-/
