/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.Exponential
import Mathlib.LinearAlgebra.Isomorphisms
import DividedPowers.BasicLemmas
import DividedPowers.DPMorphism
import DividedPowers.RatAlgebra
import Mathlib.Data.Nat.Choose.Vandermonde

section Polynomial

open Ring

theorem Polynomial.C_eq_smul_one {R : Type*} [Semiring R] {a : R} :
    (C a : Polynomial R) = a • (1 : Polynomial R) := by
  rw [← C_mul', mul_one]

theorem Polynomial.inv_C_eq_C_inv {R : Type*} [CommSemiring R] {a : R} :
    inverse (C a) = C (inverse a) := by
  simp only [inverse]
  by_cases ha : IsUnit a
  · have hCa : IsUnit (C a) := by
      rw [← IsUnit.unit_spec ha]
      exact RingHom.isUnit_map C ha
    rw [dif_pos ha, dif_pos hCa]
    apply IsUnit.mul_right_cancel hCa
    simp only [← map_mul, IsUnit.val_inv_mul, map_one]
  · simp only [inverse, dif_neg ha, map_zero]
    rw [dif_neg]
    intro hCa
    apply ha
    rw [isUnit_iff_exists_inv] at hCa ⊢
    obtain ⟨b, hb⟩ := hCa
    use b.coeff 0
    rw [← Polynomial.coeff_C_mul, hb, coeff_one_zero]

end Polynomial

section onSup

namespace LinearMap

open Submodule

variable {A : Type*} [Ring A] {X Y : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    {M N : Submodule A X} {f : M →ₗ[A] Y} {g : N →ₗ[A] Y}

noncomputable def _root_.Submodule.quotientCoprodAddEquiv :
    ((M × N) ⧸ (ker ((inclusion (le_sup_left (b := N))).coprod (inclusion (le_sup_right (a := M)))))) ≃ₗ[A] (M + N) := by
  apply quotKerEquivOfSurjective
  rw [← range_eq_top, eq_top_iff]
  rintro ⟨x, hx⟩ _
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
  use ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  simp [← Subtype.coe_inj]

noncomputable def onSup (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) :
    M + N →ₗ[A] Y := by
  apply comp ?_ quotientCoprodAddEquiv.symm.toLinearMap
  apply (ker _).liftQ (f.coprod g)
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ hxy
  simp only [Submodule.add_eq_sup, mem_ker, coprod_apply,
    add_eq_zero_iff_eq_neg, ← Subtype.coe_inj, coe_inclusion, NegMemClass.coe_neg] at hxy
  simp only [mem_ker, coprod_apply, add_eq_zero_iff_eq_neg, ← map_neg]
  have : - (⟨y, hy⟩ : N) = ⟨-y, N.neg_mem hy⟩ := by simp [← Subtype.coe_inj]
  rw [this]
  simp_rw [hxy]
  apply h

theorem onSup_apply_left (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩)
    {x} (hx : x ∈ M) : onSup h ⟨x, le_sup_left (b := N) hx⟩ = f ⟨x, hx⟩ := by
  simp only [Submodule.add_eq_sup, onSup, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  suffices (quotientCoprodAddEquiv (M := M) (N := N)).symm ⟨x, le_sup_left (b := N) hx⟩ =
    Submodule.Quotient.mk ⟨⟨x, hx⟩, (0 : N)⟩ by
    erw [this]
    simp [liftQ_apply]
  rw [LinearEquiv.symm_apply_eq]
  simp only [Submodule.add_eq_sup, quotientCoprodAddEquiv, quotKerEquivOfSurjective,
    LinearEquiv.trans_apply, LinearEquiv.ofTop_apply, quotKerEquivRange_apply_mk, coprod_apply,
    _root_.map_zero, add_zero, inclusion_apply]

theorem onSup_apply_right (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩)
    {x} (hx : x ∈ N) : onSup h ⟨x, le_sup_right (a := M) hx⟩ = g ⟨x, hx⟩ := by
  simp only [Submodule.add_eq_sup, onSup, coe_comp, coe_coe, Function.comp_apply]
  suffices (quotientCoprodAddEquiv (M := M) (N := N)).symm ⟨x, le_sup_right (a := M) hx⟩ =
    Submodule.Quotient.mk ⟨(0 : M), ⟨x, hx⟩⟩ by
    erw [this]
    simp [liftQ_apply]
  rw [LinearEquiv.symm_apply_eq]
  simp only [Submodule.add_eq_sup, quotientCoprodAddEquiv, quotKerEquivOfSurjective,
    LinearEquiv.trans_apply, LinearEquiv.ofTop_apply, quotKerEquivRange_apply_mk, coprod_apply,
    _root_.map_zero, zero_add, inclusion_apply]

theorem onSup_apply (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩)
    {x y} (hx : x ∈ M) (hy : y ∈ N) :
    onSup h ⟨x + y, add_mem_sup hx hy⟩ = f ⟨x, hx⟩ + g ⟨y, hy⟩ := by
  rw [← onSup_apply_left h hx, ← onSup_apply_right h hy, ← map_add, AddMemClass.mk_add_mk]

theorem onSup_comp_left (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) :
    (onSup h).comp (inclusion le_sup_left) = f := by
  ext ⟨x, hx⟩
  rw [← onSup_apply_left h, comp_apply, inclusion_apply]

theorem onSup_comp_right (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) :
    (onSup h).comp (inclusion le_sup_right) = g := by
  ext ⟨x, hx⟩
  rw [← onSup_apply_right h, comp_apply, inclusion_apply]

theorem onSup_unique (h : ∀ x (hM : x ∈ M) (hN : x ∈ N), f ⟨x, hM⟩ = g ⟨x, hN⟩) {u : M + N →ₗ[A] Y}
    (huf : u.comp (inclusion le_sup_left) = f) (hug : u.comp (inclusion le_sup_right) = g) :
    u = LinearMap.onSup h := by
  ext ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, heq⟩ := mem_sup.mp hx
  suffices (⟨x, hx⟩ : M + N) = ⟨y, le_sup_left (b := N) hy⟩ + ⟨z, le_sup_right (a := M) hz⟩ by
    rw [this, map_add, map_add, onSup_apply_left h, onSup_apply_right h]
    rw [LinearMap.ext_iff] at huf hug
    specialize huf ⟨y, hy⟩
    specialize hug ⟨z, hz⟩
    simp only [Submodule.add_eq_sup, coe_comp, Function.comp_apply, inclusion_apply] at huf hug
    erw [huf, hug]
  simp [← Subtype.coe_inj, heq]

end LinearMap

end onSup

namespace DividedPowers

/- We need `A` to be a ring, until we can prove `dpow_factorsThrough` with semiring
 The better proof using the exponential module should work in the general case -/

variable {A : Type*} [CommRing A]
variable {I : Ideal A} {hI : DividedPowers I} {J : Ideal A} {hJ : DividedPowers J}

-- move to DividedPowers.Basic (after mathlib is updated)

theorem coeff_dpowExp (n : ℕ) (a : A) :
    PowerSeries.coeff A n (hI.dpowExp a) = hI.dpow n a := by
  simp only [dpowExp, PowerSeries.coeff_mk]

theorem constantCoeff_dpowExp {a : A} (ha : a ∈ I) :
    PowerSeries.constantCoeff A (hI.dpowExp a) = 1 := by
  simp only [dpowExp, PowerSeries.constantCoeff_mk, hI.dpow_zero ha]

namespace IdealAdd

open Finset BigOperators Polynomial

/-- Some complicated numerical coefficients for the proof of ideal_add.dpow_comp -/
private def cnik (n i : ℕ) (k : Multiset ℕ) : ℕ :=
  if i = 0 then (k.count i).uniformBell n
  else if i = n then  (k.count i).uniformBell n
  else (k.count i).factorial * (k.count i).uniformBell i * (k.count i).uniformBell (n - i)

/-- The exponential map on the sup of two compatible divided power ideals -/
noncomputable def exp_LinearMap (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    (I + J) →ₗ[A] (ExponentialModule A) := by
  apply LinearMap.onSup (f := hI.exp_LinearMap) (g := hJ.exp_LinearMap)
  intro x hxI hxJ
  simp only [exp_LinearMap_apply]
  rw [← Subtype.coe_inj]
  apply Additive.toMul.injective
  ext n
  exact hIJ x ⟨hxI, hxJ⟩

theorem exp_LinearMap_apply (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    exp_LinearMap hIJ ⟨x + y, Submodule.add_mem_sup hx hy⟩ =
      hI.exp_LinearMap ⟨x, hx⟩ + hJ.exp_LinearMap ⟨y, hy⟩ := by
  rw [exp_LinearMap, LinearMap.onSup_apply]

theorem exp_LinearMap_apply_left (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {x : A} (hx : x ∈ I) :
    exp_LinearMap hIJ ⟨x, Ideal.mem_sup_left hx⟩ = hI.exp_LinearMap ⟨x, hx⟩ := by
  rw [exp_LinearMap, LinearMap.onSup_apply_left _ hx]

theorem exp_LinearMap_apply_right (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {y : A} (hy : y ∈ J) :
    exp_LinearMap hIJ ⟨y, Ideal.mem_sup_right hy⟩ = hJ.exp_LinearMap ⟨y, hy⟩ := by
  rw [exp_LinearMap, LinearMap.onSup_apply_right _ hy]

/-- The divided power function on the sup of two ideals. -/
noncomputable def dpow (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) :=
  Function.extend (fun a ↦ ↑a : (I + J) → A) (fun a ↦ PowerSeries.coeff A n (exp_LinearMap hIJ a)) 0

theorem dpow_def (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) {a : A} (ha : a ∈ I + J) :
    dpow hIJ n a = PowerSeries.coeff A n (exp_LinearMap hIJ ⟨a, ha⟩) :=
  Subtype.val_injective.extend_apply _ _ ⟨a, ha⟩

/-
noncomputable def dpow : ℕ → A → A := fun n =>
  Function.extend (fun ⟨a, b⟩ => (a : A) + (b : A) : I × J → A)
    (fun ⟨a, b⟩ =>
      Finset.sum (range (n + 1)) fun k => hI.dpow k (a : A) * hJ.dpow (n - k) (b : A))
    (Function.const A 0)

/-- Independence on choices for `dpow` -/
theorem dpow_factorsThrough (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) :
    (fun (a, b) => Finset.sum (range (n + 1)) fun k => hI.dpow k (a : A) *
      hJ.dpow (n - k) (b : A)).FactorsThrough (fun ⟨a, b⟩ => (a : A) + (b : A) : I × J → A) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ H
  dsimp only at H ⊢
  -- Needs A to be a ring
  set c := a - a' with hc
  have haa' : a = a' + c := by simp only [hc, add_sub_cancel]
  have hbb' : b' = b + c := by rw [← sub_eq_iff_eq_add'.mpr H, haa']; ring
  have hcI : c ∈ I := sub_mem ha ha'
  have hcJ : c ∈ J := by rw [← sub_eq_iff_eq_add'.mpr hbb']; exact sub_mem hb' hb
  rw [haa', hbb']
  have Ha'c : ((range (n + 1)).sum fun k : ℕ => hI.dpow k (a' + c) * hJ.dpow (n - k) b) =
      (range (n + 1)).sum fun k : ℕ => (range (k + 1)).sum fun l : ℕ =>
        hI.dpow l a' * hJ.dpow (n - k) b * hI.dpow (k - l) c := by
    refine sum_congr rfl (fun k _ ↦ ?_)
    rw [hI.dpow_add' ha' hcI, sum_mul]
    exact sum_congr rfl (fun l _ ↦ by ring)
  have Hbc : ((range (n + 1)).sum fun k : ℕ => hI.dpow k a' * hJ.dpow (n - k) (b + c)) =
      (range (n + 1)).sum fun k : ℕ => (range (n - k + 1)).sum
        fun l : ℕ => hI.dpow k a' * hJ.dpow l b * hJ.dpow (n - k - l) c := by
    refine sum_congr rfl (fun k _ ↦ ?_)
    rw [hJ.dpow_add' hb hcJ, mul_sum]; ring_nf
  rw [Ha'c, sum_sigma', Hbc, sum_sigma']
  set s := (range (n + 1)).sigma fun a : ℕ => range (a + 1) with hs_def
  set i : ∀ x : Σ _ : ℕ, ℕ, x ∈ s → Σ _ : ℕ, ℕ := fun ⟨k, m⟩ _ => ⟨m, n - k⟩ with hi_def
  set t := (range (n + 1)).sigma fun a : ℕ => range (n - a + 1) with ht_def
  set j : ∀ y : Σ _ : ℕ, ℕ, y ∈ t → Σ _ : ℕ, ℕ := fun ⟨k, m⟩ _ => ⟨n - m, k⟩ with hj_def
  rw [sum_bij' i j _ _ _ _]
  · rintro ⟨k, m⟩ h
    apply congr_arg₂ _ rfl
    suffices h : n - m - (n - k) = k - m by
      rw [h]
      apply hIJ
      exact ⟨hcI, hcJ⟩
    rw [Nat.sub_sub, add_comm, ← Nat.sub_sub, Nat.sub_sub_self ?_]
    simp only [hs_def, mem_sigma, mem_range] at h
    exact Nat.le_of_lt_succ h.1
  · rintro ⟨k, m⟩ h
    simp only [hs_def, ht_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h ⊢
    exact ⟨le_trans h.2 h.1, tsub_le_tsub_left h.2 _⟩
  · rintro ⟨k, m⟩ h
    simp only [hs_def, ht_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h ⊢
    apply And.intro (Nat.sub_le _ _)
    rw [Nat.le_sub_iff_add_le] at h ⊢
    rw [add_comm]; exact h.2
    exact le_trans (Nat.le_add_right _ _) h.2
    exact h.1
  · rintro ⟨k, m⟩ h
    simp only [hs_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp only [hj_def, Sigma.mk.inj_iff, heq_eq_eq, and_true]
    exact Nat.sub_sub_self h.1
  · rintro ⟨u, v⟩ h
    simp only [ht_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp only [hi_def, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    exact Nat.sub_sub_self (le_trans h.2 (Nat.sub_le n u)) -/

theorem dpow_eq (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {a b : A} (ha : a ∈ I) (hb : b ∈ J) :
    dpow hIJ n (a + b) = ∑ k ∈ (antidiagonal n), hI.dpow k.1 a * hJ.dpow k.2 b := by
  rw [dpow_def, exp_LinearMap_apply hIJ ha hb, ExponentialModule.coe_add]
  rw [PowerSeries.coeff_mul]
  apply congr_arg₂ _ rfl
  ext ⟨u, v⟩
  simp only [DividedPowers.exp_LinearMap_apply, coe_exp, coeff_dpowExp]

private theorem dpow_eq_of_mem_left' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ I) :
    dpow hIJ n x = hI.dpow n x := by
  rw [dpow_def, exp_LinearMap_apply_left hIJ hx]
  simp only [DividedPowers.exp_LinearMap_apply, coe_exp, coeff_dpowExp]

private theorem dpow_eq_of_mem_right' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ J) :
    dpow hIJ n x = hJ.dpow n x := by
  rw [dpow_def, exp_LinearMap_apply_right hIJ hx]
  simp only [DividedPowers.exp_LinearMap_apply, coe_exp, coeff_dpowExp]

theorem dpow_zero (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {x : A} (hx : x ∈ I + J) :
    dpow hIJ 0 x = 1 := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hIJ ha hb]
  simp only [antidiagonal_zero, Prod.mk_zero_zero, sum_singleton, Prod.fst_zero, Prod.snd_zero]
  rw [hI.dpow_zero ha, hJ.dpow_zero hb, mul_one]

theorem dpow_mul (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {m n : ℕ} {x : A} (hx : x ∈ I + J) :
    dpow hIJ m x * dpow hIJ n x = ((m + n).choose m) * dpow hIJ (m + n) x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp only [dpow_eq hIJ ha hb, sum_mul_sum, ← sum_product']
  have hf : ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      hI.dpow x.1.1 a * hJ.dpow x.1.2 b * (hI.dpow x.2.1 a * hJ.dpow x.2.2 b) =
        (x.1.1 + x.2.1).choose x.1.1 * (x.1.2 + x.2.2).choose x.1.2 *
            hI.dpow (x.1.1 + x.2.1) a * hJ.dpow (x.1.2 + x.2.2) b := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    rw [mul_assoc, ← mul_assoc (hJ.dpow j b), mul_comm (hJ.dpow j b), mul_assoc, hJ.dpow_mul hb,
      ← mul_assoc, hI.dpow_mul ha]
    ring
  rw [sum_congr rfl fun x _ ↦ hf x]
  set s : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := fun x ↦ ⟨x.1.1 + x.2.1, x.1.2 + x.2.2⟩ with hs_def
  have hs : ∀ x ∈ antidiagonal m ×ˢ antidiagonal n, s x ∈ antidiagonal (m + n) := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ h
    simp only [mem_antidiagonal, mem_product] at h ⊢
    rw [add_assoc, ← add_assoc k j l, add_comm k _, add_assoc, h.2, ← add_assoc, h.1]
  rw [← sum_fiberwise_of_maps_to hs]
  have hs' : ∑ y ∈ antidiagonal (m + n),
      ∑ x ∈ ((antidiagonal m ×ˢ antidiagonal n).filter (fun x ↦ s x = y)),
          ((x.1.1 + x.2.1).choose x.1.1) * ((x.1.2 + x.2.2).choose x.1.2) *
            hI.dpow (x.1.1 + x.2.1) a * hJ.dpow (x.1.2 + x.2.2) b =
      ∑ y ∈ antidiagonal (m + n),
        (∑ x ∈ ((antidiagonal m ×ˢ antidiagonal n).filter (fun x ↦ s x = y)),
          ((y.fst.choose x.1.1) * (y.snd.choose x.1.2))) * hI.dpow y.fst a * hJ.dpow y.snd b := by
    apply sum_congr rfl
    rintro ⟨u, v⟩ _
    simp only [Prod.mk.injEq, mem_product, mem_antidiagonal, and_imp, Prod.forall, Nat.cast_sum,
    Nat.cast_mul, sum_mul]
    apply sum_congr rfl
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hx
    simp only [hs_def, mem_product, mem_antidiagonal, and_imp, Prod.forall, mem_filter,
      Prod.mk.injEq] at hx
    rw [hx.2.1, hx.2.2]
  rw [hs', mul_sum]
  apply sum_congr rfl
  rintro ⟨u, v⟩ h
  simp only [mem_antidiagonal] at h
  simp only [Prod.mk.inj_iff]
  rw [← mul_assoc]
  congr
  simp only [hs_def, Prod.mk.injEq]
  --
  rw [Finset.sum_filter, Finset.sum_product]
  rw [← h, Nat.add_choose_eq]
  apply Finset.sum_congr rfl
  intro x hx
  -- x1 + x2 = m, y1 + y2 = n, x1 + y1 = u,  x2 + y2 = v
  -- y1 = u - x1, y2 = v - x2
  rw [Finset.sum_eq_single (u-x.1, v - x.2)]
  · simp only [ite_eq_then, not_and_or, zero_eq_mul]
    apply Or.imp
    all_goals {
      rw [Nat.choose_eq_zero_iff, ← not_le, not_imp_not]
      exact Nat.add_sub_of_le }
  · intro y _ hy'
    simp only [ite_eq_else]
    intro hy''
    apply False.elim (hy' _)
    ext
    · rw [← Nat.add_right_inj (n := x.1), hy''.1, Nat.add_sub_of_le (hy''.1.symm ▸ Nat.le_add_right _ _)]
    · rw [← Nat.add_right_inj (n := x.2), hy''.2, Nat.add_sub_of_le (hy''.2.symm ▸ Nat.le_add_right _ _)]
  · intro hx'
    simp only [ite_eq_else]
    intro hx''
    apply False.elim (hx' _)
    simp only [mem_antidiagonal] at hx ⊢
    rw [← Nat.add_right_inj (n := x.1), ← add_assoc, hx''.1]
    rw [← Nat.add_left_inj (n := x.2), add_assoc, add_comm _ x.2, hx''.2]
    rw [h, add_assoc, add_comm n, ← add_assoc, hx]

theorem dpow_mem (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I + J) :
    dpow hIJ n x ∈ I + J := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hIJ ha hb]
  refine Submodule.sum_mem (I ⊔ J) (fun k hk ↦ ?_)
  simp only [mem_antidiagonal] at hk
  by_cases h : k.1 = 0
  · simp only [h, zero_add] at hk
    exact hk ▸ Submodule.mem_sup_right (J.mul_mem_left _ (hJ.dpow_mem hn hb))
  · exact Submodule.mem_sup_left (I.mul_mem_right _ (hI.dpow_mem h ha))

theorem dpow_smul (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {c x : A} (hx : x ∈ I + J) :
    dpow hIJ n (c * x) = c ^ n * dpow hIJ n x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp_rw [dpow_eq hIJ ha hb]
  simp_rw [mul_add c a b]
  rw [dpow_eq hIJ (I.mul_mem_left c ha) (J.mul_mem_left c hb), mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [mem_range, Nat.lt_succ_iff, mem_antidiagonal] at hk
  rw [hI.dpow_smul ha, hJ.dpow_smul hb, mul_mul_mul_comm, ← pow_add, hk]

theorem dpow_add (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x y : A} (hx : x ∈ I + J) (hy : y ∈ I + J) :
    dpow hIJ n (x + y) = ∑ k ∈ (antidiagonal n), dpow hIJ k.1 x * dpow hIJ k.2 y := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hy
  rw [add_add_add_comm a b a' b']
  rw [dpow_eq hIJ (I.add_mem ha ha') (J.add_mem hb hb')]
  have hf1 (k : ℕ × ℕ) : hI.dpow k.1 (a + a') * hJ.dpow k.2 (b + b') =
      ∑ i ∈ (antidiagonal k.1), ∑ l ∈ (antidiagonal k.2),
        hI.dpow i.1 a * hI.dpow i.2 a' * hJ.dpow l.1 b * hJ.dpow l.2 b' := by
    rw [hI.dpow_add ha ha', hJ.dpow_add hb hb', sum_mul]
    refine sum_congr rfl (fun _ _ ↦ ?_)
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ ↦ by ring)
  have hf2 (k : ℕ × ℕ) : dpow hIJ k.1 (a + b) * dpow hIJ k.2 (a' + b') =
      ∑ i ∈ (antidiagonal k.1), ∑ l ∈ (antidiagonal k.2),
        hI.dpow i.1 a * hI.dpow l.1 a' * hJ.dpow i.2 b * hJ.dpow l.2 b' := by
    rw [dpow_eq hIJ ha hb, dpow_eq hIJ ha' hb', sum_mul]
    refine sum_congr rfl (fun _ _ ↦ ?_)
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ ↦ by ring)
  rw [sum_congr rfl (fun k _ ↦ hf1 k), sum_congr rfl (fun k _ ↦ hf2 k)]
  -- One needs to swap the inner terms in the four-order sum
  simp_rw [← sum_antidiagonalFourth'_eq (f := fun (i, l) ↦ hI.dpow i.1 a * hI.dpow l.1 a' * hJ.dpow i.2 b * hJ.dpow l.2 b')]
  simp_rw [← sum_antidiagonalFourth'_eq (f := fun (i, l) ↦ hI.dpow i.1 a * hI.dpow i.2 a' * hJ.dpow l.1 b * hJ.dpow l.2 b')]
  let i : (ℕ × ℕ) × (ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) := fun (u, v) ↦ ((u.1, v.1), (u.2, v.2))
  have hi (a) (ha : a ∈ antidiagonalFourth' n) : i a ∈ antidiagonalFourth' n := by
    simp only [mem_antidiagonalFourth'] at ha ⊢
    rw [← ha]
    rw [add_assoc, add_add_add_comm, ← add_assoc]
  have hi' (a) : i (i a) = a := rfl
  apply Finset.sum_nbij' i i hi hi (fun a _ ↦ hi' a) (fun a _ ↦ hi' a)
  intro a _
  rw [mul_assoc, mul_mul_mul_comm, ← mul_assoc]

theorem dpow_add' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x y : A} (hx : x ∈ I + J) (hy : y ∈ I + J) :
    dpow hIJ n (x + y) =
      ∑ k ∈ range (n + 1), dpow hIJ k x * dpow hIJ (n - k) y := by
  rw [dpow_add hIJ hx hy]
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Prove the `dpow_comp` axiom for the ideal `I ⊔ J`, assuming agreement on `I ⊓ J` , -/
theorem dpow_comp_aux (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {m n : ℕ} (hn : n ≠ 0) {a b : A} (ha : a ∈ I) (hb : b ∈ J) :
    dpow hIJ m (dpow hIJ n (a + b)) =
      ∑ p ∈ range (m * n + 1),
        (∑ x ∈ ((range (n + 1)).sym m).filter (fun l : Sym ℕ m ↦ ∑ i ∈ range (n + 1), Multiset.count i ↑l * i = p),
          ((∏ i ∈ range (n + 1), cnik n i ↑x) *
            Nat.multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * i) *
            Nat.multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * (n - i)) *
        hI.dpow p a * hJ.dpow (m * n - p) b := by
  rw [dpow_eq hIJ ha hb]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ (f := fun k l ↦ hI.dpow k a * hJ.dpow l b)]
  have L1 (k : Sym ℕ m) (i : ℕ) (hi : i ∈ range (n + 1)) :
      dpow hIJ (Multiset.count i ↑k) (hI.dpow i a * hJ.dpow (n - i) b) = cnik n i ↑k *
        hI.dpow (Multiset.count i ↑k * i) a * hJ.dpow (Multiset.count i ↑k * (n - i)) b := by
    simp only [cnik]
    by_cases hi2 : i = n
    · rw [hi2, Nat.sub_self, if_neg hn, if_pos rfl]
      simp only [hJ.dpow_zero hb, mul_one, mul_zero]
      rw [dpow_eq_of_mem_left' hIJ (hI.dpow_mem hn ha), hI.dpow_comp hn ha]
    · have hi2' : n - i ≠ 0 := by
        intro h; apply hi2
        rw [mem_range, Nat.lt_succ_iff] at hi
        rw [← Nat.sub_add_cancel hi, h, zero_add]
      by_cases hi1 : i = 0
      · rw [hi1, hI.dpow_zero ha, Nat.sub_zero, one_mul, if_pos rfl,
          dpow_eq_of_mem_right' hIJ (hJ.dpow_mem hn hb), hJ.dpow_comp hn hb, mul_zero,
          hI.dpow_zero ha, mul_one]
      -- i ≠ 0  and i ≠ n
      · rw [if_neg hi1, if_neg hi2, mul_comm, dpow_smul hIJ
          (Submodule.mem_sup_left (hI.dpow_mem hi1 ha)), mul_comm, dpow_eq_of_mem_left' hIJ
          (hI.dpow_mem hi1 ha), ← hJ.factorial_mul_dpow_eq_pow (hJ.dpow_mem hi2' hb),
          hI.dpow_comp hi1 ha, hJ.dpow_comp hi2' hb]
        simp only [← mul_assoc]
        apply congr_arg₂ _ _ rfl
        simp only [mul_assoc]
        rw [mul_comm (hI.dpow _ a)]
        simp only [← mul_assoc]
        apply congr_arg₂ _ _ rfl
        simp only [Sym.mem_coe, ge_iff_le, Nat.cast_mul]
        apply congr_arg₂ _ _ rfl
        rw [mul_comm]

  rw [dpow_sum_aux (dpow := dpow hIJ)]
  · set φ := fun (k : Sym ℕ m) ↦ ∑ i ∈ (range (n + 1)), Multiset.count i ↑k * i with hφ_def
    suffices hφ : ∀ k ∈ (range (n + 1)).sym m, φ k ∈ range (m * n + 1) by
      rw [← sum_fiberwise_of_maps_to hφ _]
      suffices L4 : ∀ (p : ℕ) (_ : p ∈ range (m * n + 1)),
          (∑ x ∈ (filter (fun x ↦ φ x = p) ((range (n + 1)).sym m)),
              ∏ i ∈ (range (n + 1)),
                dpow hIJ (Multiset.count i ↑x) (hI.dpow i a * hJ.dpow (n - i) b)) =
            ∑ k ∈ ((range (n + 1)).sym m).filter (fun x ↦ φ x = p),
              (∏ i ∈ (range (n + 1)), ↑(cnik n i ↑k)) *
                  ↑(Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑k * i) *
                  ↑(Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑k * (n - i)) *
              hI.dpow p a * hJ.dpow (m * n - p) b by
          simp only [Nat.succ_eq_add_one, sum_congr rfl L4, Nat.cast_sum, Nat.cast_mul,
            Nat.cast_prod, sum_mul]
      intro p _
      apply sum_congr rfl
      intro k hk
      rw [mem_filter] at hk
      rw [prod_congr rfl (L1 k), prod_mul_distrib, prod_mul_distrib,
        hI.prod_dpow_self _ ha, hJ.prod_dpow_self _ hb]
      simp only [mul_assoc]; apply congr_arg₂ _ rfl
      apply congr_arg₂ _ rfl
      rw [sum_range_sym_mul_compl hk.1]
      simp only [← mul_assoc]
      simp only [mem_sym_iff, mem_range, hφ_def] at hk
      rw [hk.2]
      apply congr_arg₂ _ _ rfl
      rw [mul_comm]
    -- hφ
    intro k hk
    simp only [Sym.mem_coe, mem_range, Nat.lt_succ_iff, range_sym_weighted_sum_le hk]
  . -- dpow_zero
    intro x hx
    exact dpow_zero hIJ hx
  . -- dpow_add
    intro n x y
    exact dpow_add hIJ
  · -- dpow_eval_zero
    intro n hn
    rw [dpow_eq_of_mem_left' hIJ I.zero_mem, dpow_eval_zero hI hn]
  · intro i _
    by_cases hi0 : i = 0
    · apply Submodule.mem_sup_right (J.mul_mem_left _ (hJ.dpow_mem ?_ hb))
      rw [hi0, tsub_zero]; exact hn
    · exact Submodule.mem_sup_left (I.mul_mem_right _ (hI.dpow_mem hi0 ha))

theorem dpow_comp_coeffs {m n p : ℕ} (hn : n ≠ 0) (hp : p ≤ m * n) :
  Nat.uniformBell m n =
    ∑ x ∈ ((range (n + 1)).sym m).filter (fun l : Sym ℕ m ↦ ∑ i ∈ range (n + 1), Multiset.count i ↑l * i = p),
        (∏ i ∈ (range (n + 1)), cnik n i ↑x) *
          ((Nat.multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * i) *
            Nat.multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * (n - i)) := by
  classical
  rw [← mul_left_inj' (pos_iff_ne_zero.mp (Nat.choose_pos hp))]
  apply @Nat.cast_injective ℚ
  simp only [Sym.mem_coe, mem_sym_iff, mem_range, ge_iff_le,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, Nat.cast_eq_zero]
  conv_lhs => rw [← Polynomial.coeff_X_add_one_pow ℚ (m * n) p]
  let A := ℚ[X]
  let I : Ideal A := ⊤
  let hI : DividedPowers I := RatAlgebra.dividedPowers ⊤
  let hII : ∀ {n : ℕ}, ∀ a ∈ I ⊓ I, hI.dpow n a = hI.dpow n a := fun _ _ => rfl
  let h1 : (1 : A) ∈ I := Submodule.mem_top
  let hX : X ∈ I := Submodule.mem_top
  rw [← hI.factorial_mul_dpow_eq_pow Submodule.mem_top, ← Polynomial.coeff_C_mul,
    ← mul_assoc, mul_comm (C ((Nat.uniformBell m n) : ℚ)), mul_assoc, C_eq_natCast,
    ← hI.dpow_comp hn Submodule.mem_top, ← dpow_eq_of_mem_left' hII Submodule.mem_top,
    ← dpow_eq_of_mem_left' hII Submodule.mem_top, dpow_comp_aux hII hn hX h1,
    ← C_eq_natCast, mul_sum, finset_sum_coeff]
  simp only [hI, RatAlgebra.dpow_eq_inv_fact_smul _ _ Submodule.mem_top, map_natCast,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, Ring.inverse_eq_inv', Algebra.mul_smul_comm, one_pow,
    mul_one, coeff_smul, coeff_natCast_mul, smul_eq_mul]
  simp only [← Nat.cast_prod, ← Nat.cast_mul, ← Nat.cast_sum]
  rw [sum_eq_single p]
  · conv_lhs =>
      rw [coeff_natCast_mul, coeff_X_pow, if_pos, mul_one, ← mul_assoc, mul_comm]
      simp only [mul_assoc]
      rw [mul_comm]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, sum_mul]
    apply sum_congr rfl
    intro x _
    simp only [mul_assoc]
    congr
    ring_nf
    simp only [mul_assoc]
    rw [inv_mul_eq_iff_eq_mul₀, inv_mul_eq_iff_eq_mul₀, ← Nat.choose_mul_factorial_mul_factorial hp]
    simp only [Nat.cast_mul]
    ring
    all_goals
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero _
  · intro b _ hb
    rw [coeff_natCast_mul, coeff_X_pow, if_neg hb.symm]
    simp only [mul_zero]
  · intro hp'
    simp only [mem_range, Nat.lt_succ_iff] at hp'
    contradiction

theorem dpow_comp (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {m n : ℕ} {x : A}
    (hn : n ≠ 0) (hx : x ∈ I + J) :
    dpow hIJ m (dpow hIJ n x) = ↑(Nat.uniformBell m n) * dpow hIJ (m * n) x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_comp_aux hIJ hn ha hb,
    dpow_add' hIJ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [dpow_eq_of_mem_left' hIJ ha, dpow_eq_of_mem_right' hIJ hb]
  simp only [mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  -- it remains to check coefficients
  rw [dpow_comp_coeffs hn (Nat.lt_succ_iff.mp (mem_range.mp hp))]

theorem dpow_null (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∉ I + J) :
    dpow hIJ n x = 0 := by
  simp only [dpow]
  -- simp only [dpow, Function.const_zero]
  rw [Function.extend_apply', Pi.zero_apply]
  rintro ⟨a, rfl⟩
  exact hx a.prop

theorem dpow_one (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {x : A} (hx : x ∈ I + J) :
    dpow hIJ 1 x = x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hIJ ha hb]
  have : antidiagonal 1 = {⟨0, 1⟩, ⟨1, 0⟩} := rfl
  simp [this, hI.dpow_one ha, hJ.dpow_one hb, hI.dpow_zero ha, hJ.dpow_zero hb, add_comm]

/-- The divided power structure on the ideal `I + J`, given that `hI` and `hJ` agree on `I ⊓ J`. -/
noncomputable def dividedPowers
    (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    DividedPowers (I + J) where
  dpow           := dpow hIJ
  dpow_null      := dpow_null hIJ
  dpow_zero      := dpow_zero hIJ
  dpow_one       := dpow_one hIJ
  dpow_mem hn hx := dpow_mem hIJ hn hx
  dpow_add       := dpow_add hIJ
  dpow_smul      := dpow_smul hIJ
  dpow_mul       := dpow_mul hIJ
  dpow_comp      := dpow_comp hIJ

theorem dpow_unique (hsup : DividedPowers (I + J))
    (hI' : ∀ {n : ℕ}, ∀ a ∈ I, hI.dpow n a = hsup.dpow n a)
    (hJ' : ∀ {n : ℕ}, ∀ b ∈ J, hJ.dpow n b = hsup.dpow n b) :
    let hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a := fun n ha => by
      rw [Submodule.mem_inf] at ha; rw [hI' _ ha.1, hJ' _ ha.2]
    hsup = dividedPowers hIJ := by
  intro hIJ
  refine hsup.eq_of_eq_on_ideal _ (fun n x hx ↦ ?_)
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp only [hsup.dpow_add (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb),
    IdealAdd.dividedPowers, dpow_eq hIJ ha hb]
  exact sum_congr rfl (fun k _ ↦ congr_arg₂ (· * ·) (hI' a ha).symm (hJ' b hb).symm)

lemma isDPMorphism_left (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    hI.IsDPMorphism (IdealAdd.dividedPowers hIJ) (RingHom.id A):=
  ⟨by simp only [Ideal.map_id]; exact le_sup_left, fun _ ↦ dpow_eq_of_mem_left' hIJ⟩

lemma isDPMorphism_right (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    hJ.IsDPMorphism (IdealAdd.dividedPowers hIJ) (RingHom.id A) :=
  ⟨by simp only [Ideal.map_id]; exact le_sup_right, fun _ ↦ dpow_eq_of_mem_right' hIJ⟩

theorem dpow_eq_of_mem_left (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ I) :
      (IdealAdd.dividedPowers hIJ).dpow n x = hI.dpow n x :=
  dpow_eq_of_mem_left' hIJ hx

theorem dpow_eq_of_mem_right (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ J) :
    (IdealAdd.dividedPowers hIJ).dpow n x = hJ.dpow n x :=
  dpow_eq_of_mem_right' hIJ hx

end IdealAdd

end DividedPowers
