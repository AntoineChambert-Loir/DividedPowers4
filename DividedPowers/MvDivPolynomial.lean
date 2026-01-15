/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib
import Mathlib.Data.Finsupp.Multiset
import DividedPowers.DPAlgebra.Init

/- import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finsupp.SMul -/
/-!
# Divided polynomials
-/

variable {ι R : Type*}

/-- As a type, divided polynomials are just finitely supported functions. -/
def MvDivPolynomial (ι R : Type*) [Zero R] : Type _ := (ι →₀ ℕ) →₀ R


namespace MvDivPolynomial

instance decidableEqMvDivPolynomial [Zero R] [DecidableEq ι] [DecidableEq R] :
    DecidableEq (MvDivPolynomial ι R) :=
  Finsupp.instDecidableEq


instance zero [Zero R] : Zero (MvDivPolynomial ι R) :=
  inferInstanceAs <| Zero <| (ι →₀ ℕ) →₀ R

instance nontrivial [Zero R] [Nontrivial R] : Nontrivial (MvDivPolynomial ι R) :=
  inferInstanceAs <| Nontrivial <| (ι →₀ ℕ) →₀ R

instance unique [Zero R] [Subsingleton R] : Unique (MvDivPolynomial ι R) :=
  inferInstanceAs <| Unique <| (ι →₀ ℕ) →₀ R

noncomputable instance addCommMonoid [AddCommMonoid R] :
    AddCommMonoid (MvDivPolynomial ι R) :=
  inferInstanceAs <| AddCommMonoid ((ι →₀ ℕ) →₀ R)

instance instIsCancelAdd [AddCommMonoid R] [IsCancelAdd R] : IsCancelAdd (MvDivPolynomial ι R) :=
  inferInstanceAs <| IsCancelAdd <| (ι →₀ ℕ) →₀ R

instance instCoeFun [Zero R] : CoeFun (MvDivPolynomial ι R) fun _ ↦ (ι →₀ ℕ) → R :=
  inferInstanceAs <| CoeFun ((ι →₀ ℕ) →₀ R) fun _ ↦ (ι →₀ ℕ) → R

instance instFunLike [Zero R] : FunLike (MvDivPolynomial ι R) (ι →₀ ℕ) R :=
  ⟨fun p n ↦ p n, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

def coeff [Zero R] (n : ι →₀ ℕ) (p : MvDivPolynomial ι R) : R := p n

/-- `MvDivPolynomial.monomial` is the divised monomial. -/
noncomputable def monomial [Zero R] (n : ι →₀ ℕ) (r : R) :
    MvDivPolynomial ι R :=
  Finsupp.single n r

noncomputable instance one [Zero R] [One R] : One (MvDivPolynomial ι R) where
  one := Finsupp.single 0 1

lemma one_def [Zero R] [One R] : (1 : MvDivPolynomial ι R) = Finsupp.single 0 1 := rfl

section Semiring

variable [Semiring R]

noncomputable instance module : Module R (MvDivPolynomial ι R) :=
  inferInstanceAs <| Module R ((ι →₀ ℕ) →₀ R)

def lcoeff (n : ι →₀ ℕ) : MvDivPolynomial ι R →ₗ[R] R where
  toFun p := p n
  map_add' p q := Finsupp.add_apply p q n
  map_smul' r p := Finsupp.smul_apply r p n

/- Writing `X i` for `monomial (Finsupp.single i 1)`,
then `monomial n 1` has to be thought as `∏  (X i) ^ (n i) / (n i)!`.
Consequently, `monomial m 1 * monomial n 1 = monomial (m + n) ?
with ? = `∏ Nat.choose (m i + n i) n i` -/
@[irreducible] noncomputable
def mul' (p q : MvDivPolynomial ι R) : MvDivPolynomial ι R :=
  p.sum fun m r ↦ q.sum fun n s ↦ (m.prod fun i a ↦ Nat.choose  (a + n i) a) • Finsupp.single (m + n) (r * s)

noncomputable instance instMul : Mul (MvDivPolynomial ι R) where
    mul := mul'

lemma mul_def (p q : MvDivPolynomial ι R) :
    p * q = p.sum fun m r ↦ q.sum fun n s ↦
      (m.prod fun i a ↦ Nat.choose (a + n i) a) • Finsupp.single (m + n) (r * s) := by
  with_unfolding_all rfl

theorem monomial_mul_monomial (m n : ι →₀ ℕ) (r s : R) :
    monomial m r * monomial n s =
      (m.prod fun i a ↦ Nat.choose (a + n i) a) • monomial (m + n) (r * s) := by
  simp [mul_def, monomial]

noncomputable instance semiring : Semiring (MvDivPolynomial ι R) where
  zero_mul := by simp [mul_def]
  mul_zero := by simp [mul_def]
  one_mul := by simp only [one_def, mul_def, Finsupp.single_mul]; simp [← Finsupp.single_mul]
  mul_one := by simp only [one_def, mul_def, Finsupp.single_mul]; simp [← Finsupp.single_mul]
  left_distrib := by classical simp [mul_def]; simp [MvDivPolynomial, Finsupp.sum_add_index, mul_add]
  right_distrib := by classical simp [mul_def]; simp [MvDivPolynomial, Finsupp.sum_add_index, add_mul]
  mul_assoc p q r := by
    simp [mul_def]
    simp [MvDivPolynomial, Finsupp.sum_sum_index, mul_add, add_mul,
      Finsupp.sum_smul_index']
    simp [← Finsupp.single_mul, Finsupp.sum_single_index]
    apply Finsupp.sum_congr
    intro u _
    apply Finsupp.sum_congr
    intro v _
    apply Finsupp.sum_congr
    intro w _
    simp only [← add_assoc, ← mul_assoc]
    congr 3
    simp only [mul_assoc]
    simp only [← Nat.cast_comm]
    simp only [← mul_assoc]
    norm_cast
    congr 2
    rw [Finsupp.prod_of_support_subset (s := (u + v + w).support) _ (Finsupp.support_mono le_self_add) _ (by simp)]
    rw [Finsupp.prod_of_support_subset (s := (u + v + w).support) _
      (Finsupp.support_mono (by simp only [add_assoc, le_add_iff_nonneg_right, zero_le])) _ (by simp)]
    rw [Finsupp.prod_of_support_subset (s := (u + v + w).support) _
      (Finsupp.support_mono (by simp only [add_assoc, le_add_iff_nonneg_right, zero_le])) _ (by simp)]
    rw [Finsupp.prod_of_support_subset (s := (u + v + w).support) _
      (Finsupp.support_mono ((CanonicallyOrderedAdd.le_add_self _ _).trans le_self_add)) _ (by simp)]
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Finsupp.coe_add, Pi.add_apply, Nat.choose_mul (Nat.le_add_right _ _),
      add_tsub_cancel_left, add_assoc]

end Semiring

noncomputable instance commSemiring [CommSemiring R] :
    CommSemiring (MvDivPolynomial ι R) where
  mul_comm p q := by
    simp [mul_def, Finsupp.sum, mul_comm, p.support.sum_comm]
    congr
    ext m n
    congr
    ext u v
    simp [← Finsupp.single_mul, add_comm u]
    congr 3
    rw [Finsupp.prod_of_support_subset (s := (u + m).support) _ (Finsupp.support_mono (by simp)) _ (by simp)]
    rw [Finsupp.prod_of_support_subset (s := (u + m).support) _ (Finsupp.support_mono (by simp)) _ (by simp)]
    congr
    ext i
    rw [add_comm (u i), Nat.choose_symm_add]

section AddCommGroup

variable [AddCommGroup R]

noncomputable instance addCommGroup :
    AddCommGroup (MvDivPolynomial ι R) :=
  inferInstanceAs <| AddCommGroup ((ι →₀ ℕ) →₀ R)

@[simp]
lemma neg_apply (n : ι →₀ ℕ) (p : MvDivPolynomial ι R) :
    (-p) n = -p n := rfl

@[simp]
lemma coeff_neg (n : ι →₀ ℕ) (p : MvDivPolynomial ι R) :
    (-p).coeff n = - p.coeff n := rfl

@[simp]
lemma neg_monomial (n : ι →₀ ℕ) (r : R) :
    - monomial n r = monomial n (-r) :=
  Finsupp.ext (fun m ↦ by simp [monomial, Finsupp.single, Pi.single_neg])

end AddCommGroup

noncomputable instance ring [Ring R] :
    Ring (MvDivPolynomial ι R) where

noncomputable instance commRing [CommRing R] :
    CommRing (MvDivPolynomial ι R) where

noncomputable instance algebra [CommSemiring R] :
    Algebra R (MvDivPolynomial ι R) where
  algebraMap :=
  { toFun r := monomial 0 r
    map_zero' := by simp [monomial]
    map_one' := by simp [monomial, one_def]
    map_mul' r s := by simp [monomial_mul_monomial]
    map_add' r s := by simp [monomial] }
  commutes' r p := by
    simp; sorry
  smul_def' r p := by
    simp
    sorry

section DividedPowerAlgebra

/- Tentative

open Module

variable [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {ι : Type*} (b : Module.Basis ι R M)

example [DecidableEq ι] (n : ℕ) : Sym ι n → ι →₀ ℕ := fun k ↦
  k.val.toFinsupp

def morphism : DividedPowerAlgebra R M →ₐ[R] MvDivPolynomial ι R := by
  classical
  apply DividedPowerAlgebra.lift' (f := fun nm ↦
    ∑ k : Sym (ι →₀ ℕ) nm.1, monomial k.val.toFinsupp (∏ i ∈ k,  fun i e ↦ b.coord i nm.2 ^ e)
  /- m = ∑ (b.coord i m) • b i
    f (n, m) = (∑ (b.coord i m) • b i) ^ n / n!
      = ∑ k ∈ ι.sym n ⟨multinomial coeff⟩ * ∏ (b.coord e m) ^ (k e) • ∏ (b e) ^ (k e) / n!
      = ∑ k ∈ ι.sym n ⟨multinomial coeff⟩ * ∏ (b.coord e m) ^ (k e) • ∏ ((b e) ^ (k e) / (k e)! ) * ∏ (k e)! / n!
    ⟨multinomial coeff⟩ = n! / ∏ (k e)!

    f(n, m) = ∑ k ∈ ι.sym n, monomial k (∏ b.coord e m ^ (k e))
    -/

  sorry -/

end DividedPowerAlgebra

end MvDivPolynomial
