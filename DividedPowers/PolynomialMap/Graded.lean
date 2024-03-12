import DividedPowers.PolynomialMap.Coeff
import Mathlib.RingTheory.TensorProduct
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic
import DividedPowers.ForMathlib.TensorProductFinsupp

open TensorProduct LinearMap

open scoped TensorProduct

section

variable {R : Type _} [CommRing R]
  {S : Type _} [CommRing S] [Algebra R S]
  {M : Type _} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {N : Type _} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  {P : Type _} [AddCommGroup P] [Module R P]
  {Q : Type _} [AddCommGroup Q] [Module R Q]

section rTensor

/-- If `f` is `S`-linear, then `TensorProduct.map (f.restrictScalars R) g` is `S`-linear -/
def TensorProduct.map_isLinearMap_of_left (f : M →ₗ[S] N) (g : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (f.restrictScalars R) g) where
  map_add := fun x y => by rw [map_add]
  map_smul := fun c x => by
    induction x using TensorProduct.induction_on with
    | zero =>
        simp only [smul_zero, map_zero]
    | tmul x y =>
        simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul]
        simp only [coe_restrictScalars, map_smul]
    | add x y hx hy =>
        simp only [smul_add, map_add, hx, hy]

lemma TensorProduct.rTensor_smul' (f : M →ₗ[S] N) (s : S) (t : M ⊗[R] P) :
    rTensor P (f.restrictScalars R) (s • t) = s • (rTensor P (f.restrictScalars R) t) := by
  have : rTensor P (f.restrictScalars R) = (IsLinearMap.mk' _ (TensorProduct.map_isLinearMap_of_left f LinearMap.id)).restrictScalars R := rfl
  rw [this]
  simp only [coe_restrictScalars, map_smul, IsLinearMap.mk'_apply]

/-
/-- If `f` is `S`-linear, then `TensorProduct.map (f.restrictScalars R) g` is `S`-linear -/
noncomputable def TensorProduct.map' (f : M →ₗ[S] N) (g : P →ₗ[R] Q) :
    M ⊗[R] P →ₗ[S] N ⊗[R] Q :=
  IsLinearMap.mk' _ (TensorProduct.map_isLinearMap_of_left f g)

lemma TensorProduct.map'_smul (f : M →ₗ[S] N) (g : P →ₗ[R] Q)
    (s : S) (t : M ⊗[R] P) :
  TensorProduct.map' f g (s • t) = s • (TensorProduct.map' f g t) := by
  rw [map_smul]

lemma TensorProduct.map'_rid_eq (f : M →ₗ[S] N)  :
    (TensorProduct.map' f (LinearMap.id)).restrictScalars R =
      rTensor P (f.restrictScalars R) := rfl

lemma TensorProduct.map'_rid_apply
    (f : M →ₗ[S] N) (t : M ⊗[R] P) :
    TensorProduct.map' f (LinearMap.id) (t) =
      rTensor P (f.restrictScalars R) (t) := rfl
-/

end rTensor

section TensorProduct

open LinearMap Function TensorProduct

universe u v w

variable {R : Type u} {M N : Type _} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem TensorProduct.is_finsupp_sum_tmul {R S : Type _}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Module R M]
    (m : S ⊗[R] M) :
    ∃ r : M →₀ S, m = r.sum fun x a => a ⊗ₜ[R] x := by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · use 0; simp only [Finsupp.sum_zero_index]
  · use Finsupp.single m r
    simp only [Finsupp.sum_single_index, TensorProduct.zero_tmul]
  · obtain ⟨rx, rfl⟩ := hx
    obtain ⟨ry, rfl⟩ := hy
    use rx + ry
    rw [Finsupp.sum_add_index']
    · intro a; simp only [TensorProduct.zero_tmul]
    · intro m r₁ r₂; rw [TensorProduct.add_tmul]
#align tensor_product.is_finsupp_sum_tmul TensorProduct.is_finsupp_sum_tmul

theorem TensorProduct.is_finsupp_sum_tmul' {R S : Type _}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Module R M]
    (t : S ⊗[R] M) :
  ∃ (n : ℕ) (m : ℕ → M) (r : ℕ → S),
    t = (Finset.range n).sum fun x => (r x) ⊗ₜ[R] (m x) := by
  induction' t using TensorProduct.induction_on with r m x y hx hy
  · use 0; use const ℕ 0; use const ℕ 0
    simp only [Finset.range_zero, Finset.sum_empty]

  · use 1; use const ℕ m; use const ℕ r;
    simp only [Finset.range_one, Finset.sum_singleton, const_apply]

  · obtain ⟨n1, m1, r1, h1⟩ := hx
    obtain ⟨n2, m2, r2, h2⟩ := hy
    use n1 + n2
    use fun x => if x < n1 then m1 x else m2 (x - n1)
    use fun x => if x < n1 then r1 x else r2 (x - n1)
    rw [Finset.sum_range_add]
    apply congr_arg₂
    . conv_lhs => rw [h1]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx
      simp only [if_pos hx]
    . conv_lhs => rw [h2]
      apply Finset.sum_congr rfl
      intro x _
      dsimp
      suffices ¬ (n1 + x  < n1) by
        simp only [if_neg this]
        simp only [add_tsub_cancel_left]
      simp only [not_lt, Nat.le_add_right]

example (α : Type _) [Fintype α] : Fintype (ULift α) := by exact ULift.fintype α

example (α : Type _) : α ≃ ULift α := by exact Equiv.ulift.symm

theorem ULift.fintype_sum (α : Type _) [Fintype α] (f : α → ℕ) :
  Finset.univ.sum f =
    Finset.univ.sum (fun (x : ULift α) ↦ f (Equiv.ulift x)) := by
  rw [Finset.sum_congr_equiv (Equiv.ulift)]
  simp only [Finset.map_univ_equiv, Equiv.ulift_apply, Function.comp_apply]
  rfl

theorem TensorProduct.is_finsupp_sum_tmul'' {R S : Type u}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Module R M]
    (t : S ⊗[R] M) :
  ∃ (ι : Type u) (hι : Fintype ι) (r : ι → S) (m : ι → M),
    t = Finset.univ.sum (fun i => (r i) ⊗ₜ[R] (m i)) := by
  obtain ⟨n, m, r, h⟩ := TensorProduct.is_finsupp_sum_tmul' t
  rw [h, Finset.sum_range]
  use ULift (Fin n)
  use ULift.fintype (Fin n)
  use fun i ↦ r ↑(Equiv.ulift i)
  use fun i ↦ m ↑(Equiv.ulift i)
  simp only [Equiv.ulift_apply, Finset.sum_congr_equiv (Equiv.ulift), Finset.map_univ_equiv, Function.comp_apply]
  apply Finset.sum_congr rfl (fun x _ ↦ rfl)

def ULift.up_embedding {α : Type _} : α ↪ ULift α where
  toFun := ULift.up
  inj' := ULift.up_injective

theorem ULift.finset_sum (α : Type _) (s : Finset α) (f : α → ℕ) :
  s.sum f = Finset.sum (s.map ULift.up_embedding)
    (fun (x : ULift α) ↦ f x.down) := by
  rw [Finset.sum_bij' (fun a _ ↦ ULift.up a) (fun a _ ↦ a.down)]
  · intro a ha
    simp only [Finset.mem_map]
    exact ⟨a, ha, rfl⟩
  . intro a ha
    simp only [Finset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hb
  . intro a _ ; rfl
  . intro a _ ; rfl
  . intro a _ ; simp only [Finset.mem_map]


example (f g : ι →₀ ℕ) (i : ι) : (f + g) i = f i + g i := by
  simp only [Finsupp.coe_add, Pi.add_apply]

example (s : Finset ι) (f : ι → (ℕ →₀ ℕ)) (n : ℕ) :
  s.sum f n = s.sum (fun i ↦ f i n) := by
  exact Finset.sum_apply' n

noncomputable example {ι κ : Type _} [Fintype ι] [Fintype κ] [DecidableEq ι][DecidableEq κ] (e : ι ≃ κ)
    (k : κ →₀ ℕ) : ι →₀ ℕ := by
  apply Finsupp.comapDomain e k
  apply Set.injOn_of_injective e.injective

lemma _root_.MvPolynomial.prod_monomial_eq {α : Type _} [DecidableEq α]
    (s : Finset α) (k : α → (ι →₀ ℕ)) (c : α → R) :
  s.prod (fun a ↦ MvPolynomial.monomial (k a) (c a))
  = MvPolynomial.monomial (s.sum k) (s.prod c) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, MvPolynomial.monomial_zero',
      _root_.map_one]
  | insert ha hs =>
      rw [Finset.prod_insert ha, hs, MvPolynomial.monomial_mul,
        Finset.sum_insert ha, Finset.prod_insert ha]

lemma _root_.MvPolynomial.monomial_one_eq {α : Type _} [DecidableEq α]
    (c : α →₀ ℕ) :
    MvPolynomial.monomial c (1 : R) = c.prod fun a n => MvPolynomial.X a ^ n := by
    rw [MvPolynomial.monomial_eq, _root_.map_one, one_mul]

lemma _root_.Finsupp.eq_sum_single_apply {α : Type _} [DecidableEq α] [Fintype α]
    (c : α →₀ ℕ) :
  Finset.sum Finset.univ (fun a => Finsupp.single a (c a)) = c := by
  ext a
  rw [Finset.sum_apply', Finset.sum_eq_single a]
  . simp only [Finsupp.single_eq_same]
  . intro b _ hb
    simp only [Finsupp.single_eq_of_ne hb]
  . exact fun h ↦ False.elim (h (Finset.mem_univ a))

end TensorProduct

end

section Homogeneous

namespace PolynomialMap



universe u v w

variable {R : Type u}[CommRing R]
    {M : Type _} [AddCommGroup M] [Module R M]
    {N : Type _}  [AddCommGroup N] [Module R N]

/-- (Roby, Prop. I.1)
  A PolynomialMap is Homogeneous of degree p
  iff all its nonzero coefficients have degree p -/
theorem isHomogeneousOfDegree_iff'
    (p : ℕ) (f : PolynomialMap R M N) :
  f.IsHomogeneousOfDegree p ↔
    ∀ {ι : Type u} [DecidableEq ι] [Fintype ι]
      (m : ι → M) (k : ι →₀ ℕ) (_ : coeff m f k ≠ 0),
      (Finset.univ.sum k) = p := by
  classical
  constructor
  · -- difficult direction
    intro hf
    intro ι _ _ m k
    rw [not_imp_comm]
    by_cases hι : Nonempty ι
    . intro hk
      suffices ∀ (s : Finset (ι →₀ ℕ)), ∃ (l : ι →₀ ℕ),
        ∀ a ∈ s, ∀ b ∈ s,
        (Finset.univ.sum a) • l + a = p • l + b →
        (Finset.univ.sum a = p ∧ a = b) by
        obtain ⟨l, hl⟩ := this (insert k (coeff m f).support)
        specialize hf (MvPolynomial ι R) (MvPolynomial.monomial l 1)
          (Finset.sum Finset.univ fun i => MvPolynomial.X i ⊗ₜ[R] m i)
        simp only [Finset.smul_sum, TensorProduct.smul_tmul', image_eq_coeff_sum] at hf
        simp only [Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf
        -- write the summands as monomials
        simp_rw [smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          MvPolynomial.monomial_pow, one_pow] at hf
        suffices h : ∀ (c : ι →₀ ℕ),
          MvPolynomial.monomial c (1 : R) = Finset.univ.prod (fun i ↦ MvPolynomial.X i ^ c i) by
          simp_rw [← h] at hf
          simp_rw [MvPolynomial.monomial_mul, mul_one] at hf

          let hf' := (zooEquiv ι R N).symm.congr_arg hf
          rw [DFunLike.ext_iff] at hf'
          simp only [_root_.map_finsupp_sum] at hf'
          simp only [Finsupp.sum_apply] at hf'
          simp only [zooEquiv_symm_apply_tmul] at hf'
          simp only [MvPolynomial.coeff_monomial] at hf'
          simp only [ite_smul, one_smul, zero_smul] at hf'
        /- For all x,
          hf' proves the equality of the sums for y in the support of (coeff m f):
          * LHS : if x = y + deg (y) • l,  coeff m f y
          * RHS : if x = y + p • l, coeff m f y

          Take x = k + p • l
          RHS : only term is given by y = k, gives coeff m f k
          LHS ? : y + deg (y) • l = k + p • l
            for deg(l) large enough,
            this will imply y = k
          -/
          specialize hf' (p • l + k)
          rw [eq_comm] at hf'
          rw [Finsupp.sum, Finset.sum_eq_single k, if_pos rfl] at hf'
          rw [hf']
          rw [Finsupp.sum, Finset.sum_eq_zero]
          . intro x hx
            rw [if_neg]
            intro hx'
            apply hk
            -- This is where the condition on l should be introduced
            -- It will suffice to take l of large degree

            let hl' := hl x (Finset.mem_insert_of_mem hx)
              k (Finset.mem_insert_self _ _) hx'
            rw [← hl'.2, hl'.1]

          · intro y _ hy
            rw [if_neg]
            intro hy'
            apply hy
            exact add_left_cancel hy'
          · rw [if_pos rfl]
            simp only [Finsupp.mem_support_iff, ne_eq, not_not, imp_self]

        . intro c
          simp only [MvPolynomial.monomial_eq, _root_.map_one, Finsupp.prod_pow, one_mul]


      . -- The choice of l
        intro s
        suffices h' : ∃ N, ∀ (l : ι →₀ ℕ), N ≤ Finset.univ.sum l →
            ∀ a ∈ s, ∀ b ∈ s,
              Finset.univ.sum a • l + a = p • l + b →
              Finset.univ.sum a = p ∧ a = b by
          obtain ⟨N, hN⟩ := h'
          obtain ⟨i : ι⟩ := hι
          use Finsupp.single i N
          apply hN
          simp only [Finsupp.univ_sum_single_apply, le_refl]

        use (s.sup (fun a ↦ Finset.univ.sum a)).succ
        intro l hl a ha b hb h
        suffices h'' : Finset.univ.sum a = p by
          refine' ⟨h'', _⟩
          rw [h''] at h
          apply add_left_cancel h
        let h' := congr_arg (fun (x : ι →₀ ℕ) ↦ Finset.univ.sum x) h
        dsimp at h'
        change Finset.univ.sum (fun i ↦ Finset.univ.sum a • (l i) + a i)
          = Finset.univ.sum (fun i ↦ p • (l i) + b i) at h'
        simp only [Finset.sum_add_distrib] at h'
        simp only [Finset.sum_nsmul] at h'
        simp only [smul_eq_mul] at h'

        rw [Nat.succ_le_iff] at hl
        let h'' := congr_arg (fun x ↦ x % (Finset.univ.sum l)) h'
        dsimp at h''
        rw [Nat.mul_add_mod_of_lt (lt_of_le_of_lt (Finset.le_sup ha) hl)] at h''
        rw [Nat.mul_add_mod_of_lt (lt_of_le_of_lt (Finset.le_sup hb) hl)] at h''
        rw [h'', add_right_cancel_iff] at h'
        rw [mul_eq_mul_right_iff] at h'
        cases h' with
        | inl h' => rw [h'', h']
        | inr h' =>
            exfalso
            rw [h'] at hl
            exact Nat.not_lt_zero _ hl
    . -- when ι is Empty
      simp only [not_nonempty_iff] at hι
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      intro hp
      specialize hf (MvPolynomial ι R) (0)
        (Finset.sum Finset.univ fun i => MvPolynomial.X i ⊗ₜ[R] m i)
      simp only [zero_pow (ne_comm.mp hp), zero_smul] at hf
      simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        zooEquiv_symm_apply, AddEquivClass.map_eq_zero_iff]
      suffices hf : generize R N m f = 0 by
        simp only [hf, map_zero]
      . simp only [generize, Finset.univ_eq_empty, Finset.sum_empty,
          coe_mk, AddHom.coe_mk]
        exact hf
  · -- Trivial direction
    intro hf S _ _ c m
    obtain ⟨n, _, r, m, rfl⟩ := TensorProduct.is_finsupp_sum_tmul'' m

    rw [Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul']
    have : ∀ x, c • r ↑x = (c • r) ↑x := by intro x ; rfl
    simp only [this]
    simp only [image_eq_coeff_sum, Finsupp.smul_sum]
    apply Finsupp.sum_congr
    intro k _
    specialize hf m k
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    simp_rw [← smul_eq_mul, ← TensorProduct.smul_tmul']
    by_cases hkp : Finset.univ.sum k = p
    . rw [hkp]
    . rw [not_imp_comm] at hf
      rw [hf hkp]
      simp only [TensorProduct.tmul_zero, smul_zero]

#align polynomial_map.is_homogeneous_of_degree_iff PolynomialMap.isHomogeneousOfDegree_iff


end PolynomialMap

end Homogeneous


section Components

/- Here, we will define the homogeneous components of a PolynomialMap.

Compared to what Roby writes, it seems we need further identifications
and/or base change of Polynomial maps…

-/

open Algebra Function LinearMap

open scoped TensorProduct

namespace PolynomialMap

open Polynomial

universe u v w

section Polynomial

variable {R : Type _} [CommSemiring R]
-- variable {ι : Type} [DecidableEq ι] [Fintype ι]

/- example : S →ₗ[S] S[X] := by
  exact Polynomial.monomial p

example : S ⊗[R] M →ₗ[S] S[X] ⊗[R] M :=
  TensorProduct.map' (Polynomial.monomial 1) (LinearMap.id)


noncomputable def test'' (S S' : Type _) [CommSemiring S] [CommSemiring S'] [Algebra S S'] :
  S[X] →ₐ[S] S'[X] := Polynomial.aeval X

noncomputable def test' (S S' : Type _) [CommSemiring S] [CommSemiring S'] (φ : S →+* S') :
  S[X] →+* S'[X] := Polynomial.eval₂RingHom (Polynomial.C.comp φ) X

variable (S S' : Type _) [CommSemiring S] [Algebra R S] [CommSemiring S'] [Algebra R S']
  (φ : S →ₐ[R] S') -/

lemma _root_.Polynomial.C_eq_algebraMap'
    {S : Type _} [CommSemiring S] [Algebra R S] (r : R) :
  Polynomial.C (algebraMap R S r) = algebraMap R S[X] r := rfl

-- TODO : find a better name for test3, and golf

/-- test3 φ aplies φ on the coefficients of a polynomial in S[X] -/
noncomputable def test3
    {S : Type _} [CommSemiring S] [Algebra R S]
    {S' : Type _} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') : S[X] →ₐ[R] S'[X] where
  toRingHom := Polynomial.eval₂RingHom (Polynomial.C.comp φ) X
  commutes' := fun r ↦ by simp [← Polynomial.C_eq_algebraMap']

/-
Other attempts to `test3`

def _root_.Polynomial.aeval'
    {S S' : Type _} [CommSemiring S] [Algebra R S] [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') (g : S') : S[X] →ₐ[R] S' where
  toRingHom := Polynomial.eval₂RingHom φ g
  commutes' := fun r ↦ by simp [← Polynomial.C_eq_algebraMap']

noncomputable def test3'
    {S S' : Type _} [CommSemiring S] [Algebra R S] [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') : S[X] →ₐ[R] S'[X] := by
  refine' Polynomial.aeval' _ (X : Polynomial S')
  refine' AlgHom.comp _ φ
  have h : S' →ₐ[S'] S'[X]
  . exact
    { toRingHom := algebraMap S' S'[X],
      commutes' := fun s ↦ by simp }
  exact h.restrictScalars R

noncomputable def test4
    {S S' : Type _} [CommSemiring S] [Algebra R S] [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') : S[X] →ₐ[R] S'[X] := by
  let hzz := (@Polynomial.aeval S S'[X] _ _
    (RingHom.toAlgebra (Polynomial.C.comp φ)) X)
  exact hzz.restrictScalars R

 -/


lemma coeff_test3_apply_eq {S S' : Type _} [CommSemiring S] [Algebra R S]
    [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') (f : S[X]) (p : ℕ) :
  Polynomial.coeff (test3 φ f) p
    = φ (Polynomial.coeff f p) := by
  simp only [test3, AlgHom.coe_mk, coe_eval₂RingHom]
  induction f using Polynomial.induction_on with
  | h_C r =>
      simp only [Polynomial.eval₂_C, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Polynomial.coeff_C]
      rw [apply_ite φ, map_zero]
  | h_add f g hf hg =>
      simp only [Polynomial.eval₂_add, Polynomial.coeff_add, hf, hg, map_add]
  | h_monomial n r _ =>
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.coe_comp,
        RingHom.coe_coe, Function.comp_apply, eval₂_X_pow,
        Polynomial.coeff_C_mul, _root_.map_mul, Polynomial.coeff_X_pow]
      rw [apply_ite φ, _root_.map_one, map_zero]

lemma coeff_comp_test3_eq {S S' : Type _} [CommSemiring S] [Algebra R S]
    [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
  LinearMap.comp (AlgHom.toLinearMap φ) ((lcoeff S p).restrictScalars R)
    = LinearMap.comp ((lcoeff S' p).restrictScalars R) (test3 φ).toLinearMap := by
  ext f
  simp only [coe_comp, coe_restrictScalars, Function.comp_apply, lcoeff_apply, AlgHom.toLinearMap_apply]
  rw [coeff_test3_apply_eq]

lemma test3_monomial {S S' : Type _} [CommSemiring S] [Algebra R S]
    [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S')
    (n : ℕ) (a : S):
  (test3 φ) ((Polynomial.monomial n) a) = (Polynomial.monomial n) (φ a)
  /- LinearMap.comp (AlgHom.toLinearMap (test3 φ))
        ((Polynomial.monomial n).restrictScalars R)
      = LinearMap.comp ((Polynomial.monomial 1).restrictScalars R)
          (AlgHom.toLinearMap φ) -/ := by
  dsimp [test3]
  simp only [Polynomial.eval₂_monomial, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  exact Polynomial.C_mul_X_pow_eq_monomial

end Polynomial

variable {R : Type u} [CommSemiring R]
  {M : Type _} [AddCommMonoid M] [Module R M]
  {N : Type _} [AddCommMonoid N] [Module R N]

/- noncomputable def component' (p : ℕ) (f : PolynomialMap R M N) :
  PolynomialMap R M N where
  toFun S _ _ := fun m ↦ TensorProduct.map' (Polynomial.lcoeff S p) (LinearMap.id)
    (f.toFun S[X] (TensorProduct.map' (Polynomial.monomial 1) (LinearMap.id) m))
  isCompat {S _ _ S' _ _} φ  := by
    ext sm
    simp only [Function.comp_apply, TensorProduct.map'_rid_apply]
    rw [← LinearMap.rTensor_comp_apply]
    rw [← LinearMap.rTensor_comp_apply]
    -- have : Algebra S S' := φ.toAlgebra
    rw [coeff_comp_test3_eq]
    rw [LinearMap.rTensor_comp_apply]
    rw [f.isCompat_apply (test3 φ)]
    apply congr_arg
    apply congr_arg
    simp only [← LinearMap.rTensor_comp_apply]
    apply LinearMap.congr_fun
    apply congr_arg
    rw [LinearMap.ext_iff]
    intro s
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [test3_monomial]
 -/

/-- The homogeneous components of a `PolynomialMap` -/
noncomputable def component (p : ℕ) (f : PolynomialMap R M N) :
  PolynomialMap R M N where
  toFun S _ _ := fun m ↦
    rTensor (R := R) N (Polynomial.lcoeff S p)
      (f.toFun S[X] (rTensor M ((Polynomial.monomial (R := S) 1).restrictScalars R) m))
  isCompat φ := by
    ext sm
    simp only [Function.comp_apply]
    simp only [← LinearMap.rTensor_comp_apply]
    rw [coeff_comp_test3_eq]
    rw [LinearMap.rTensor_comp_apply]
    rw [f.isCompat_apply (test3 φ)]
    apply congr_arg
    apply congr_arg
    simp only [← LinearMap.rTensor_comp_apply]
    apply LinearMap.congr_fun
    apply congr_arg
    rw [LinearMap.ext_iff]
    intro s
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [test3_monomial]

/-- `f.PolynomialMap.component p` is homogeneous of degree p -/
lemma componentIsHomogeneous (p : ℕ) (f : PolynomialMap R M N) :
  (f.component p).IsHomogeneousOfDegree p:= by
  intro S _ _ s sm
  dsimp [component]
  let ψ := ((Polynomial.aeval (R := S) (monomial 1 s : S[X])).restrictScalars R)
  suffices  (rTensor M ((Polynomial.monomial 1).restrictScalars R)) (s • sm)
      = (rTensor M ψ.toLinearMap) (rTensor M ((monomial 1).restrictScalars R) sm) by
    rw [this]
    rw [← f.isCompat_apply ψ]
    generalize toFun f S[X] (rTensor M ((monomial 1).restrictScalars R) sm) = t
    rw [← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (s ^ p)).mk'_apply,
      ← coe_restrictScalars R]
    rw [← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    apply symm
    dsimp [rTensor, TensorProduct.map]
    apply TensorProduct.lift.unique
    intro f n
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, TensorProduct.lift.tmul,
      lcoeff_apply, TensorProduct.mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply,
      AlgHom.coe_restrictScalars']
    rw [TensorProduct.smul_tmul']
    apply congr_arg₂ _ _ rfl
    induction f using Polynomial.induction_on' with
    | h_add f g hf hg =>
        rw [coeff_add, smul_add, hf, hg, aeval_add, coeff_add]
    | h_monomial n a =>
        simp only [aeval_monomial, ← smul_eq_mul, algebraMap_smul, coeff_smul]
        simp only [monomial_pow, one_mul, coeff_monomial]
        split_ifs with h
        . simp only [smul_eq_mul]
          rw [mul_comm, h]
        . simp only [smul_zero]
  . --
    suffices ∀ (sm : S ⊗[R] M), s • sm =
        rTensor M (((IsLinearMap.isLinearMap_smul s).mk').restrictScalars R) sm by
      rw [this]
      simp only [← rTensor_comp_apply]
      apply LinearMap.congr_fun
      apply congr_arg
      rw [LinearMap.ext_iff]
      intro r
      simp only [compl₂_id, smul_eq_mul, TensorProduct.lift.tmul, coe_comp, coe_restrictScalars, Function.comp_apply,
        IsLinearMap.mk'_apply, TensorProduct.mk_apply, AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars',
        aeval_monomial, pow_one]
      rw [mul_comm]
      simp only [← smul_eq_mul, algebraMap_smul]
      rw [Polynomial.smul_monomial]
    --
    intro sm
    rw [← (IsLinearMap.isLinearMap_smul s).mk'_apply, ← LinearMap.coe_restrictScalars R]
    apply LinearMap.congr_fun
    dsimp [rTensor, TensorProduct.map]
    apply TensorProduct.lift.unique
    intro r m
    simp only [coe_restrictScalars, IsLinearMap.mk'_apply, compl₂_id, coe_comp, Function.comp_apply,
      TensorProduct.mk_apply]
    rw [TensorProduct.smul_tmul', smul_eq_mul]

theorem component_add (p : ℕ) (f g : PolynomialMap R M N) :
    (f + g).component p = f.component p + g.component p := by
  ext S _ _ sm
  simp only [add_def_apply, component, map_add]

theorem component_smul (r : R) (f : PolynomialMap R M N) :
    (r • f).component p = r • f.component p := by
  ext S _ _ sm
  simp only [component, smul_def, Pi.smul_apply, map_smul]

theorem LocFinsupp_component' -- (f : PolynomialMap R M N)
    (S : Type*) [CommSemiring S] [Algebra R S] (sn : S[X] ⊗[R] N) :
    Set.Finite (Function.support (fun i => (rTensor N ((lcoeff S i).restrictScalars R) sn))) := by
  induction sn using TensorProduct.induction_on with
  | zero => simp only [map_zero, Function.support_zero, Set.finite_empty]
  | tmul s m =>
    simp only [rTensor_tmul, coe_restrictScalars, lcoeff_apply]
    suffices _ ⊆ (s.support : Set ℕ) by
      apply Set.Finite.subset _ this
      exact Finset.finite_toSet (Polynomial.support s)
    intro i
    contrapose
    simp only [Finset.mem_coe, mem_support_iff, ne_eq, not_not, mem_support]
    intro hi
    simp only [hi, zero_tmul]
  | add sm sm' h h' =>
    simp only [map_add]
    apply Set.Finite.subset ?_ (Function.support_add _ _)
    exact Set.Finite.union h h'

noncomputable example
    (S : Type*) [CommSemiring S] [Algebra R S] (i : ℕ):
    S ⊗[R] N →ₗ[R] S[X] ⊗[R] N :=
  rTensor N ((monomial i).restrictScalars R)

noncomputable def f
    (S : Type*) [CommSemiring S] [Algebra R S] (sn : S[X] ⊗[R] N) :
    ℕ → S ⊗[R] N :=
  fun i => (rTensor N ((lcoeff S i).restrictScalars R) sn)

noncomputable def F
    (S : Type*) [CommSemiring S] [Algebra R S] :
    S[X] ⊗[R] N →ₗ[S] (ℕ → S ⊗[R] N) where
  toFun := fun sn i ↦ (rTensor N ((lcoeff S i).restrictScalars R) sn)
  map_add' := fun sn sn' ↦ by
    ext i
    simp only [map_add, Pi.add_apply]
  map_smul' := fun s sn ↦ by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply, @rTensor_smul']

lemma hF
    (S : Type*) [CommSemiring S] [Algebra R S] (sn : S[X] ⊗[R] N) :
    Set.Finite (Function.support (F S sn)) := by
  induction sn using TensorProduct.induction_on with
  | zero =>
    suffices F S 0 = (0 : ℕ → S ⊗[R] N) by
      simp only [this, support_zero', Set.finite_empty]
    ext i
    simp only [map_zero, Pi.zero_apply]
  | tmul s m =>
    suffices  _ ⊆ (s.support : Set ℕ) by
      apply Set.Finite.subset _ this
      exact Finset.finite_toSet (Polynomial.support s)
    intro i
    contrapose
    simp only [Finset.mem_coe, mem_support_iff, ne_eq, not_not, mem_support]
    intro hi
    simp [F, hi, zero_tmul]
  | add sm sm' h h' =>
    simp only [f, map_add]
    apply Set.Finite.subset ?_ (Function.support_add _ _)
    exact Set.Finite.union h h'

lemma hf
    (S : Type*) [CommSemiring S] [Algebra R S] (sn : S[X] ⊗[R] N) :
    Set.Finite (Function.support (f S sn)) := by
  induction sn using TensorProduct.induction_on with
  | zero =>
    suffices  f S 0 = (0 : ℕ → S ⊗[R] N) by
      simp only [this, support_zero', Set.finite_empty]
    ext i
    simp only [f, map_zero, Pi.zero_apply]
  | tmul s m =>
    suffices  _ ⊆ (s.support : Set ℕ) by
      apply Set.Finite.subset _ this
      exact Finset.finite_toSet (Polynomial.support s)
    intro i
    contrapose
    simp only [Finset.mem_coe, mem_support_iff, ne_eq, not_not, mem_support]
    intro hi
    simp [f, hi, zero_tmul]
  | add sm sm' h h' =>
    apply Set.Finite.subset (Set.Finite.union h h')
    intro i
    contrapose
    simp only [Set.mem_union, mem_support, f, ne_eq, map_add, not_not, not_or, and_imp]
    intro hi hi'
    rw [hi, hi', add_zero]

noncomputable def F'
    (S : Type*) [CommSemiring S] [Algebra R S] :
    S[X] ⊗[R] N →ₗ[S] (ℕ →₀ S ⊗[R] N) where
  toFun := fun sn => Finsupp.ofSupportFinite _ (hF S sn)
  map_add' := fun sn sn' => by
    ext i
    simp only [map_add, Finsupp.ofSupportFinite_coe, Pi.add_apply, Finsupp.coe_add]
  map_smul' := fun s sn => by
    ext i
    simp only [map_smul, Finsupp.ofSupportFinite_coe, Pi.smul_apply,
      RingHom.id_apply, Finsupp.coe_smul]

noncomputable def F'inv
    (S : Type*) [CommSemiring S] [Algebra R S] :
    (ℕ →₀ S ⊗[R] N) →ₗ[S] S[X] ⊗[R] N where
  toFun := fun f ↦ f.sum (fun i ↦ (rTensor N ((monomial i).restrictScalars R)))
  map_add' := fun f g ↦ by
    rw [← Finsupp.sum_add_index]
    · intro i _
      simp only [map_zero]
    · intro a _ s s'
      simp only [map_add]
  map_smul' := fun s f ↦ by
    simp only [RingHom.id_apply]
    -- doesn't work ! --  rw [Finsupp.sum_smul_index]
    apply symm
    rw [Finsupp.sum, Finset.smul_sum, Finsupp.sum_of_support_subset]
    apply Finset.sum_congr rfl
    · intro i _
      simp only [Finsupp.coe_smul, Pi.smul_apply, rTensor_smul']
    · exact Finsupp.support_smul
    · intro i _
      simp only [map_zero]

#check TensorProduct.directSumLeft

example : N ≃ₗ[R] (R →ₗ[R] N) := by
  exact LinearEquiv.symm (ringLmapEquivSelf R R N)

section

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable {ι : Type*} [DecidableEq ι]

def Finsupp.lsum (f : ι → M →ₗ[R] N) : (ι →₀ M) →ₗ[R] N where
  toFun := fun p ↦ p.sum (f · ·)
  map_add' := fun p q ↦ by
    rw [← Finsupp.sum_add_index]
    · intro i _ ; simp only [map_zero]
    · intro i _ m m'
      simp only [map_add]
  map_smul' := fun r p ↦ by
    simp only [Finsupp.sum_smul_index_linearMap', RingHom.id_apply]

noncomputable def Finsupp.tensorProductLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  LinearEquiv.ofLinear
    (TensorProduct.lift
      (Finsupp.lsum (fun i ↦ TensorProduct.curry (Finsupp.lsingle i))))
    (Finsupp.lsum (fun i ↦ rTensor N (Finsupp.lsingle i)))
    (by ext i m n j; simp [Finsupp.lsum])
    (by ext i m n; simp [Finsupp.lsum])

lemma Finsupp.tensorProductLeft_apply_tmul (p : ι →₀ M) (n : N) :
  Finsupp.tensorProductLeft (p ⊗ₜ[R] n) =
    p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp [tensorProductLeft, Finsupp.lsum]

lemma Finsupp.tensorProductLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    Finsupp.tensorProductLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [Finsupp.tensorProductLeft, Finsupp.lsum]

noncomputable def Finsupp.tensorProductRight :
    M ⊗[R] (ι →₀ N) ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  ((TensorProduct.comm R _ _).trans
    (Finsupp.tensorProductLeft (ι := ι) (M := N) (N := M) (R := R))).trans
      (Finsupp.mapRange.linearEquiv (TensorProduct.comm R _ _))



noncomputable example  :
    R[X] ⊗[R] N ≃ₗ[R] (ℕ →₀ N) := by
  apply LinearEquiv.ofLinear (TensorProduct.lift (Polynomial.lsum (fun i ↦ (ringLmapEquivSelf R R _).symm (Finsupp.lsingle i)))) (by

    sorry)
  · sorry
  · sorry

noncomputable example (S : Type*) [CommSemiring S] [Algebra R S] :
    S[X] ⊗[R] N ≃ₗ[S] (ℕ →₀ S ⊗[R] N) := {
  F' S with
  invFun := F'inv S
  left_inv := fun s => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add => simp only [map_add]; sorry
    | tmul => sorry
  right_inv := fun f => by
    ext i
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    sorry }



noncomputable def f'
    (S : Type*) [CommSemiring S] [Algebra R S] (sn : S[X] ⊗[R] N) :
    ℕ →₀ S ⊗[R] N :=
  Finsupp.ofSupportFinite _ (hf S sn)

noncomputable def hf'
    (S : Type*) [CommSemiring S] [Algebra R S] (sn : S[X] ⊗[R] N) :
    (Finsupp.ofSupportFinite _ (hf S sn)).sum
      (fun i => (rTensor N ((monomial i).restrictScalars R))) = sn := by
  induction sn using TensorProduct.induction_on with
  | zero => exact (Finsupp.sum_zero)
  | tmul s n =>
    conv_rhs => rw [← Polynomial.sum_monomial_eq s]
    rw [Polynomial.sum, TensorProduct.sum_tmul]
    rw [Finsupp.sum_of_support_subset (s := s.support)]
    apply Finset.sum_congr rfl
    · intro i _
      rfl
    · intro i
      contrapose
      simp only [mem_support_iff, ne_eq, not_not, Finsupp.mem_support_iff]
      intro hi
      rw [Finsupp.ofSupportFinite_coe]
      simp only [f, rTensor_tmul, coe_restrictScalars, lcoeff_apply, hi, zero_tmul]
    · intro i _
      simp only [map_zero]
  | add sn sn' h h' =>
    conv_rhs => rw [← h, ← h']
    rw [← Finsupp.sum_add_index]
    · conv_rhs => rw [Finsupp.sum]
      rw [Finsupp.sum_of_support_subset]
      apply Finset.sum_congr rfl
      · intro i _
        simp [Finsupp.ofSupportFinite_coe, f]
      · intro i
        contrapose
        simp [Finsupp.ofSupportFinite_coe, f]
      · intro i _
        simp only [map_zero]
    · simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq, map_zero, implies_true,
      forall_const]
    · simp only [Finset.mem_union, Finsupp.mem_support_iff, ne_eq, map_add, forall_const,
      implies_true]



--       (fun i => rTensor N ((monomial i).restrictScalars R) (rTensor N ((lcoeff S i).restrictScalars R) sn)) := by
  --sorry

  -- fun i => (rTensor N ((lcoeff S i).restrictScalars R) sn)

theorem LocFinsupp_component (f : PolynomialMap R M N) :
    LocFinsupp (fun p ↦ f.component p) := by
  intro S _ _ sm
  simp only [component]
  apply LocFinsupp_component'

/-- A polynomial map is the locally finite sum of its homogeneous components.
(PolynomialMap lies in between the direct sum and the product of its graded submodules, hence there is no graded module structure.) -/
theorem recompose_component (f : PolynomialMap R M N) :
    f.LocFinsupp_component.sum = f := by
  ext S _ _ sm
  simp [LocFinsupp.sum, component]
  have := f.isCompat_apply ((algebraMap' S S[X]).restrictScalars R) sm
  set φ := rTensor N ((algebraMap' S S[X]).restrictScalars R).toLinearMap
  suffices h : Function.Injective φ by
    apply h
    simp [φ, this]
    rw [map_finsupp_sum]
    sorry
  -- suffices : f.toFun S[X] ((rTensor M (monomial (1 : S)).restrictScalars R) sm = sm
  sorry

example  {α : Type*} {M : Type*} {N : Type*} {P : Type*}
    [Zero M] [AddCommMonoid N] [AddCommMonoid P]
    (f : α →₀ M) (g : α → M → N) (h : N →+ P) :
    h (f.sum g) = f.sum (fun a m => h (g a m)) := by
  apply _root_.map_finsupp_sum

#exit

section test







example {S : Type u} [CommSemiring S] [Algebra R S]  (r : R) : S →ₗ[R] S := (IsLinearMap.isLinearMap_smul r).mk'

lemma _root_.TensorProduct.smul_left
  (r : R) (mn : M ⊗[R] N):
  rTensor N (IsLinearMap.isLinearMap_smul (M := M) r).mk' mn = r • mn
  := by
  rw [← (IsLinearMap.isLinearMap_smul (M := M ⊗[R] N) r).mk'_apply]
  dsimp only [rTensor, TensorProduct.map]
  revert mn
  rw [← LinearMap.ext_iff]
  apply symm
  apply TensorProduct.lift.unique
  intro m n
  simp only [IsLinearMap.mk'_apply, compl₂_id, coe_comp, Function.comp_apply, map_smul, smul_apply,
    TensorProduct.mk_apply]


variable {S : Type _} [CommSemiring S] [Algebra R S]
  {M : Type _} [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  {N : Type _} [AddCommMonoid N] [Module R N]
  (s : S) (mn : M ⊗[R] N)

#check IsLinearMap.isLinearMap_smul (M := M) s

#check (IsLinearMap.isLinearMap_smul (M := M) s).mk'

#check ((IsLinearMap.isLinearMap_smul (M := M) s).mk').restrictScalars R


#check TensorProduct.map' (Polynomial.monomial 1) LinearMap.id

#check rTensor N ((Polynomial.monomial (R := S) 1).restrictScalars R)


#check (Polynomial.monomial (R := S) 1)

lemma _root_.TensorProduct.smul_left'
  {S : Type _} [CommSemiring S] [Algebra R S]
  {M : Type _} [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  {N : Type _} [AddCommMonoid N] [Module R N]
  (s : S) (mn : M ⊗[R] N) :
  rTensor N (((IsLinearMap.isLinearMap_smul (M := M) s).mk').restrictScalars R) mn = s • mn := rfl


#check TensorProduct.smul_left'

#check Polynomial.monomial (R := S) 0

#check (Polynomial.monomial (R := S) 0).restrictScalars R

#check rTensor M ((Polynomial.monomial (R := S) 0).restrictScalars R
)

-- For f ∈ S[X], the multiplication by f on the left on S[X] \otimes[R] M
-- is given by
variable (f : S[X])
#check IsLinearMap.isLinearMap_smul (M := S[X] ⊗[R] M) f
#check (IsLinearMap.isLinearMap_smul (M := S[X] ⊗[R] M) f).mk'
#check ((IsLinearMap.isLinearMap_smul (M := S[X] ⊗[R] M) f).mk').restrictScalars R


/- Pour s ∈ S[X], définir S[X] →ₐ[R] S[X] qui applique X sur f -/
noncomputable def test4 (f : S[X]) : S →ₗ[S] S[X]  := {
  toFun := fun a ↦ a • f
  map_add' := fun a b ↦ add_smul a b f
  map_smul' := fun a b ↦ (smul_smul a b f).symm }





end test


end PolynomialMap

end Components
ply?
