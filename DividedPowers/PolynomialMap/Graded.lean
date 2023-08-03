import DividedPowers.PolynomialMap.Coeff
import Mathlib.RingTheory.TensorProduct
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic

section Homogeneous

open Algebra Function LinearMap

open scoped TensorProduct

namespace PolynomialMap

universe u v w

variable {R : Type u} {M N : Type _} [CommRing R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

def IsHomogeneousOfDegree
    (p : ℕ) (f : PolynomialMap R M N) : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (r : S) (m : S ⊗[R] M),
    f.toFun S (r • m) = r ^ p • f.toFun S m
#align polynomial_map.is_homogeneous_of_degree PolynomialMap.IsHomogeneousOfDegree

theorem TensorProduct.is_finsupp_sum_tmul {R S : Type _}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Module R M]
    (m : S ⊗[R] M) :
  ∃ r : M →₀ S, m = r.sum fun x a => a ⊗ₜ[R] x :=
  by
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
#align tensor_product.is_finsupp_sum_tmul PolynomialMap.TensorProduct.is_finsupp_sum_tmul

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
      suffices : ¬ (n1 + x  < n1)
      simp only [if_neg this]
      simp only [add_tsub_cancel_left]
      simp only [not_lt, Nat.le_add_right]

example (α : Type _) [Fintype α] : Fintype (ULift α) := by exact ULift.fintype α

example (α : Type _) : α ≃ ULift α := by apply?

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

#print Equiv.ulift_apply
def ULift.up_embedding {α : Type _} : α ↪ ULift α where
  toFun := ULift.up
  inj' := ULift.up_injective

theorem ULift.finset_sum (α : Type _) (s : Finset α) (f : α → ℕ) :
  s.sum f = Finset.sum (s.map ULift.up_embedding)
    (fun (x : ULift α) ↦ f x.down) := by
  rw [Finset.sum_bij' (fun a _ ↦ ULift.up a) _ _ (fun a _ ↦ a.down)]
  . intro a ha
    simp only [Finset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hb
  . intro a _ ; rfl
  . intro a _ ; rfl
  . intro a ha
    simp only [Finset.mem_map]
    exact ⟨a, ha, rfl⟩
  . intro a _ ; rfl


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
    simp only [Finset.prod_empty, Finset.sum_empty, MvPolynomial.monomial_zero', map_one] 
  | insert ha hs => 
      rw [Finset.prod_insert ha, hs, MvPolynomial.monomial_mul, 
        Finset.sum_insert ha, Finset.prod_insert ha]

lemma _root_.MvPolynomial.monomial_one_eq {α : Type _} [DecidableEq α]  
    (c : α →₀ ℕ) :
    MvPolynomial.monomial c (1 : R) = c.prod fun a n => MvPolynomial.X a ^ n := by
    rw [MvPolynomial.monomial_eq, map_one, one_mul]
    
lemma _root_.Finsupp.eq_sum_single_apply {α : Type _} [DecidableEq α] [Fintype α] 
    (c : α →₀ ℕ) :
  Finset.sum Finset.univ (fun a => Finsupp.single a (c a)) = c := by
  ext a
  rw [Finset.sum_apply', Finset.sum_eq_single a]
  . simp only [Finsupp.single_eq_same]
  . intro b _ hb
    simp only [Finsupp.single_eq_of_ne hb]
  . simp only [Finset.mem_univ a]
    apply False.elim

/-- (Roby, Prop. I.1)
  A PolynomialMap is Homogeneous of degree p 
  iff all its nonzero coefficients have degree p -/
theorem isHomogeneousOfDegree_iff
    (p : ℕ) (f : PolynomialMap R M N) :
  f.IsHomogeneousOfDegree p ↔
    ∀ {ι : Type u} [DecidableEq ι] [Fintype ι]
      (m : ι → M) (k : ι →₀ ℕ) (h : coeff m f k ≠ 0),
      (Finset.univ.sum k) = p :=
  by
  classical
  constructor
  · -- difficult direction
    intro hf
    intro ι _ _ m k
    rw [not_imp_comm]
    by_cases hι : Nonempty ι
    . intro hk

      suffices : ∀ (s : Finset (ι →₀ ℕ)), ∃ (l : ι →₀ ℕ), 
        ∀ a ∈ s, ∀ b ∈ s,
        (Finset.univ.sum a) • l + a = p • l + b → 
        (Finset.univ.sum a = p ∧ a = b)
      obtain ⟨l, hl⟩ := this (insert k (coeff m f).support)

      specialize hf (MvPolynomial ι R) (MvPolynomial.monomial l 1)
        (Finset.sum Finset.univ fun i => MvPolynomial.X i ⊗ₜ[R] m i)
      simp only [Finset.smul_sum, TensorProduct.smul_tmul', image_eq_coeff_sum] at hf
      simp only [Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf
      -- write the summands as monomials
      simp_rw [smul_eq_mul, mul_pow, Finset.prod_mul_distrib, 
        Finset.prod_pow_eq_pow_sum, MvPolynomial.monomial_pow,
        one_pow] at hf
      suffices : ∀ (c : ι →₀ ℕ), 
        MvPolynomial.monomial c (1 : R) = Finset.univ.prod (fun i ↦ MvPolynomial.X i ^ c i)
      simp_rw [← this] at hf
      simp_rw [MvPolynomial.monomial_mul, mul_one] at hf

      let hf' := (zooEquiv ι R N).symm.congr_arg hf
      rw [FunLike.ext_iff] at hf'
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

      . intro y _ hy
        rw [if_neg]
        intro hy'
        apply hy
        exact add_left_cancel hy'
      . rw [if_pos rfl]
        simp only [Finsupp.mem_support_iff, ne_eq, not_not, imp_self]

      . intro c
        simp only [MvPolynomial.monomial_eq, map_one, Finsupp.prod_pow, one_mul]


      . -- The choice of l 
        intro s
        suffices : ∃ N, ∀ (l : ι →₀ ℕ), 
          N ≤ Finset.univ.sum l →
          ∀ a ∈ s, ∀ b ∈ s, 
            Finset.univ.sum a • l + a = p • l + b →
            Finset.univ.sum a = p ∧ a = b
          
        obtain ⟨N, hN⟩ := this
        obtain ⟨i : ι⟩ := hι
        use Finsupp.single i N
        apply hN
        simp only [Finsupp.sum_univ_single, le_refl]
        
        use (s.sup (fun a ↦ Finset.univ.sum a)).succ
        intro l hl a ha b hb h
        suffices : Finset.univ.sum a = p
        . constructor
          exact this
          rw [this] at h
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
      simp only [zero_pow' p (ne_comm.mp hp), zero_smul] at hf 
      simp only [coeff, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        zooEquiv_symm_apply, AddEquivClass.map_eq_zero_iff] 
      suffices : generize R N m f = 0
      . simp only [this, map_zero]
      . simp only [generize._eq_1, Finset.univ_eq_empty, Finset.sum_empty, 
          coe_mk, AddHom.coe_mk]
        exact hf
  · -- Trivial direction
    intro hf S _ _ c m
    obtain ⟨n, _, r, m, rfl⟩ := TensorProduct.is_finsupp_sum_tmul'' m

    rw [Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul', Pi.smul_def]
    have : ∀ x, c • r ↑x = (c • r) ↑x := by intro x ; rfl
    simp only [this]
    simp only [image_eq_coeff_sum, Finsupp.smul_sum]
    apply Finsupp.sum_congr
    intro k hk
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

open Polynomial MvPolynomial

universe u v w

variable {R : Type u} {M N : Type _} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

def _root_.TensorProduct.map'
    {S : Type _} [CommSemiring S] [Algebra R S]
    {N : Type _} [AddCommMonoid N] [Module R N]
    {P : Type _} [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P] 
    {Q : Type _} [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : P →ₗ[S] Q) (g : M →ₗ[R] N) :
  P ⊗[R] M →ₗ[S] Q ⊗[R] N := {
  toFun   := TensorProduct.map  (f.restrictScalars R) g
  map_add'  := by simp only [map_add, forall_const] 
  map_smul' := fun s x ↦ by
    dsimp
    induction x using TensorProduct.induction_on with
    | C0 => 
        simp only [smul_zero, map_zero]
    | C1 x y => 
        simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul]
        simp only [coe_restrictScalars, map_smul]
    | Cp x y hx hy => 
        simp only [smul_add, map_add, hx, hy] }

lemma _root_.TensorProduct.map'_rid_apply
    {S : Type _} [CommSemiring S] [Algebra R S]
    {P : Type _} [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P] 
    {Q : Type _} [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : P →ₗ[S] Q) (pm : P ⊗[R] N) :
    TensorProduct.map' f (LinearMap.id) (pm) = rTensor N (f.restrictScalars R) (pm) := rfl 


-- variable {ι : Type} [DecidableEq ι] [Fintype ι]

/- example : S →ₗ[S] S[X] := by 
  exact Polynomial.monomial p

example : S ⊗[R] M →ₗ[S] S[X] ⊗[R] M := 
  TensorProduct.map' (Polynomial.monomial 1) (LinearMap.id)


noncomputable def test'' (S S' : Type _) [CommRing S] [CommRing S'] [Algebra S S'] :
  S[X] →ₐ[S] S'[X] := Polynomial.aeval X

noncomputable def test' (S S' : Type _) [CommRing S] [CommRing S'] (φ : S →+* S') :
  S[X] →+* S'[X] := Polynomial.eval₂RingHom (Polynomial.C.comp φ) X
  
variable (S S' : Type _) [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  (φ : S →ₐ[R] S') -/

lemma _root_.Polynomial.C_eq_algebraMap' {S : Type _} [CommSemiring S] [Algebra R S]
  (r : R) : Polynomial.C (algebraMap R S r) = algebraMap R S[X] r := rfl 

noncomputable def test3 
  {S S' : Type _} [CommSemiring S] [Algebra R S] [CommSemiring S'] [Algebra R S']
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
        Polynomial.coeff_C_mul, map_mul, Polynomial.coeff_X_pow]
      rw [apply_ite φ, map_one, map_zero]

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


/-- The homogeneous components of a `PolynomialMap` -/
noncomputable def component (p : ℕ) (f : PolynomialMap R M N) :
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
    revert sm
    rw [← LinearMap.ext_iff]
    apply congr_arg
    rw [LinearMap.ext_iff]
    intro s
    simp only [coe_comp, coe_restrictScalars, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [test3_monomial]


end PolynomialMap

end Components

