/- Copyright ACL & MIdFF, 2024 -/

import DividedPowers.ForMathlib.MvPowerSeries.Substitutions

/-! # Exponential module of a commutative ring

Let `R` be a commutative ring.
The exponential module of `R` is the set of all power series `f : R⟦X⟧`
that are of exponential type :
  `f (X + Y) = f X * f Y`
where `X` and `Y` are two indeterminates
It is an abelian group under multiplication, and an `R`-module under rescaling.

* For `f : R⟦X⟧`, `IsExponential f` says that `f` is of exponential type

* `ExponentialModule R` is the exponential module of `R`.

* For `f : R →+* S`, we define `ExponentialModule.map f : ExponentialModule R → ExponentialModule S`

## TODO

* Prove that the inverse of a power series of exponential type is exponential,
the inverse being given by `f (-X)`

-/

section complements

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommSemiring R]

@[simp]
lemma MvPolynomial.coe_smul (φ : MvPolynomial σ R) (r : R) :
  (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

@[simp]
lemma Polynomial.coe_smul (φ : Polynomial R) (r : R) :
  (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl

@[simp]
theorem PowerSeries.constantCoeff_smul (a : R) (f : PowerSeries R) :
    PowerSeries.constantCoeff R (a • f) = a • PowerSeries.constantCoeff R f :=
  rfl

end complements

section IsExponential

namespace PowerSeries

open MvPowerSeries

variable {A : Type*} [CommRing A]
variable {R : Type*} [CommRing R] [Algebra A R]
variable {S : Type*} [CommRing S] [Algebra A S]

/-- A power series f : R⟦X⟧ is exponential if f(X + Y) = f(X) f(Y) and f(0) = 1 -/
structure IsExponential (f : R⟦X⟧) : Prop where
  add_mul : subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f
    = subst (MvPowerSeries.X 0) f * PowerSeries.subst (MvPowerSeries.X 1) f
  constantCoeff : constantCoeff R f = 1

private lemma coeff_add_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    MvPolynomial.coeff d ((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ^ n) =
    if (d 0, d 1) ∈ Finset.antidiagonal n
    then n.choose (d 0)
    else 0 := by
  have hmon : ∀ (u v : ℕ),
    MvPolynomial.X (0 : Fin 2) ^ u * MvPolynomial.X 1 ^ v
      = MvPolynomial.monomial (Finsupp.single 0 u + Finsupp.single 1 v) (1 : R) := by
    intro u v
    rw [MvPolynomial.monomial_eq]
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
    · simp only [map_one, Fin.prod_univ_two, Fin.isValue, one_mul]
      simp only [Fin.isValue, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.single_eq_of_ne, add_zero, zero_ne_one, zero_add]
    · exact fun i _ ↦ by simp only [pow_zero]
  rw [Commute.add_pow' (Commute.all _ _), MvPolynomial.coeff_sum]
  simp only [nsmul_eq_smul, MvPolynomial.coeff_smul]
  simp only [Fin.isValue, Nat.cast_ite, Nat.cast_zero, hmon]
  split_ifs with hd
  · rw [Finset.sum_eq_single (d 0, d 1)]
    · rw [MvPolynomial.coeff_monomial, if_pos]
      simp only [Fin.isValue, nsmul_eq_mul, mul_one]
      ext i
      match i with
      | 0 => simp
      | 1 => simp
    · intro e _ hed
      rw [MvPolynomial.coeff_monomial, if_neg, smul_zero]
      intro hde
      apply hed
      rw [← hde]
      simp
    · intro hd'
      contradiction
  · apply Finset.sum_eq_zero
    intro e he
    simp only [Finset.mem_antidiagonal] at he
    rw [MvPolynomial.coeff_monomial, if_neg, smul_zero]
    intro hed
    apply hd
    rw [← hed, Finset.mem_antidiagonal]
    simpa using he

lemma coeff_subst_single {σ : Type*} [DecidableEq σ] [Finite σ]
    (s : σ) (f : R⟦X⟧) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff R e (subst (MvPowerSeries.X s) f) =
      if e = Finsupp.single s (e s)
      then PowerSeries.coeff R (e s) f
      else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.substDomain_of_constantCoeff_zero (by simp))]
  rw [finsum_eq_single _ (e s)]
  · rw [MvPowerSeries.coeff_X_pow]
    simp only [Fin.isValue, ↓reduceIte, smul_eq_mul, mul_one]
    split_ifs with he
    · rw [mul_one]
    · rw [mul_zero]
  · intro d hd
    simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro hd'
    simp only [hd', Finsupp.single_eq_same, ne_eq, not_true_eq_false] at hd

lemma ne_zero_of_mul_ne_zero {M : Type*} [MonoidWithZero M] {a b : M}
    (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    apply h
    rw [ha, zero_mul]
  · intro hb
    apply h
    rw [hb, mul_zero]

lemma fin_two_equiv_prod (α : Type*) [Zero α] : ((Fin 2) →₀ α) ≃ α × α :=
  Finsupp.equivFunOnFinite.trans {
  toFun := fun e ↦ (e 0, e 1)
  invFun := fun (a, b) i ↦ match i with
    | 0 => a
    | 1 => b
  left_inv := fun e ↦ by
    ext i
    match i with
    | 0 => rfl
    | 1 => rfl
  right_inv := fun (a, b) ↦ by
    simp only
  }

lemma forall_congr_curry {α : Type*}
    {p : (Fin 2 → α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 → α, p e ↔ q (e 0) (e 1)) :
    (∀ (e : Fin 2 → α), p e) ↔ ∀ (u v : α), q u v := by
  constructor
  · intro H u v
    set e : Fin 2 → α := fun
    | 0 => u
    | 1 => v
    specialize hpq e
    simp [e] at hpq
    rw [← hpq]
    apply H
  · intro H e
    rw [hpq]
    apply H

lemma forall_congr_curry₀ {α : Type*} [Zero α]
    {p : (Fin 2 →₀ α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 →₀ α, p e ↔ q (e 0) (e 1)) :
    (∀ e, p e) ↔ ∀ u v, q u v := by
  constructor
  · intro H u v
    set e : Fin 2 → α := fun
    | 0 => u
    | 1 => v
    specialize hpq (Finsupp.equivFunOnFinite.symm e)
    simp [e] at hpq
    rw [← hpq]
    apply H
  · intro H e
    rw [hpq]
    apply H

/-- A power series f is exponential iff its coefficients (f n) satisfy
  the relations `(p + q).choose p * f (p + q)= f p * f q`
  and its constant coefficient is 1 -/
theorem isExponential_add_mul_iff (f : R⟦X⟧) :
    (subst (MvPowerSeries.X 0 + MvPowerSeries.X 1) f : MvPowerSeries (Fin 2) R)
      = (subst (MvPowerSeries.X 0) f : MvPowerSeries (Fin 2) R) * (subst (MvPowerSeries.X 1) f : MvPowerSeries (Fin 2) R)
    ↔ ∀ (p q : ℕ), (p + q).choose p * (coeff R (p + q) f) =
        coeff R p f * coeff R q f:= by
  have he : ∀ (e : Fin 2 →₀ ℕ), (MvPowerSeries.coeff R e) (subst (MvPowerSeries.X 0 + MvPowerSeries.X 1) f) = (e 0 + e 1).choose (e 0) * coeff R (e 0 + e 1) f := by
    intro e
    rw [PowerSeries.subst, MvPowerSeries.coeff_subst _]
    simp only [Fin.isValue, Finsupp.prod_pow, Finset.univ_unique,
      PUnit.default_eq_unit, Finset.prod_singleton, smul_eq_mul]
    simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe]
    rw [finsum_eq_single _ (Finsupp.single () (e 0 + e 1)), mul_comm]
    · apply congr_arg₂
      simp only [Finsupp.single_add, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      simp only [Fin.isValue, coeff_add_pow e _, Finset.mem_antidiagonal, ↓reduceIte, coeff]
      rfl
    · intro d hd'
      simp [coeff_add_pow]
      intro hd
      exfalso
      apply hd'
      ext
      simp only [PUnit.default_eq_unit, hd, Finsupp.single_eq_same]
    · exact MvPowerSeries.substDomain_of_constantCoeff_zero
            (fun _ ↦ by simp)
  have he' : ∀ (e : Fin 2 →₀ ℕ),
    MvPowerSeries.coeff R e
      (subst (MvPowerSeries.X 0) f * subst (MvPowerSeries.X 1) f) =
        coeff R (e 0) f * coeff R (e 1) f := by
    intro e
    rw [MvPowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
    · apply congr_arg₂
      · simp only [coeff_subst_single, Finsupp.single_eq_same, if_pos]
      · simp only [coeff_subst_single, Finsupp.single_eq_same, if_pos]
    · intro b hb hb'
      rw [Finset.mem_antidiagonal] at hb
      by_contra hmul_ne_zero
      rcases ne_zero_of_mul_ne_zero hmul_ne_zero with ⟨h0, h1⟩
      simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff,
        not_forall, exists_prop] at h0 h1
      apply hb'
      rw [Prod.ext_iff, ← hb, h0.1, h1.1]
      simp
    · intro he
      exfalso
      apply he
      simp only [Finset.mem_antidiagonal]
      ext i
      match i with
      | 0 => simp
      | 1 => simp
  rw [MvPowerSeries.ext_iff]
  convert forall_congr_curry₀ _
  intro e
  rw [he, he']

/-- A power series f is exponential iff its coefficients (f n) satisfy
  the relations `(p + q).choose p * f (p + q)= f p * f q`
  and its constant coefficient is 1 -/
theorem isExponential_iff (f : R⟦X⟧) :
    IsExponential f
    ↔  (constantCoeff R f = 1) ∧ ∀ p q, (p + q).choose p * coeff R (p + q) f = coeff R p f * coeff R q f := by
  rw [← isExponential_add_mul_iff]
  constructor
  · exact fun hf ↦ ⟨hf.constantCoeff, hf.add_mul⟩
  · exact fun hf ↦ {
      constantCoeff := hf.1
      add_mul := hf.2 }

/-- The unit power series is exponential -/
theorem isExponential_one : IsExponential (1 : R⟦X⟧) where
  add_mul := by
    rw [← Polynomial.coe_one]
    rw [subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    rw [subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    rw [subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    simp only [map_one, mul_one]
  constantCoeff := by simp only [map_one]

/-- If f and g are exponential, then so is f * g -/
theorem isExponential_mul {f g : PowerSeries R}
    (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) where
  add_mul := by
    repeat
      rw [← coe_substAlgHom (substDomain_of_constantCoeff_zero (by simp))]
    simp only [map_mul, coe_substAlgHom, hf.add_mul, hg.add_mul]
    ring
  constantCoeff := by simp only [map_mul, hf.constantCoeff, hg.constantCoeff, mul_one]

/-- If `f` is exponential and n : ℕ`, then `f ^ n` is exponential -/
theorem isExponential_npow {f : R⟦X⟧} (hf : IsExponential f) (n : ℕ) :
    IsExponential (f ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, pow_zero]
    exact isExponential_one
  | succ n hn =>
    rw [pow_succ]
    exact isExponential_mul hn hf

/-- If f is exponential, then f(r T) is exponential, for any r : R -/
theorem isExponential_scale (a : A) {f : PowerSeries R} (hf : IsExponential f) :
    IsExponential (scale a f) where
  constantCoeff := by
    rw [← coeff_zero_eq_constantCoeff, coeff_scale]
    simp only [pow_zero, coeff_zero_eq_constantCoeff, one_smul,
      hf.constantCoeff]
  add_mul := by
    rw [subst_linear_subst_scalar_comm]
    rw [subst_linear_subst_scalar_comm]
    rw [subst_linear_subst_scalar_comm]
    simp only [← MvPowerSeries.coe_scale_algHom, ← map_mul, hf.add_mul]
    -- we prove the hypothesis of the last two applications of subst_linear_subst_scalar_comm
    repeat
      intro d hd
      simp only [Fin.isValue, map_add, MvPowerSeries.coeff_X]
      rw [if_neg]
      intro hd'
      apply hd
      rw [hd']
      simp only [Fin.isValue, Finsupp.sum_single_index]
    -- the first application of subst_linear_subst_scalar_comm is a bit different
    · intro d hd
      simp only [Fin.isValue, map_add, MvPowerSeries.coeff_X]
      split_ifs with h0 h1 h1
      · rw [h1, Finsupp.single_left_inj (by norm_num)] at h0
        exfalso; exact one_ne_zero h0
      · exfalso; apply hd
        simp only [h0, Fin.isValue, Finsupp.sum_single_index]
      · exfalso; apply hd
        simp only [h1, Fin.isValue, Finsupp.sum_single_index]
      · simp only [add_zero]

theorem isExponential_scale_add (r s : A) {f : R⟦X⟧} (hf : IsExponential f) :
    scale (r + s) f = scale r f * scale s f := by
  let a : Fin 2 → PowerSeries R
  | 0 => r • X
  | 1 => s • X
  have ha : MvPowerSeries.SubstDomain a := by
    apply MvPowerSeries.substDomain_of_constantCoeff_zero
    intro i
    simp only [X, a]
    match i with
    | 0 =>
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
    | 1 =>
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hf' := congr_arg (MvPowerSeries.subst a) hf.add_mul
  simp only [PowerSeries.subst] at hf'
  rw [← MvPowerSeries.coe_substAlgHom ha] at hf'
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))] at hf'
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))] at hf'
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))] at hf'
  simp only [MvPowerSeries.substAlgHom_comp_substAlgHom_apply, map_mul] at hf'
  simp only [MvPowerSeries.coe_substAlgHom] at hf'
  simp only [scale_eq_subst, subst]
  convert hf'
  repeat
    simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_add,
      MvPowerSeries.subst_coe ha]
    simp only [Fin.isValue, map_add, MvPolynomial.aeval_X, add_smul]

theorem isExponential_neg {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (scale  (-1 : A) f) := isExponential_scale (-1 : A) hf

theorem isExponential_self_mul_neg_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    f * (scale (-1 : A) f) = 1 := by
  convert (isExponential_scale_add (1 : A) (-1 : A) hf).symm
  · rw [scale_one, id_eq]
  · simp only [add_right_neg, scale_zero_apply, hf.constantCoeff, map_one]

theorem isExponential_neg_mul_self_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    (scale (-1) f) * f = 1 := by
  rw [mul_comm, isExponential_self_mul_neg_eq_one hf]

theorem isExponential_map (φ : R →+* S) {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (PowerSeries.map φ f) := by
  rw [isExponential_iff]
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff, hf.constantCoeff, map_one]
  · intro p q
    simp only [coeff_map, ← map_mul, ← ((isExponential_iff f).mp hf).2 p q]
    simp only [map_mul, map_natCast]

open Additive

noncomputable instance : SMul A (Additive R⟦X⟧) where
  smul r f := ofMul.toFun (scale r (toMul f))

lemma toAdditive_smul_coe (r : A) (f : R⟦X⟧) :
  r • (ofMul f) = ofMul (scale r f) := rfl

lemma toAdditive_smul_coe' (r : A) (f : Additive R⟦X⟧) :
  toMul (r • f) = scale r (toMul f) := rfl

noncomputable instance : DistribMulAction A (Additive R⟦X⟧) where
  one_smul := by
    simp only [Additive.forall, toAdditive_smul_coe, scale_one, AlgHom.coe_id,
      id_eq, forall_const]
  mul_smul := by
    simp only [Additive.forall, toAdditive_smul_coe, ← scale_scale_apply,
      AlgHom.coe_comp, Function.comp_apply, forall_const]
  smul_zero a := by
    rw [← ofMul_one, toAdditive_smul_coe, ← coe_scale_algHom, map_one]
  smul_add := by
    simp only [Additive.forall, toAdditive_smul_coe, ← ofMul_mul,
      ← coe_scale_algHom, map_mul, forall_const]

variable (R) in
/-- The R-module of exponential power series f ∈ R⟦X⟧
  satisfying f(X+Y) = f(X) f(Y) and f(0) = 1.
  The addition law is the multiplication of power series
  The scalar multiplication law is given by `PowerSeries.scale` -/
def ExponentialModule : AddSubmonoid (Additive R⟦X⟧) where
  carrier := { f : Additive (R⟦X⟧) | IsExponential (toMul f) }
  add_mem' {f g} hf hg := by
    rw [Set.mem_setOf_eq, toMul_add]
    exact isExponential_mul hf hg
  zero_mem' := by
    simp only [Set.mem_setOf_eq, toMul_zero]
    exact isExponential_one

def memExponentialModule_iff (f : R⟦X⟧) :
    ofMul f ∈ ExponentialModule R ↔ IsExponential f := by
  simp only [ExponentialModule, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    toMul_ofMul]

def memExponentialModule_iff' (f : Additive R⟦X⟧) :
    f ∈ ExponentialModule R ↔ IsExponential (toMul f) := by
  simp only [ExponentialModule, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

end PowerSeries

namespace ExponentialModule

open PowerSeries Additive

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- The coercion map from `ExponentialModule R` to `R⟦X⟧` -/
@[coe]
def toPowerSeries (f : ExponentialModule R) : R⟦X⟧ := toMul (f : Additive R⟦X⟧)

variable (R) in
instance instCoe : Coe (ExponentialModule R) R⟦X⟧ := ⟨toPowerSeries⟩

lemma coe_injective : Function.Injective ((↑) : ExponentialModule R → R⟦X⟧) :=
  fun f g ↦ by
    simp only [toPowerSeries, EmbeddingLike.apply_eq_iff_eq, SetLike.coe_eq_coe, imp_self]

@[simp, norm_cast]
lemma coe_inj {f g : ExponentialModule R} : (f : R⟦X⟧) = ↑g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
lemma coe_ext {f g : ExponentialModule R} (h : (f : R⟦X⟧) = ↑g) : f = g :=
  coe_injective h

@[simp]
theorem toMul_val_eq_coe {f : ExponentialModule R} :
    toMul (↑f : Additive R⟦X⟧) = ↑f := rfl

noncomputable instance instExponentialModule_smul :
    SMul A (ExponentialModule R) where
  smul r f := ⟨r • (f : Additive R⟦X⟧), by
    simp only [memExponentialModule_iff', toAdditive_smul_coe']
    exact isExponential_scale r f.prop⟩

theorem smul_def (r : A) (f : ExponentialModule R) :
  (r • f : ExponentialModule R) = r • (f : Additive R⟦X⟧) := rfl

noncomputable instance instExponentialModule_module :
    Module A (ExponentialModule R) where
  one_smul f := by rw [← Subtype.coe_inj, smul_def, one_smul]
  mul_smul r s f := by
    rw [← Subtype.coe_inj]
    simp only [smul_def, mul_smul]
  smul_zero r := by
    rw [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero, smul_zero]
  smul_add r f g := by
    rw [← Subtype.coe_inj]
    simp only [smul_def, AddSubmonoid.coe_add, smul_add]
  add_smul r s f := by
    rw [← Subtype.coe_inj]
    simp only [smul_def, AddSubmonoid.coe_add]
    apply Additive.toMul.injective
    simp only [toAdditive_smul_coe', toMul_add]
    exact isExponential_scale_add r s f.prop
  zero_smul f := by
    rw [← Subtype.coe_inj, smul_def]
    simp only [ZeroMemClass.coe_zero]
    apply Additive.toMul.injective
    simp only [toAdditive_smul_coe', scale_zero_apply, toMul_zero, f.prop.constantCoeff, map_one]

lemma coe_add (f g : ExponentialModule R) : (↑(f + g) : R⟦X⟧) = ↑f * ↑g := by
  simp only [toPowerSeries, AddSubmonoid.coe_add, toMul_add]

lemma coe_smul (r : A) (f : ExponentialModule R) :
    ((r • f) : ExponentialModule R) = scale r (f : R⟦X⟧) :=
  rfl

instance inst_exponentialModule_tower
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] :
    IsScalarTower R S (ExponentialModule S) where
  smul_assoc r s f := by
    apply coe_injective
    simp only [coe_smul]
    rw [← algebraMap_smul S, smul_eq_mul, ← scale_scale_apply]
    apply congr_fun
    ext f n
    simp only [coeff_scale, ← map_pow, algebraMap_smul]

lemma coe_ofMul (f : R⟦X⟧) (hf : IsExponential f) :
    ↑(⟨ofMul f, hf⟩ : ExponentialModule R) = f := rfl

lemma isExponential_coe (f : ExponentialModule R) :
    IsExponential (f : R⟦X⟧) := f.prop

lemma constantCoeff_coe (f : ExponentialModule R) :
    constantCoeff R (f : R⟦X⟧) = 1 := f.prop.constantCoeff

lemma add_mul_coe (f : ExponentialModule R) :
    subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (f : R⟦X⟧)
      = (subst (MvPowerSeries.X 0) (f : R⟦X⟧)) * (subst (MvPowerSeries.X 1) (f : R⟦X⟧)) :=
  f.prop.add_mul

lemma add_mul_coe' (f : ExponentialModule R) (p q : ℕ) :
    (p + q).choose p * (coeff R (p + q) (f : R⟦X⟧)) = coeff R p f * coeff R q f :=
  (isExponential_add_mul_iff (R := R) f).mp (add_mul_coe f) p q

variable {S : Type*} [CommRing S] [Algebra A S] (φ : R →ₐ[A] S)

def linearMap : ExponentialModule R →ₗ[A] ExponentialModule S where
  toFun := fun f ↦
    ⟨ofMul (PowerSeries.map φ (f : R⟦X⟧)), by
      simp [memExponentialModule_iff]
      exact isExponential_map (φ  : R →+* S) f.prop⟩
  map_add' := fun f g ↦ by
    apply coe_injective
    simp only [coe_add, map_mul, ofMul_mul]
    rfl
  map_smul' := fun a f ↦ by
    apply coe_injective
    simp only [coe_smul, RingHom.id_apply, coe_ofMul]
    rw [scale_map_eq_map_scale]

theorem coeff_linearMap (n : ℕ) (f : ExponentialModule R) :
    coeff S n (linearMap φ f) = φ (coeff R n f) := rfl

end ExponentialModule
