import DividedPowers.DPAlgebra.Init
import DividedPowers.ExponentialModule.Basic
-- import DividedPowers.ForMathlib.MvPowerSeries.Order
-- import DividedPowers.ForMathlib.MvPowerSeries.Topology


/-! # Divided power algebra and exponential modules

Here we prove Theorem III.1 of [Roby1963].
M is an R-module
A is an R-algebra
There is an equivalence between
* algebra morphisms α : DividedPowerAlgebra R M →ₐ[R] A
* module morphisms β : M →ₗ[R] ExponentialModule (A)
which satisfies
  β m = ∑ α ( dp n m ) X ^ n
for all m : M

We define
- `DividedPowerAlgebra.exp` : the power series `∑ (dp n m) X ^ n

-/

variable (R : Type*) [CommRing R] {A : Type*} [CommSemiring A] [Algebra R A]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

namespace DividedPowerAlgebra

open PowerSeries Additive ExponentialModule

/-- The exponential power series of an element of a module, in the DividedPowerAlgebra -/
noncomputable def exp' (m : M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dp R n m)

lemma coeff_exp' (m : M) (n : ℕ) : coeff n (exp' R m) = dp R n m := by
  simp only [coeff_mk, exp']

theorem isExponential_exp' (m : M) : IsExponential (exp' R m) := by
  rw [isExponential_iff]
  constructor
  · intro p q
    simp only [coeff_exp', dp_mul, nsmul_eq_mul]
  · rw [← coeff_zero_eq_constantCoeff, coeff_exp', dp_zero]

/-- The exponential power series of an element of a module,
  in the ExponentialModule of the DividedPowerAlgebra -/
noncomputable def exp (m : M) : ExponentialModule (DividedPowerAlgebra R M) :=
  ⟨ofMul (exp' R m), isExponential_exp' R m⟩

theorem coe_exp (m : M) : ↑(exp R m) = exp' R m := rfl

theorem coeff_exp (m : M) (n : ℕ) : coeff n (exp R m) = dp R n m := by
  simp only [coe_exp, coeff_exp']

-- TODO : The following could serve as a definition of an exponential structure
-- this is equivalent to the combination of dpow_zero, dpow_add and dpow_smul

variable (M) in
/-- The exponential power series of an element of a module,
  valued in the ExponentialModule of the DividedPowerAlgebra,
  as a LinearMap -/
noncomputable def exp_LinearMap :
    M →ₗ[R] ExponentialModule (DividedPowerAlgebra R M) where
  toFun := exp R
  map_add' x y := by
    apply coe_injective
    ext n
    simp only [ExponentialModule.coe_add, coeff_exp, coeff_mul, dp_add]
  map_smul' r m := by
    apply coe_injective
    ext n
    simp only [coeff_exp, RingHom.id_apply]
    rw [← algebraMap_smul (DividedPowerAlgebra R M) r (exp R m),
      coe_smul, coeff_rescale, coeff_exp, ← map_pow, dp_smul]
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.smul_def, map_pow]


theorem coe_exp_LinearMap :
    ⇑(exp_LinearMap R M) = exp R := rfl

theorem coeff_exp_LinearMap (n : ℕ) (m : M) :
    coeff n (exp_LinearMap R M m) = dp R n m := by
  rw [coe_exp_LinearMap, coeff_exp]

variable {S : Type*} [CommRing S] [Algebra R S]

variable (M S) in
/-- The equivalence between
  algebra morphisms `DividedPowerAlgebra R M →ₐ[R] S` and
  linear maps `M →ₗ[R] ExponentialModule S`

  [Roby1963, theorem III.1] -/
noncomputable
def dividedPowerAlgebra_exponentialModule_equiv :
    (DividedPowerAlgebra R M →ₐ[R] S) ≃ (M →ₗ[R] ExponentialModule S) where
  toFun α := (linearMap α).comp (exp_LinearMap R M)
  invFun β := by
    apply DividedPowerAlgebra.lift' (f := fun (n, m) ↦ coeff n (β m))
    · intro m
      simp only [coeff_zero_eq_constantCoeff]
      exact constantCoeff_coe (β m)
    · intro n r m
      simp only [LinearMapClass.map_smul, coe_smul, coeff_rescale]
      rw [Algebra.smul_def, map_pow]
    · intro n p m
      simp only [nsmul_eq_mul]
      rw [(isExponential_iff.mp (isExponential_coe _)).1]
      -- TODO: add lemmas for product of coeff and constant coeff
    · intro n x y
      simp only [map_add, coe_add, coeff_mul]
  left_inv := by
    intro α
    simp only [LinearMap.coe_comp, Function.comp_apply]
    apply algHom_ext
    intro n m
    simp only [lift'_apply_dp]
    rw [coeff_linearMap]
    simp only [coeff_exp_LinearMap]
  right_inv := by
    intro β
    ext m n
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [coeff_linearMap]
    rw [coeff_exp_LinearMap]
    simp only [lift'_apply_dp]

variable {R} in
theorem dividedPowerAlgebra_exponentialModule_equiv_apply
    (α : DividedPowerAlgebra R M →ₐ[R] S) :
    dividedPowerAlgebra_exponentialModule_equiv R M S α = (linearMap α).comp (exp_LinearMap R M) :=
  rfl

variable {R} in
theorem dividedPowerAlgebra_exponentialModule_equiv_symm_apply
    (β : M →ₗ[R] ExponentialModule S) (n : ℕ) (m : M) :
    (dividedPowerAlgebra_exponentialModule_equiv R M S).symm β (dp R n m) = coeff n (β m) := by
  unfold dividedPowerAlgebra_exponentialModule_equiv
  simp only [Equiv.coe_fn_symm_mk, lift'_apply_dp]

section quotient

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (Q : Submodule R M)

def J : Ideal (DividedPowerAlgebra R M) := Ideal.span
  (Set.range (fun (nq : ℕ × Q) ↦ dp R (nq.1 + 1) (nq.2 : M)))

theorem coeff_linearMap (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (x : ExponentialModule A) (n : ℕ) :
  coeff n ((linearMap f x) : B⟦X⟧) = f (coeff n (x : A⟦X⟧)) :=
  rfl

lemma coe_zero_eq_one (A : Type*) [CommRing A] :
    ((0 : ExponentialModule A) : A⟦X⟧) = 1 := by
  rfl

theorem ker_linearMap_mk_exp_LinearMap :
    Q ≤ LinearMap.ker (linearMap (S := DividedPowerAlgebra R M ⧸ (J Q)) (Ideal.Quotient.mkₐ R (J Q)) ∘ₗ exp_LinearMap R M) := fun q hq ↦ by
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
  ext n
  simp only [coeff_linearMap, coeff_exp_LinearMap, Ideal.Quotient.mkₐ_eq_mk, coe_zero_eq_one,
    coeff_one]
  split_ifs with hn
  · simp [hn, dp_zero] -- make dp_zero @[simp] ?
  · rw [Ideal.Quotient.eq_zero_iff_mem, J]
    apply Ideal.subset_span
    simp only [Set.mem_range, Prod.exists, Subtype.exists, exists_prop]
    use n.pred, q, hq
    congr
    exact (Nat.succ_pred_eq_of_ne_zero hn)

noncomputable def esymm :
    DividedPowerAlgebra R (M ⧸ Q) →ₐ[R] DividedPowerAlgebra R M ⧸ (J Q) :=
  (dividedPowerAlgebra_exponentialModule_equiv R (M ⧸ Q) (DividedPowerAlgebra R M ⧸ (J Q))).symm (
  Q.liftQ ((linearMap (Ideal.Quotient.mkₐ R (J Q))).comp (exp_LinearMap R M)) (by exact ker_linearMap_mk_exp_LinearMap Q))

theorem esymm_dp (n : ℕ) (m : M) :
    esymm Q (dp R n (Q.mkQ m)) = Ideal.Quotient.mk _ (dp R n m) := by
  simp only [esymm]
  simp only [Submodule.mkQ_apply]
  rw [dividedPowerAlgebra_exponentialModule_equiv_symm_apply]
  simp [coeff_linearMap, coeff_exp_LinearMap]

noncomputable def e :
    DividedPowerAlgebra R M ⧸ (J Q) →ₐ[R] (DividedPowerAlgebra R (M ⧸ Q)) := by
  let h := Ideal.Quotient.mkₐ R (J Q)
  apply Ideal.Quotient.liftₐ (J Q) (LinearMap.lift R Q.mkQ)
  suffices J Q ≤ RingHom.ker (LinearMap.lift R Q.mkQ) by
    intro a ; apply this
  rw [J]
  rw [Ideal.span_le]
  rintro x ⟨⟨n, q⟩, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  simp only [LinearMap.lift_apply_dp]
  suffices Q.mkQ (q : M) = 0 by
    rw [this]
    apply dp_null_of_ne_zero R
    exact Ne.symm (Nat.zero_ne_add_one n)
  aesop

theorem e_dp (n : ℕ) (m : M) :
    (e Q) ((Ideal.Quotient.mk (J Q)) (dp R n m)) = dp R n (Q.mkQ m) := by
  simp [e, LinearMap.lift_apply_dp]

noncomputable def dividedPowerAlgebra_quotient_equiv :
    (DividedPowerAlgebra R M ⧸ (J Q)) ≃ₐ[R] DividedPowerAlgebra R (M ⧸ Q) := by
  apply AlgEquiv.ofAlgHom (e Q) (esymm Q)
  · rw [algHom_ext_iff]
    rintro n ⟨m⟩
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    rw [show Quot.mk ⇑Q.quotientRel m = ⇑Q.mkQ m from by rfl,
      esymm_dp, e_dp]
  · apply Ideal.Quotient.algHom_ext
    rw [algHom_ext_iff]
    intro n m
    simp only [AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, Submodule.mkQ_apply, e_dp]
    rw [show Submodule.Quotient.mk m = Q.mkQ m from by rfl, esymm_dp]
    simp

end quotient
end DividedPowerAlgebra
