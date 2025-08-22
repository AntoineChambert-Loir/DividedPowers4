import DividedPowers.PolynomialLaw.Basic2

/-

# Base Change

The goal is to define a base change map
  `PolynomialLaw R M N →ₗ[R] PolynomialLaw R' (R' ⊗[R] M) (R' ⊗[R] N)``
when M and N are R-modules and R' is an R-algebra (commutative)

This requires to simplify the tensor product
  `S' ⊗[R'] (R' ⊗[R] M)`
to
  `S' ⊗[R] M`

an S'-isomorphism which Mathlib doesn't know (yet)

What follows is draft

Prove that coeff, multiCoeff, biCoeff commute with base change

Compare ground

(Maybe) commSemiring the file

-/

open TensorProduct

universe u v w
variable {R : Type u} [CommRing R]
  {M : Type*}  [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

variable {R' : Type v} [CommRing R'] [Algebra R R']
variable {S' : Type w} [CommRing S'] [Algebra R' S']

variable [Algebra R S'] [IsScalarTower R R' S']

-- variant of `Algebra.TensorProdyct.includeRight`
noncomputable def baseChange_include : M →ₗ[R] R' ⊗[R] M := {
  toFun     := fun m ↦ 1 ⊗ₜ[R] m
  map_add'  := fun x y ↦ TensorProduct.tmul_add 1 x y
  map_smul' := fun r m  ↦ by
    simp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, ← TensorProduct.smul_tmul]
    rfl }

-- Try to use some module analogue of Algebra.TensorProduct.assoc and Algebra.TensorProduct.rid.

example : S' ⊗[R'] (R' ⊗[R] M) →ₗ[S'] S' ⊗[R] M := by
  apply TensorProduct.AlgebraTensorModule.lift {
    toFun := fun s' ↦ {
      toFun := TensorProduct.lift {
        toFun := fun r' ↦ r' • baseChange_include
        map_add' := fun a b ↦ by simp only [add_smul]
        map_smul' := fun a b ↦ by
          simp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, smul_assoc] }
      map_add' := fun x y ↦ by rw [map_add]
      map_smul' := fun r x ↦ by
        simp only [RingHom.id_apply]
        sorry }
    map_add'  := fun x y ↦ by
      sorry
    map_smul' := sorry
  }

example : S' ⊗[R'] (R' ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M := by
  sorry

--Universe error
def baseChange (f : PolynomialLaw R M N) : PolynomialLaw R' (R' ⊗[R] M) (R' ⊗[R] N) where
  toFun' S' _ _ := by
    /- have : Algebra R S' := RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    let fS' := toFun' f S'
    let u := Algebra.TensorProduct.rid R' S' -/

    sorry
  isCompat' := sorry

end BaseChange


end PolynomialLaw

end
