import DividedPowers.PolynomialLaw.Coeff

universe u

variable (R : Type u) [CommSemiring R]

/- # Polynomial laws. -/

namespace PolynomialLaw

variable {R}

/- **MI** : The file now works assuming the weaker hypotheses `CommSemiring R`, `CommSemiring S`,
  `AddCommMonoid M`, `AddCommMonoid N`. -/

open Finset MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {ι N : Type*} {M : ι → Type u} [(i : ι) → AddCommMonoid (M i)]
  [(i : ι) → Module R (M i)] [AddCommMonoid N] [Module R N]

section Fintype

open LinearMap

variable [Fintype ι]

section generize

/-- Given `m : ι → Π i, M i`, `generize m` is the `R`-linear map sending `f : (Π i, M i) →ₚₗ[R] N`
to the term of `MvPolynomial ι R ⊗[R] N` obtained by applying `f.toFun (MvPolynomial ι R)` to the
sum `∑ i, X i ⊗ₜ[R] m i`. -/
noncomputable def multiGenerize (m : ι → Π i, M i):
    ((Π i, M i) →ₚₗ[R] N) →ₗ[R] MvPolynomial ι R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial ι R) (∑ i, X i ⊗ₜ[R] m i)
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

end generize

section coeff

variable [DecidableEq ι] (m : ι → Π i, M i) (k : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)

/-- The multi-coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def multiCoeff : ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N :=
  scalarRTensor.toLinearMap.comp (multiGenerize m)

end coeff

end Fintype
