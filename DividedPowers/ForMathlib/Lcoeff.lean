import Mathlib.Algebra.MvPolynomial.Basic

variable {ι : Type*}
variable (R : Type*) [CommSemiring R]
def MvPolynomial.lcoeff' (k : ι →₀ ℕ) : MvPolynomial ι R →ₗ[R] R where
  toFun     := coeff k
  map_add'  := coeff_add k
  map_smul' := coeff_smul k

theorem MvPolynomial.lcoeff_apply' (k : ι →₀ ℕ) (f : MvPolynomial ι R) :
    lcoeff R k f = coeff k f := rfl
