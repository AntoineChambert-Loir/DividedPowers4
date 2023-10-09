import Oneshot.DividedPowers.DPAlgebra.Init
import Oneshot.MvPowerSeries.Order
import Oneshot.MvPowerSeries.Topology

variable (R : Type _) [CommSemiring R]

def IsExponential (f : ℕ → R) : Prop :=
  f 0 = 1 ∧ ∀ p q, f (p + q) = Nat.choose (p + q) q * f p * f q
#align is_exponential IsExponential

structure Exp (R : Type _) [Semiring R] where
  toFun : ℕ → R
  map_zero : to_fun 0 = 1
  map_add : ∀ p q, to_fun (p + q) = Nat.choose (p + q) q * to_fun p * to_fun q
#align Exp Exp

namespace Exp

instance funLike : FunLike (Exp R) ℕ fun _ => R
    where
  coe := Exp.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
#align Exp.fun_like Exp.funLike

@[simp]
theorem toFun_eq_coe {f : Exp R} : f.toFun = (f : ℕ → R) :=
  rfl
#align Exp.to_fun_eq_coe Exp.toFun_eq_coe

@[ext]
theorem ext {f g : Exp R} (h : ∀ n, f n = g n) : f = g :=
  FunLike.ext f g h
#align Exp.ext Exp.ext

protected def copy (f : Exp R) (f' : ℕ → R) (h : f' = f) : Exp R
    where
  toFun := f'
  map_zero := h.symm ▸ f.map_zero
  map_add := h.symm ▸ f.map_add
#align Exp.copy Exp.copy

def add : Exp R → Exp R → Exp R := fun f g =>
  { toFun := fun p => (Finset.Nat.antidiagonal p).Sum fun rs => f rs.1 * g rs.2
    map_zero := by
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, ← to_fun_eq_coe, map_zero,
        mul_one]
    map_add := by sorry }
#align Exp.add Exp.add

/- example : add_comm_group (Exp R) := {
  
} -/
--#print is_exponential
end Exp

