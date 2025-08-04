import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

open TensorProduct

namespace Submodule

/- Mathlib.LinearAlgebra.TensorProduct.Associator,
 Mathlib.Algebra.Algebra.Bilinear,
 Mathlib.LinearAlgebra.TensorProduct.DirectLimit]-/
theorem span_tensorProduct_eq_top_of_span_eq_top {R σ M S : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [Semiring S] [Algebra R S] (e : σ → M) (hm : span R (Set.range e) = ⊤) :
    (span S (Set.range fun s ↦ (1 : S) ⊗ₜ[R] e s) : Submodule S (S ⊗[R] M)) = ⊤ := by
  rw [eq_top_iff]
  intro m h
  induction m using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul r m =>
      let f : M →ₗ[R] S ⊗[R] M :=
        { toFun m       := (1 : S) ⊗ₜ[R] m
          map_add' x y  := by simp [tmul_add]
          map_smul' a x := by simp [tmul_smul] }
      suffices r ⊗ₜ[R] m = r • (1 : S) ⊗ₜ[R] m by
        have heq : (Set.range fun s ↦ 1 ⊗ₜ[R] e s) = ⇑f '' Set.range e := by
          conv_rhs => rw [← Set.image_univ, Set.image_image, Set.image_univ]
          simp [f]
        exact this ▸ smul_mem _ r (span_le_restrictScalars R _ _
          (heq ▸ apply_mem_span_image_of_mem_span f (hm ▸ mem_top)))
      rw [smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => exact Submodule.add_mem _ (hx mem_top) (hy mem_top)

end Submodule
