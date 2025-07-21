import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.DirectSum.Decomposition


/-! # Base change of graded modules and graded algebras -/

variable {ι R S M N A σ : Type*}

section

open TensorProduct

variable
    [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [Semiring S] [Algebra R S]
    [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Lift an `R`-linear map to an `S`-linear map -/
noncomputable def LinearMap.baseChange.lift
    (f : M →ₗ[R] N) : S ⊗[R] M →ₗ[S] N :=
  AlgebraTensorModule.lift (toSpanSingleton S (M →ₗ[R] N) f)

theorem LinearMap.baseChange.lift.tmul {f : M →ₗ[R] N} (s : S) (m : M) :
    LinearMap.baseChange.lift f (s ⊗ₜ[R] m) = s • (f m) := by
  simp [LinearMap.baseChange.lift]

/-- Canonical map of a module to its base change -/
noncomputable def LinearMap.baseChange.include : M →ₗ[R] S ⊗[R] M where
      toFun m := 1 ⊗ₜ[R] m
      map_add' x y := by simp only [tmul_add]
      map_smul' s x := by simp only [tmul_smul, RingHom.id_apply]

/-- Canonical map of a submodule to its base change (as a submodule) -/
noncomputable def Submodule.baseChange.include (N : Submodule R M) :
    N →ₗ[R] Submodule.baseChange S N where
  toFun n := ⟨1 ⊗ₜ[R] n, Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.coe_mem n)⟩
  map_add' x y := by simp [tmul_add]
  map_smul' r x := by simp

theorem Submodule.baseChange_eq_range
    {R : Type u_1} {M : Type u_2} (A : Type u_3) [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] (p : Submodule R M):
    Submodule.baseChange A p =
      LinearMap.range (LinearMap.baseChange A p.subtype) := by
ext x
constructor
· simp only [Submodule.baseChange_eq_span]
  intro hx
  apply Submodule.span_induction
    (p := fun x _ ↦ (x ∈ LinearMap.range (LinearMap.baseChange A p.subtype))) _ (zero_mem _)
    (fun _ _ _ _ hx hy ↦ add_mem hx hy) (fun a _ _ hx ↦ Submodule.smul_mem _ a hx) hx
  rintro _ ⟨x, hx, rfl⟩
  simp only [mk_apply, LinearMap.mem_range]
  use 1 ⊗ₜ[R] (⟨x, hx⟩ : p)
  simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype]
· rintro ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, coe_subtype]
    exact tmul_mem_baseChange_of_mem a (coe_mem x)
  | add x y hx hy =>
    simp only [map_add]
    exact add_mem hx hy

end

section decompose

open TensorProduct DirectSum

variable [CommSemiring R]
variable [CommSemiring S] [Algebra R S]
variable [DecidableEq ι] [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M) [Decomposition ℳ]

/-- The components of a graded module, as linear maps -/
def DirectSum.Decomposition.component (i : ι) : M →ₗ[R] (ℳ i) :=
  (DirectSum.component R ι (fun i ↦ ℳ i) i).comp  (decomposeLinearEquiv ℳ).toLinearMap

/-- The decomposition of the base change of a graded module (as linear map) -/
noncomputable def DirectSum.Decompose.baseChange.decompose :
    S ⊗[R] M →ₗ[S] ⨁ (i : ι), ↥(Submodule.baseChange S (ℳ i)) := by
  apply LinearMap.baseChange.lift
  apply LinearMap.comp ?_ (decomposeLinearEquiv ℳ).toLinearMap
  refine toModule R ι (⨁ (i : ι), ↥(Submodule.baseChange S (ℳ i))) ?_
  intro i
  exact LinearMap.comp
    (DirectSum.lof R ι (fun i ↦ (Submodule.baseChange S (ℳ i))) i)
    (Submodule.baseChange.include (ℳ i))

theorem DirectSum.Decompose.baseChange.decompose_tmul_of (s : S) (i : ι) (m : ℳ i) :
    DirectSum.Decompose.baseChange.decompose ℳ (s ⊗ₜ[R] m) =
      DirectSum.of  (fun i ↦ Submodule.baseChange S (ℳ i)) i ⟨s ⊗ₜ[R] m,
        Submodule.tmul_mem_baseChange_of_mem s (Submodule.coe_mem m)⟩ := by
  unfold DirectSum.Decompose.baseChange.decompose
  rw [LinearMap.baseChange.lift.tmul]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    decomposeLinearEquiv_apply, decompose_coe]
  rw [← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  simp only [Submodule.baseChange.include]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [DirectSum.lof_eq_of, ← DirectSum.lof_eq_of S, ← LinearMap.map_smul _ s, DirectSum.lof_eq_of]
  apply congr_arg
  simp only [SetLike.mk_smul_mk, Subtype.mk.injEq]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem Decompose.baseChange.decompose_of_mem {m : S ⊗[R] M} {i : ι}
    (hm : m ∈ Submodule.baseChange S (ℳ i)) :
    (Decompose.baseChange.decompose ℳ) m =
      (of (fun i ↦ ↥(Submodule.baseChange S (ℳ i))) i) ⟨m, hm⟩ := by
  simp only [Submodule.baseChange_eq_span] at hm
  apply Submodule.span_induction (p := fun m hm ↦ Decompose.baseChange.decompose ℳ m =
    of (fun i ↦ Submodule.baseChange S (ℳ i)) i ⟨m, Submodule.baseChange_eq_span S (ℳ i) ▸ hm⟩)
  · rintro _ ⟨x, hx : x ∈ ℳ i, rfl⟩
    simp only [mk_apply]
    -- why doesn't `rw [← Submodule.coe_mk x hx]` work?
    suffices ∃ (m : ℳ i), x = ↑m by
      obtain ⟨m, rfl⟩ := this
      rw [Decompose.baseChange.decompose_tmul_of]
    use ⟨x, hx⟩
  · rw [← DirectSum.lof_eq_of S, map_zero, eq_comm]
    convert LinearMap.map_zero _
  · intro x hx y hy px py
    rw [LinearMap.map_add, px, py, eq_comm]
    simp only [← DirectSum.lof_eq_of S]
    convert LinearMap.map_add _ _ _
    simp only [AddMemClass.mk_add_mk]
  · intro s x hx px
    rw [LinearMap.map_smul, px, eq_comm]
    simp only [← DirectSum.lof_eq_of S]
    convert LinearMap.map_smul _ _ _
    simp only [SetLike.mk_smul_mk]
  · exact hm

/-- Base change of a graded module -/
noncomputable def DirectSum.Decomposition.baseChange [Decomposition ℳ] :
    Decomposition (fun i => (ℳ i).baseChange S) where
      decompose' := DirectSum.Decompose.baseChange.decompose ℳ
      left_inv m := by
        induction m using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul s m =>
          induction m using DirectSum.Decomposition.inductionOn ℳ with
          | zero => simp only [tmul_zero, map_zero]
          | @homogeneous i m =>
            simp [Decompose.baseChange.decompose_tmul_of]
          | add m m' hm hm' => simp [TensorProduct.tmul_add, map_add, hm, hm']
        | add x y hx hy => simp [map_add, hx, hy]
      right_inv m := by
        induction m using DirectSum.induction_on with
        | zero => simp only [map_zero]
        | of i m =>
          simp only [coeAddMonoidHom_of]
          rcases m with ⟨m, hm⟩
          rw [Decompose.baseChange.decompose_of_mem ℳ hm]
        | add m m' hm hm' => simp [map_add, hm, hm']

end decompose

section algebra

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
variable [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable [CommSemiring S] [Algebra R S]

open TensorProduct

noncomputable def GradedAlgebra.baseChange :
  GradedAlgebra (fun i ↦ Submodule.baseChange S (𝒜 i)) where
    toDecomposition := DirectSum.Decomposition.baseChange 𝒜
    one_mem := Submodule.tmul_mem_baseChange_of_mem (1 : S) SetLike.GradedOne.one_mem
    mul_mem := fun i j gi gj hi hj ↦ by
      simp only [Submodule.baseChange_eq_span] at hi hj
      apply Submodule.span_induction (p := fun gj _ ↦ gi * gj ∈ Submodule.baseChange S _) _ _ _ _ hj
      · rintro _ ⟨y, hy, rfl⟩
        simp only [mk_apply]
        apply Submodule.span_induction (p := fun gi _ ↦ gi * _ ∈ _) _ _ _ _ hi
        rintro _ ⟨x, hx, rfl⟩
        · simp only [mk_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          exact Submodule.tmul_mem_baseChange_of_mem 1 (SetLike.GradedMul.mul_mem hx hy)
        · simp
        · intro a b _ _ ha hb
          rw [add_mul]
          exact add_mem ha hb
        · intro s a _ ha
          rw [← smul_eq_mul, smul_assoc]
          apply Submodule.smul_mem
          simp only [smul_eq_mul, ha]
      · simp
      · intro a b _ _ ha hb
        rw [mul_add]
        exact add_mem ha hb
      · intro s a _ ha
        rw [← smul_eq_mul, smul_comm]
        apply Submodule.smul_mem
        simp only [smul_eq_mul, ha]
