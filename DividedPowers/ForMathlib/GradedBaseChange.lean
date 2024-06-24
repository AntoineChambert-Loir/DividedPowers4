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

end

section decompose

open TensorProduct DirectSum

variable [CommRing R]
variable [CommRing S] [Algebra R S]
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

/-- Base change of a graded module -/
noncomputable def DirectSum.Decomposition.baseChange [Decomposition ℳ] :
    Decomposition (fun i => (ℳ i).baseChange S) where
      decompose' := DirectSum.Decompose.baseChange.decompose ℳ
      left_inv m := by
        induction m using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul s m =>
          induction m using DirectSum.Decomposition.inductionOn ℳ with
          | h_zero => simp only [tmul_zero, map_zero]
          | @h_homogeneous i m =>
            simp [Decompose.baseChange.decompose_tmul_of]
          | h_add m m' hm hm' => simp [TensorProduct.tmul_add, map_add, hm, hm']
        | add x y hx hy => simp [map_add, hx, hy]
      right_inv m := by
        induction m using DirectSum.induction_on with
        | H_zero => simp only [map_zero]
        | H_basic i m =>
          rcases m with ⟨m, hm⟩
          simp only [coeAddMonoidHom_of]
          simp only [Submodule.baseChange] at hm
          apply Submodule.span_induction' (p := fun m hm ↦ Decompose.baseChange.decompose ℳ m = of (fun i ↦ Submodule.baseChange S (ℳ i)) i ⟨m, hm⟩)
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
            simp only [AddSubmonoid.mk_add_mk, Submodule.map_coe]
          · intro s x hx px
            rw [LinearMap.map_smul, px, eq_comm]
            simp only [← DirectSum.lof_eq_of S]
            convert LinearMap.map_smul _ _ _
            simp only [SetLike.mk_smul_mk, Submodule.map_coe]
        | H_plus m m' hm hm' => simp [map_add, hm, hm']

end decompose


variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
