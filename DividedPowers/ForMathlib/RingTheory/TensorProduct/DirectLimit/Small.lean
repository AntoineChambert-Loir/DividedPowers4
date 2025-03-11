import DividedPowers.ForMathlib.RingTheory.TensorProduct.DirectLimit.FG
import Mathlib.RingTheory.FiniteType

/- # Tensor products and small submodules

* `Submodules_small_equiv` proves that a module is the direct limit
of its finitely generated submodules, with respect to the inclusion maps

* `rTensor_smallEquiv` deduces that a tensor product `M ⊗[R] N`
is the direct limit of the modules `P ⊗[R] N`, for all finitely generated
submodules `P`, with respect to the maps deduced from the inclusions

## TODO

* Fix namespaces, add docstrings

* The results are valid in the context of `AddCommMonoid M` over a `Semiring`.
However,  tensor products in mathlib require commutativity of the scalars,
and direct limits of modules are restricted to modules over rings.

* Provide the analogous results for `lTensor`, and both sides at the same time.

-/

open Submodule LinearMap

section Semiring

universe u v
variable {R : Type u} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

-- [Mathlib.RingTheory.Finiteness.Defs]
theorem Submodule.FG.small [Small.{v} R] (P : Submodule R M) (hP : P.FG) : Small.{v} P := by
  rw [Submodule.fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.linearCombination'_range s]
  apply small_range

theorem Submodule.bot_small : Small.{v} (⊥ : Submodule R M) := by
  let f : Unit → (⊥ : Submodule R M) := fun _ ↦ 0
  have : Small.{v} Unit := small_lift Unit
  apply small_of_surjective (f := f)
  rintro ⟨x, hx⟩
  simp only [mem_bot] at hx
  use default
  simp [← Subtype.coe_inj, f, hx]

-- The directed system of small submodules of `M`
def DirectedSystem.Submodules_small :
    DirectedSystem (ι := {P : Submodule R M // Small.{v} P}) (F := fun P ↦ P.val)
    (f := fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

--[Mathlib.RingTheory.Finiteness.Basic, Mathlib.LinearAlgebra.Quotient.Basic]
theorem Submodule.small_sup {P Q : Submodule R M} (_ : Small.{v} P) (_ : Small.{v} Q) :
    Small.{v} (P ⊔ Q : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact small_range _

theorem small_finset {ι : Type*} [Small.{v} ι] : Small.{v} (Finset ι) :=
  small_of_injective (f := Finset.toSet) Finset.coe_injective

theorem Submodule.small_directSum
    {ι : Type*} {P : ι → Submodule R M} [Small.{v} ι] [∀ i, Small.{v} (P i)] :
    Small.{v} (Π₀ (i : ι), ↥(P i)) := by
  classical
  have : Small.{v} (Finset ι) := small_finset
  have (s : Finset ι) : Small.{v} (Π (i : s), P i) := small_Pi _
  let h : (Σ (s : Finset ι), (Π i : s, P i)) → Π₀ i, P i := fun sf ↦ by
    exact {
      toFun (i : ι) := if h : i ∈ sf.1.val then sf.2 ⟨i, h⟩ else 0
      support' := Trunc.mk ⟨sf.1.val, fun i ↦ by
        simp only [Finset.mem_val, dite_eq_right_iff]
        by_cases hi : i ∈ sf.1
        · exact Or.inl hi
        · apply Or.inr fun h ↦ False.elim (hi h)⟩}
  apply small_of_surjective (f := h)
  intro m
  use ⟨m.support, fun i ↦ m i⟩
  ext i
  simp only [Finset.mem_val, DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite, DFinsupp.coe_mk',
    ite_not, SetLike.coe_eq_coe, ite_eq_right_iff, h]
  simp only [eq_comm, imp_self, h]

theorem Submodule.small_iSup
    {ι : Type*} {P : ι → Submodule R M} (_ : Small.{v} ι) (_ : ∀ i, Small.{v} (P i)) :
    Small.{v} (iSup P : Submodule R M) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum]
  have : Small.{v} (Π₀ (i : ι), ↥(P i)) := Submodule.small_directSum
  apply small_range

instance : SemilatticeSup {P : Submodule R M // Small.{v} P} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, Submodule.small_sup P.property Q.property⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

instance : Inhabited {P : Submodule R M // Small.{v} P} where
  default := ⟨⊥, by
    let f : Unit → (⊥ : Submodule R M) := fun _ ↦ 0
    have : Small.{v} Unit := small_lift Unit
    apply small_of_surjective (f := f)
    rintro ⟨x, hx⟩
    simp only [mem_bot] at hx
    use default
    simp [← Subtype.coe_inj, f, hx]⟩

variable (R M) in
/-- Any module is the direct limit of its finitely generated submodules -/
noncomputable def Submodules_small_equiv
    [Small.{v} R] [DecidableEq {P : Submodule R M // Small.{v} P}] :
    Module.DirectLimit (ι := {P : Submodule R M // Small.{v} P})
      (G := fun P ↦ P.val)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P ↦ P.val.subtype) (fun _ _ _ _ ↦ rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P ↦ Submodule.injective_subtype P.val),
      fun x ↦ ⟨Module.DirectLimit.of _ {P : Submodule R M // Small.{v} P} _ _
          ⟨Submodule.span R {x}, Submodule.FG.small _ (fg_span_singleton x)⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩, by simp⟩⟩


end Semiring


section TensorProducts

open TensorProduct

universe v

variable (R : Type*) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

variable {R M N}

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all small submodules of `M`. -/
noncomputable def rTensor_small_equiv
    [Small.{v} R]  [DecidableEq {P : Submodule R M // Small.{v} P}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // Small.{v} P}) (fun P ↦ P.val ⊗[R] N)
      (fun ⦃P Q⦄ (h : P ≤ Q)  ↦ (Submodule.inclusion h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodules_small_equiv R M).rTensor N)

end TensorProducts

section Algebra

open MvPolynomial AlgHom

universe u v

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]

theorem MvPolynomial.aeval_range (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S]
    [Algebra R S] {σ : Type*} (s : σ → S) :
    (aeval s).range = Algebra.adjoin R (Set.range s) := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on' with
    | h1 d r =>
      simp only [aeval_monomial]
      apply mul_mem
      · exact Subalgebra.algebraMap_mem (Algebra.adjoin R (Set.range s)) r
      · apply prod_mem
        intro c _
        refine pow_mem (Algebra.adjoin_mono (s := {s c}) ?_ ?_) _
        · simp only [Set.singleton_subset_iff, Set.mem_range, exists_apply_eq_apply]
        · exact Algebra.self_mem_adjoin_singleton R (s c)
    | h2 p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  · rw [Algebra.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    use X i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

theorem Algebra.small_adjoin [Small.{u} R] {s : Set S} [Small.{u} s] :
    Small.{u} (Algebra.adjoin R s : Subalgebra R S) := by
  let j' := MvPolynomial.mapEquiv (Shrink.{u} s) (Shrink.ringEquiv R)
  have : Small.{u} (MvPolynomial (Shrink.{u} s) R) := small_of_surjective j'.surjective
  let j : MvPolynomial (Shrink.{u} s) R →ₐ[R] S := aeval (fun i ↦ (equivShrink s).symm i)
  have hj : adjoin R s = j.range := by
    rw [MvPolynomial.aeval_range, ← Function.comp_def]
    simp
  rw [hj]
  apply small_range (f := j)

/-   let A := MvPolynomial (Shrink.{u} s) R
  let j : A →ₐ[R] S := MvPolynomial.aeval (fun x ↦ (equivShrink s).symm x)
  have : Algebra.adjoin R s = j.range := by
    simp only [j]
    rw [MvPolynomial.aeval_range, ← Function.comp_def]
    simp
  rw [this]
  have htop: (⊤ : Submodule R A) =
      iSup  (fun d : Shrink.{u} s  →₀ ℕ ↦ LinearMap.range (MvPolynomial.monomial (R := R) d)) := by
    symm
    rw [eq_top_iff]
    intro a _
    induction a using MvPolynomial.induction_on' with
    | h1 d r => exact mem_iSup_of_mem d (mem_range_self (MvPolynomial.monomial d) r)
    | h2 p q hp hq => exact add_mem (hp Submodule.mem_top) (hq Submodule.mem_top)
  have _ : Small.{u} (⊤ : Submodule R A) := by
    simp_rw [htop]
    apply small_iSup (small_self _)
    intro d
    apply small_range
  have : Small.{u} A := small_of_surjective (f := Submodule.subtype (⊤ : Submodule R A))
    (fun a ↦ ⟨⟨a, Submodule.mem_top⟩, rfl⟩)
  apply small_range
-/

theorem Algebra.FiniteType.small [Small.{u} R] [Algebra.FiniteType R S] :
    Small.{u} S := by
  obtain ⟨s : Finset S, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  set j : MvPolynomial (Fin s.card) R →ₐ[R] S := aeval (fun i ↦ s.equivFin.symm i)
  set j' := MvPolynomial.mapEquiv (Fin s.card) (Shrink.ringEquiv R)
  apply small_of_surjective (f := j.toRingHom.comp j'.toRingHom)
  simp only [toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    EquivLike.surjective_comp]
  rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs]
  rw [MvPolynomial.aeval_range]
  apply Algebra.adjoin_mono
  exact fun i hi ↦ ⟨s.equivFin ⟨i, hi⟩, by simp⟩
/-  apply Algebra.adjoin_le
  intro x hx
  use X (s.equivFin ⟨x, hx⟩)
  simp only [toRingHom_eq_coe, RingHom.coe_coe, aeval_X, Equiv.symm_apply_apply, j]-/

theorem Subalgebra.FG.small [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG) :
    Small.{u} A := by
  have : Algebra.FiniteType R A := by
    exact (fg_iff_finiteType A).mp fgS
  apply Algebra.FiniteType.small (R := R) (S := A)

end Algebra

