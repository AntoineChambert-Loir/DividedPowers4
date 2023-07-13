import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations

theorem Ideal.image_eq_map_of_surjective {A B : Type _} [Semiring A] [Semiring B] (f : A →+* B)
    (I : Ideal A) (hf : Function.Surjective f) : f '' I = I.map f :=
  by
  apply le_antisymm
  rintro b ⟨a, ha, rfl⟩
  simp only [SetLike.mem_coe]
  exact Ideal.mem_map_of_mem f ha
  intro b hb
  rw [SetLike.mem_coe, Ideal.map, ← Ideal.submodule_span_eq] at hb 
  refine' Submodule.span_induction hb _ _ _ _ 
  · exact fun x hx => hx
  · use 0; simp only [SetLike.mem_coe, Submodule.zero_mem, map_zero, eq_self_iff_true, and_self_iff]
  · rintro x y ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    use x + y
    simp only [SetLike.mem_coe] at hx hy ⊢
    simp only [I.add_mem hx hy, map_add, eq_self_iff_true, and_self_iff]
  · rintro b _ ⟨x, ⟨hx, rfl⟩⟩
    obtain ⟨a, rfl⟩ := hf b
    use a • x
    constructor
    . exact I.smul_mem a (SetLike.mem_coe.mp hx)
    . simp only [smul_eq_mul, _root_.map_mul]
-- #align ideal.image_eq_map_of_surjective Ideal.image_eq_map_of_surjective

