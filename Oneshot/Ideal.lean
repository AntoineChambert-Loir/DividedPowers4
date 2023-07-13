import Mathbin.RingTheory.Ideal.Basic
import Mathbin.RingTheory.Ideal.Operations

theorem Ideal.image_eq_map_of_surjective {A B : Type _} [Semiring A] [Semiring B] (f : A →+* B)
    (I : Ideal A) (hf : Function.Surjective f) : f '' I = I.map f :=
  by
  apply le_antisymm
  rintro b ⟨a, ha, rfl⟩
  simp only [SetLike.mem_coe]
  exact Ideal.mem_map_of_mem f ha
  intro b hb
  simp only [SetLike.mem_coe] at hb 
  apply Submodule.span_induction hb
  · exact fun x hx => hx
  · use 0; simp only [SetLike.mem_coe, Submodule.zero_mem, map_zero, eq_self_iff_true, and_self_iff]
  · rintro x y ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    use x + y
    simp only [SetLike.mem_coe] at hx hy ⊢
    simp only [I.add_mem hx hy, map_add, eq_self_iff_true, and_self_iff]
  · rintro b x ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := hf b
    use a • x
    constructor
    exact I.smul_mem a (set_like.mem_coe.mp hx)
    simp only [smul_eq_mul, map_mul]
#align ideal.image_eq_map_of_surjective Ideal.image_eq_map_of_surjective

