import Mathlib.GroupTheory.GroupAction.Hom

section SMul

variable (R : Type*) (S : Type*) (smulRS : SMul R S) (smulRS' : SMul R S) (r : R) (x : S)
    (h : smulRS = smulRS')

lemma smulRS_eq (h : smulRS = smulRS') : @SMul.smul R S smulRS r x = @SMul.smul R S smulRS' r x := by
  rw [h]

def foo' (h : smulRS = smulRS') :
    @MulActionHom R R id S smulRS S smulRS' :=
  @MulActionHom.mk _ _ _ _ (_) _ (_) (fun x => x) (fun _ _ => h ▸ rfl)

#check foo'
-- doesn't work
def foo' (h : smulRS = smulRS') : @MulActionHom R R id S smulRS S smulRS' where
  toFun := id
  map_smul' r x : @SMul.smul R S smulRS r x = @SMul.smul R S smulRS' r x := sorry

end SMul



#exit

section Algebra

variable (R : Type*) (S : Type*)
    [CommSemiring R]
    [CommSemiring S]
    (alg3 : Algebra R S) (alg4 : Algebra R S) (r : R) (x : S)
    (h : alg3 = alg4)

lemma smul_eq : @SMul.smul R S alg3.toSMul r x = @SMul.smul R S alg4.toSMul r x := sorry

#check smul_eq

example (r : R) : alg3.algebraMap r = alg4.algebraMap r := by
  rw [h]

variable (f : @LinearMap R R _ _ (RingHom.id R) S S _ _ alg3.toModule alg4.toModule)

#check f.map_smul'

#check  @LinearMap R R _ _ (RingHom.id R) S S _ _ alg3.toModule alg4.toModule

def foo'' : @AddHom S S _ _  := AddHom.id S

set_option trace.Meta.synthInstance true in
def foo' : @MulActionHom R R id S alg3.toSMul S alg4.toSMul := {
  AddHom.id S with
  map_smul' r x : @SMul.smul R S alg3.toSMul r x = @SMul.smul R S alg4.toSMul r x :=
    smul_eq R S alg3 alg4 r x}

end Algebra
