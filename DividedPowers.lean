--import DividedPowers.Basic -- In PR #15657
import DividedPowers.PolynomialLaw.Basic -- mathlib's file for CommRing and AddCommGroup rather than CommSemiring and AddCommMonoid
import DividedPowers.PolynomialLaw.Basic2 -- the rest
import DividedPowers.ForMathlib.RingTheory.Congruence.Hom
import DividedPowers.BasicLemmas
import DividedPowers.DPAlgebra.BaseChange -- It uses sorry
-- import DividedPowers.DPAlgebra.Compatible -- TODO: uncomment  -- It uses sorry (depended on AlgebraComp)
-- import DividedPowers.DPAlgebra.Dpow -- TODO: uncomment It uses sorry (depended on RobyLemma5)
-- import DividedPowers.DPAlgebra.Envelope -- TODO: uncomment -- It uses sorry (depended on AlgebraComp)
import DividedPowers.DPAlgebra.Exponential
import DividedPowers.DPAlgebra.Graded.Basic
import DividedPowers.DPAlgebra.Graded.GradeOne
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.DPAlgebra.Init
import DividedPowers.DPAlgebra.Misc
import DividedPowers.DPAlgebra.PolynomialLaw -- It uses sorry
import DividedPowers.DPAlgebra.RobyLemma9
--import DividedPowers.DPMorphism --In PR #22318
import DividedPowers.ExponentialModule.Basic
import DividedPowers.Exponential
--import DividedPowers.ForMathlib.AlgebraLemmas -- In PR #22237, #22239 and #22240.
--import DividedPowers.ForMathlib.Algebra.MvPolynomial.Equiv -- In PR #15019
import DividedPowers.ForMathlib.Data.Nat.Factorial.NatCast
--import DividedPowers.ForMathlib.Bell -- -- In PR #15644
import DividedPowers.ForMathlib.GradedBaseChange
import DividedPowers.ForMathlib.GradedRingQuot
--import DividedPowers.ForMathlib.InfiniteSum.Basic -- In mathlib
--import DividedPowers.ForMathlib.InfiniteSum.Order -- In mathlib
import DividedPowers.ForMathlib.Lcoeff
import DividedPowers.ForMathlib.LinearAlgebra.OnSup
import DividedPowers.ForMathlib.RingTheory.AugmentationIdeal -- uses sorry.
--import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Evaluation -- In PR 15019
--import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.LinearTopology -- In PR #15007
--import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Order -- In PR #14983
--import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.PiTopology -- In PR #14866 and PR #14989
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.StronglySummable.Basic -- it uses sorry
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.StronglySummable.Topology
--import DividedPowers.ForMathlib.MvPowerSeries.Sandbox -- Test file, do not import here.
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Substitution
import DividedPowers.ForMathlib.RingTheory.Polynomial.Coeff
--import DividedPowers.ForMathlib.MvPowerSeries.Trunc -- In PR 20958
--import DividedPowers.ForMathlib.RingTheory.PowerSeries.Topology -- In PR #14866
--import DividedPowers.ForMathlib.RingTheory.PowerSeries.Evaluation -- In PR #15019
import DividedPowers.ForMathlib.RingTheory.PowerSeries.Substitution
import DividedPowers.ForMathlib.RingTheory.SubmoduleMem
import DividedPowers.ForMathlib.RingTheory.TensorProduct.LinearEquiv
import DividedPowers.ForMathlib.RingTheory.TensorProduct.MonoidAlgebra
import DividedPowers.ForMathlib.RingTheory.TensorProduct.MvPolynomial
import DividedPowers.ForMathlib.RingTheory.TensorProduct.Polynomial
import DividedPowers.ForMathlib.Topology.Algebra.LinearTopology
--import DividedPowers.ForMathlib.Topology.Algebra.TopologicallyNilpotent -- In PR #20971
import DividedPowers.IdealAdd
import DividedPowers.IdealAdd_v1 -- For comparison of definitions
import DividedPowers.Padic
--import DividedPowers.PolynomialLaw.Basic
import DividedPowers.PolynomialLaw.Coeff
import DividedPowers.PolynomialLaw.Homogeneous -- It has a sorry
import DividedPowers.RatAlgebra -- In PR #22322
import DividedPowers.SubDPIdeal
