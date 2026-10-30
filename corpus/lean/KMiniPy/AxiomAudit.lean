import KMiniPy.Concrete.A1SumToN
import KMiniPy.Concrete.A2Gcd
import KMiniPy.Concrete.A3CollatzSteps
import KMiniPy.Concrete.A4HalfOfEven
import KMiniPy.Symbolic.B1AbsVal
import KMiniPy.Symbolic.B2ClassifyTriangle
import KMiniPy.Verification.C1SumToN
import KMiniPy.Verification.C2AbsVal
import KMiniPy.Verification.C3Refutation
import KMiniPy.Verification.C4KbAssign
import KMiniPy.Verification.C5KbSwap
import KMiniPy.Verification.C6KbChain
import KMiniPy.Verification.C7KbDoubleHalf
import KMiniPy.Verification.C8KbArithMix
import KMiniPy.Verification.C9KbAbs
import KMiniPy.Verification.C10KbMax
import KMiniPy.Verification.C11KbMin
import KMiniPy.Verification.C12KbCountdown
import KMiniPy.Verification.C17KbMax3
import KMiniPy.Verification.C18KbClamp
import KMiniPy.Verification.C19KbAbsTimes
import KMiniPy.Verification.C13KbCountup
import KMiniPy.Verification.C14KbSum
import KMiniPy.Verification.C15KbAddLoop
import KMiniPy.Verification.C16KbSubLoop
import KMiniPy.Verification.C21KbMultLoop
import KMiniPy.Verification.C22KbTriangleDown
import KMiniPy.Verification.C23KbSumUp
import KMiniPy.Verification.C20KbSumdiff
import KMiniPy.Verification.C24KbCountEven
import KMiniPy.Verification.C25KbLoopMax
import KMiniPy.Verification.C32KbPipeline
import KMiniPy.Verification.C33KbStatsPipeline
import KMiniPy.Verification.C34KbNormalizeCount
import KMiniPy.Verification.C26KbPureNested
import KMiniPy.Verification.C27KbMultNested
import KMiniPy.Verification.C28KbTriangleNested
import KMiniPy.Verification.C29KbSquaresCubic
import KMiniPy.Verification.C30KbRowsSumNested
import KMiniPy.Verification.C31KbNestedWithBranch

/-! Axiom audit: every theorem below must print only Lean's core axioms
(`propext`, `Classical.choice`, `Quot.sound`) plus the two String-hook
declarations (klean's signature-only symbol and `eqStringHook` interpreting
it). `sorryAx` anywhere means a stub; a collection-hook axiom would mean a
prelude leak — the stock klean Prelude declares 41 of them, all unreachable. -/
#print axioms A1SumToN.trace
#print axioms A2Gcd.trace
#print axioms B1AbsVal.path_neg
#print axioms B1AbsVal.path_nonneg
#print axioms B2ClassifyTriangle.path_equilateral
#print axioms B2ClassifyTriangle.path_iso_ab
#print axioms B2ClassifyTriangle.path_iso_bc
#print axioms B2ClassifyTriangle.path_iso_ac
#print axioms B2ClassifyTriangle.path_scalene
#print axioms C1SumToN.gauss
#print axioms C2AbsVal.spec
#print axioms C3BuggyAbsAt0.trace
#print axioms A3CollatzSteps.trace
#print axioms A4HalfOfEven.trace
#print axioms C3Refutation.spec_refuted

-- Ported KleverBench problems (C4–C11): the RL `spec` mirror of each K
-- claim, plus the ∀-quantified path theorems it rests on.
#print axioms C4KbAssign.spec
#print axioms C4KbAssign.path_main
#print axioms C5KbSwap.spec
#print axioms C5KbSwap.path_main
#print axioms C6KbChain.spec
#print axioms C6KbChain.path_main
#print axioms C7KbDoubleHalf.spec
#print axioms C7KbDoubleHalf.path_main
#print axioms C8KbArithMix.spec
#print axioms C8KbArithMix.path_main
#print axioms C9KbAbs.spec
#print axioms C9KbAbs.path_neg
#print axioms C9KbAbs.path_nonneg
#print axioms C10KbMax.spec
#print axioms C10KbMax.path_le
#print axioms C10KbMax.path_gt
#print axioms C11KbMin.spec
#print axioms C11KbMin.path_le
#print axioms C11KbMin.path_gt
#print axioms C12KbCountdown.spec
#print axioms C12KbCountdownLegs.body_leg
#print axioms C13KbCountup.spec
#print axioms C13KbCountupLegs.body_leg
#print axioms C14KbSum.spec
#print axioms C14KbSumLegs.body_leg
#print axioms C15KbAddLoop.spec
#print axioms C15KbAddLoopLegs.body_leg
#print axioms C16KbSubLoop.spec
#print axioms C16KbSubLoopLegs.body_leg
#print axioms C21KbMultLoop.spec
#print axioms C21KbMultLoopLegs.body_leg
#print axioms C22KbTriangleDown.spec
#print axioms C22KbTriangleDownLegs.body_leg
#print axioms C23KbSumUp.spec
#print axioms C23KbSumUpLegs.body_leg
#print axioms C20KbSumdiff.spec
#print axioms C24KbCountEven.spec
#print axioms C25KbLoopMax.spec
#print axioms C32KbPipeline.spec
#print axioms C33KbStatsPipeline.spec
#print axioms C34KbNormalizeCount.spec
#print axioms C26KbPureNested.spec
#print axioms C26KbPureNested.inner_all
#print axioms C27KbMultNested.spec
#print axioms C27KbMultNested.inner_all
#print axioms C28KbTriangleNested.spec
#print axioms C28KbTriangleNested.inner_all
#print axioms C29KbSquaresCubic.spec
#print axioms C29KbSquaresCubic.inner_all
#print axioms C30KbRowsSumNested.spec
#print axioms C30KbRowsSumNested.inner_all
#print axioms C31KbNestedWithBranch.spec
#print axioms C31KbNestedWithBranch.inner_all
#print axioms C17KbMax3.spec
#print axioms C17KbMax3.path_le_le
#print axioms C17KbMax3.path_le_gt
#print axioms C17KbMax3.path_gt_le
#print axioms C17KbMax3.path_gt_gt
#print axioms C18KbClamp.spec
#print axioms C18KbClamp.path_neg
#print axioms C18KbClamp.path_hi
#print axioms C18KbClamp.path_mid
#print axioms C19KbAbsTimes.spec
#print axioms C19KbAbsTimes.path_neg
#print axioms C19KbAbsTimes.path_nonneg

-- `Reaches` corollaries of the trace theorems (one-liners over the audited
-- traces via the axiom-free `Reaches.of_rewrites`).
#print axioms A1SumToN.trace_reaches
#print axioms A2Gcd.trace_reaches
#print axioms A3CollatzSteps.trace_reaches
#print axioms A4HalfOfEven.trace_reaches
#print axioms C3BuggyAbsAt0.trace_reaches
