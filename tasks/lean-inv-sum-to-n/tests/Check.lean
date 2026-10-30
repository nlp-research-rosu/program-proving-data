import KMiniPy.Verification.C1SumToNSpec
import KMiniPy.Verification.C1SumToN

theorem harborCheck : _root_.C1SumToNSpec.statement :=
  fun n => _root_.C1SumToN.gauss n

#print axioms harborCheck
