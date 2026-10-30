import KMiniPy.Verification.C2AbsValSpec
import KMiniPy.Verification.C2AbsVal

theorem harborCheck : _root_.C2AbsValSpec.statement :=
  fun x => _root_.C2AbsVal.spec x

#print axioms harborCheck
