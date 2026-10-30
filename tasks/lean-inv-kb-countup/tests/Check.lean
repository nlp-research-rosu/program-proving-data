import KMiniPy.Verification.C13KbCountupSpec
import KMiniPy.Verification.C13KbCountup

theorem harborCheck : _root_.C13KbCountupSpec.statement :=
  fun n r => _root_.C13KbCountup.spec n r

#print axioms harborCheck
