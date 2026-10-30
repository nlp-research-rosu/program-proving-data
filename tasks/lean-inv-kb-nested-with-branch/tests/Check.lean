import KMiniPy.Verification.C31KbNestedWithBranchSpec
import KMiniPy.Verification.C31KbNestedWithBranch

theorem harborCheck : _root_.C31KbNestedWithBranchSpec.statement :=
  fun a b => _root_.C31KbNestedWithBranch.spec a b

#print axioms harborCheck
