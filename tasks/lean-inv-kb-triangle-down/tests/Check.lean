import KMiniPy.Verification.C22KbTriangleDownSpec
import KMiniPy.Verification.C22KbTriangleDown

theorem harborCheck : _root_.C22KbTriangleDownSpec.statement :=
  fun n => _root_.C22KbTriangleDown.spec n

#print axioms harborCheck
