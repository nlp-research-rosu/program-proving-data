import KMiniPy.Verification.C28KbTriangleNestedSpec
import KMiniPy.Verification.C28KbTriangleNested

theorem harborCheck : _root_.C28KbTriangleNestedSpec.statement :=
  fun n => _root_.C28KbTriangleNested.spec n

#print axioms harborCheck
