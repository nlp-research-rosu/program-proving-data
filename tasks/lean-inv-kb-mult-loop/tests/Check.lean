import KMiniPy.Verification.C21KbMultLoopSpec
import KMiniPy.Verification.C21KbMultLoop

theorem harborCheck : _root_.C21KbMultLoopSpec.statement :=
  fun n a => _root_.C21KbMultLoop.spec n a

#print axioms harborCheck
