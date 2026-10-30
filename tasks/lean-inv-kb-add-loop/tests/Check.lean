import KMiniPy.Verification.C15KbAddLoopSpec
import KMiniPy.Verification.C15KbAddLoop

theorem harborCheck : _root_.C15KbAddLoopSpec.statement :=
  fun n res a => _root_.C15KbAddLoop.spec n res a

#print axioms harborCheck
