import KMiniPy.Verification.C16KbSubLoopSpec
import KMiniPy.Verification.C16KbSubLoop

theorem harborCheck : _root_.C16KbSubLoopSpec.statement :=
  fun a b => _root_.C16KbSubLoop.spec a b

#print axioms harborCheck
