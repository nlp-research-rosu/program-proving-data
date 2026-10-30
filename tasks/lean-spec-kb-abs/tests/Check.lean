import KMiniPy.Verification.C9KbAbsSpec
import KMiniPy.Verification.C9KbAbs

theorem harborCheck : _root_.C9KbAbsSpec.statement :=
  fun a => _root_.C9KbAbs.spec a

#print axioms harborCheck
