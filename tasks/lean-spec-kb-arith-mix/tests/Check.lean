import KMiniPy.Verification.C8KbArithMixSpec
import KMiniPy.Verification.C8KbArithMix

theorem harborCheck : _root_.C8KbArithMixSpec.statement :=
  fun a b => _root_.C8KbArithMix.spec a b

#print axioms harborCheck
