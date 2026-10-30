import KMiniPy.Verification.C18KbClampSpec
import KMiniPy.Verification.C18KbClamp

theorem harborCheck : _root_.C18KbClampSpec.statement :=
  fun a => _root_.C18KbClamp.spec a

#print axioms harborCheck
