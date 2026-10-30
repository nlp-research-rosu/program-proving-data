import KMiniPy.Verification.C4KbAssignSpec
import KMiniPy.Verification.C4KbAssign

theorem harborCheck : _root_.C4KbAssignSpec.statement :=
  fun a => _root_.C4KbAssign.spec a

#print axioms harborCheck
