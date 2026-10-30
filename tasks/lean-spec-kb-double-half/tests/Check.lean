import KMiniPy.Verification.C7KbDoubleHalfSpec
import KMiniPy.Verification.C7KbDoubleHalf

theorem harborCheck : _root_.C7KbDoubleHalfSpec.statement :=
  fun a => _root_.C7KbDoubleHalf.spec a

#print axioms harborCheck
