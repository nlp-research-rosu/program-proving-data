import KMiniPy.Verification.C23KbSumUpSpec
import KMiniPy.Verification.C23KbSumUp

theorem harborCheck : _root_.C23KbSumUpSpec.statement :=
  fun n => _root_.C23KbSumUp.spec n

#print axioms harborCheck
