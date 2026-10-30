import KMiniPy.Verification.C12KbCountdownSpec
import KMiniPy.Verification.C12KbCountdown

theorem harborCheck : _root_.C12KbCountdownSpec.statement :=
  fun n => _root_.C12KbCountdown.spec n

#print axioms harborCheck
