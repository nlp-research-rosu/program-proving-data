import KMiniPy.Verification.C19KbAbsTimesSpec
import KMiniPy.Verification.C19KbAbsTimes

theorem harborCheck : _root_.C19KbAbsTimesSpec.statement :=
  fun a b => _root_.C19KbAbsTimes.spec a b

#print axioms harborCheck
