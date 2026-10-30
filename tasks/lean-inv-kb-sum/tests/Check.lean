import KMiniPy.Verification.C14KbSumSpec
import KMiniPy.Verification.C14KbSum

theorem harborCheck : _root_.C14KbSumSpec.statement :=
  fun n sum => _root_.C14KbSum.spec n sum

#print axioms harborCheck
