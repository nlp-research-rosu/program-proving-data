import KMiniPy.Verification.C5KbSwapSpec
import KMiniPy.Verification.C5KbSwap

theorem harborCheck : _root_.C5KbSwapSpec.statement :=
  fun a b => _root_.C5KbSwap.spec a b

#print axioms harborCheck
