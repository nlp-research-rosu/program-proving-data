import KMiniPy.Verification.C25KbLoopMaxSpec
import KMiniPy.Verification.C25KbLoopMax

theorem harborCheck : _root_.C25KbLoopMaxSpec.statement :=
  fun a n => _root_.C25KbLoopMax.spec a n

#print axioms harborCheck
