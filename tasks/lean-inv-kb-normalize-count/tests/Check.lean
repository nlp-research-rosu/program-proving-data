import KMiniPy.Verification.C34KbNormalizeCountSpec
import KMiniPy.Verification.C34KbNormalizeCount

theorem harborCheck : _root_.C34KbNormalizeCountSpec.statement :=
  fun a b n => _root_.C34KbNormalizeCount.spec a b n

#print axioms harborCheck
