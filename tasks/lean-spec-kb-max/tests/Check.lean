import KMiniPy.Verification.C10KbMaxSpec
import KMiniPy.Verification.C10KbMax

theorem harborCheck : _root_.C10KbMaxSpec.statement :=
  fun a b => _root_.C10KbMax.spec a b

#print axioms harborCheck
