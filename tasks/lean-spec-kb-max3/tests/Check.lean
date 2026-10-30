import KMiniPy.Verification.C17KbMax3Spec
import KMiniPy.Verification.C17KbMax3

theorem harborCheck : _root_.C17KbMax3Spec.statement :=
  fun a b n => _root_.C17KbMax3.spec a b n

#print axioms harborCheck
