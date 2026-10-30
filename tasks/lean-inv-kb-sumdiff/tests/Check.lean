import KMiniPy.Verification.C20KbSumdiffSpec
import KMiniPy.Verification.C20KbSumdiff

theorem harborCheck : _root_.C20KbSumdiffSpec.statement :=
  fun a b => _root_.C20KbSumdiff.spec a b

#print axioms harborCheck
