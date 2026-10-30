import KMiniPy.Verification.C11KbMinSpec
import KMiniPy.Verification.C11KbMin

theorem harborCheck : _root_.C11KbMinSpec.statement :=
  fun a b => _root_.C11KbMin.spec a b

#print axioms harborCheck
