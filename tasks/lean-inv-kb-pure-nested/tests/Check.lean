import KMiniPy.Verification.C26KbPureNestedSpec
import KMiniPy.Verification.C26KbPureNested

theorem harborCheck : _root_.C26KbPureNestedSpec.statement :=
  fun a b => _root_.C26KbPureNested.spec a b

#print axioms harborCheck
