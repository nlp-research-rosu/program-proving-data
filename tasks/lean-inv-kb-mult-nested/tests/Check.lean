import KMiniPy.Verification.C27KbMultNestedSpec
import KMiniPy.Verification.C27KbMultNested

theorem harborCheck : _root_.C27KbMultNestedSpec.statement :=
  fun a b => _root_.C27KbMultNested.spec a b

#print axioms harborCheck
