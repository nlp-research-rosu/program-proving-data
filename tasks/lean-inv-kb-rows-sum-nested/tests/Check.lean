import KMiniPy.Verification.C30KbRowsSumNestedSpec
import KMiniPy.Verification.C30KbRowsSumNested

theorem harborCheck : _root_.C30KbRowsSumNestedSpec.statement :=
  fun a b => _root_.C30KbRowsSumNested.spec a b

#print axioms harborCheck
