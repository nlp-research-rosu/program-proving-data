import KMiniPy.Verification.C24KbCountEvenSpec
import KMiniPy.Verification.C24KbCountEven

theorem harborCheck : _root_.C24KbCountEvenSpec.statement :=
  fun n => _root_.C24KbCountEven.spec n

#print axioms harborCheck
