import KMiniPy.Verification.C29KbSquaresCubicSpec
import KMiniPy.Verification.C29KbSquaresCubic

theorem harborCheck : _root_.C29KbSquaresCubicSpec.statement :=
  fun n => _root_.C29KbSquaresCubic.spec n

#print axioms harborCheck
