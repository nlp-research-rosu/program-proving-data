import KMiniPy.Verification.C6KbChainSpec
import KMiniPy.Verification.C6KbChain

theorem harborCheck : _root_.C6KbChainSpec.statement :=
  fun a => _root_.C6KbChain.spec a

#print axioms harborCheck
