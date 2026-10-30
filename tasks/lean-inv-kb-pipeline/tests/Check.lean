import KMiniPy.Verification.C32KbPipelineSpec
import KMiniPy.Verification.C32KbPipeline

theorem harborCheck : _root_.C32KbPipelineSpec.statement :=
  fun a b n => _root_.C32KbPipeline.spec a b n

#print axioms harborCheck
