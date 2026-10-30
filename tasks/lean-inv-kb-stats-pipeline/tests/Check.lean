import KMiniPy.Verification.C33KbStatsPipelineSpec
import KMiniPy.Verification.C33KbStatsPipeline

theorem harborCheck : _root_.C33KbStatsPipelineSpec.statement :=
  fun a b n => _root_.C33KbStatsPipeline.spec a b n

#print axioms harborCheck
