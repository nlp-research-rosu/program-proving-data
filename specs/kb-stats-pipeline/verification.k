requires "../../vendor/klever/src/semantics.k"

module KB-STATS-PIPELINE-VERIFICATION
  imports MPY
  imports MAP-SYMBOLIC
  syntax Expr ::= Val   // proof-only: a Val may sit in expression position (symbolic inputs A, B, N)
endmodule
