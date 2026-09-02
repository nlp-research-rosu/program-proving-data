requires "../../vendor/klever/src/semantics.k"

module BUGGY-ABS-VERIFICATION
  imports MPY
  imports MAP-SYMBOLIC
  syntax Expr ::= Val   // proof-only: a Val may sit in expression position (symbolic arg X)
endmodule
