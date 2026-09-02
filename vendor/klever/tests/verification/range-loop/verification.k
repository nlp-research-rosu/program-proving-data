requires "../../../src/semantics.k"

module RANGE-LOOP-VERIFICATION
  imports MPY
  imports MAP-SYMBOLIC
  syntax Expr ::= Val   // proof-only: a Val may sit in expression position (symbolic arg N)
endmodule
