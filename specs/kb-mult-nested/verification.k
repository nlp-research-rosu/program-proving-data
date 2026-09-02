requires "../../vendor/klever/src/semantics.k"

module KB-MULT-NESTED-VERIFICATION
  imports MPY
  imports MAP-SYMBOLIC
  syntax Expr ::= Val   // proof-only: a Val may sit in expression position (symbolic input N)
endmodule
