// Verification module shared by every K task: the untouched klever MPY
// semantics plus the symbolic map hooks. The one syntax extension lets a
// value sit in expression position, so a claim can write `Assign(Name("n"),
// N:Int)` with a symbolic integer N where the program had a literal.
requires "/opt/klever/src/semantics.k"

module MPY-VERIFICATION
  imports MPY
  imports MAP-SYMBOLIC
  syntax Expr ::= Val
endmodule
