requires "../../vendor/klever/src/semantics.k"

module KB-NESTED-WITH-BRANCH-VERIFICATION
  imports MPY
  imports MAP-SYMBOLIC
  syntax Expr ::= Val   // proof-only: a Val may sit in expression position (symbolic inputs A, B)

  // proof-only minInt collapse under NON-STRICT path facts: the stock domains.md
  // minInt equations require strict `I1 <Int I2` / `I1 >=Int I2`; after the branch
  // split the path carries the non-strict `i <=Int b` atom, which implies neither,
  // and deciding them makes z3 model-search a nonlinear div/mod context — it returns
  // unknown and kprove aborts (DecidePredicateUnknown). These are ordinary minInt
  // facts (at I1 ==Int I2 both produce the same value), fired on the atom the path
  // actually contains, ahead of the stock equations.
  rule minInt(I1:Int, I2:Int) => I1 requires I1 <=Int I2 [simplification(45)]
  rule minInt(I1:Int, I2:Int) => I2 requires I2 <=Int I1 [simplification(45)]
endmodule
