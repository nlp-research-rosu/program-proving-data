// reference/src/semantics/comprehension.k — MPY-COMPREHENSION

module MPY-COMPREHENSION
  imports MPY-CORE
  imports MPY-OPERATORS
  imports MPY-LIST
  imports MPY-CONTROLS
  imports MPY-FUNCTIONS

  // A comprehension is pure syntactic sugar
  rule ListComp(ELT:Expr, Gs:CompFors) => Call(closureExpr(.ParamNames, compBody(Gs, ELT)), .Exprs)
  rule GenExp(ELT:Expr, Gs:CompFors)   => Call(closureExpr(.ParamNames, compBody(Gs, ELT)), .Exprs)

  syntax Stmts ::= compBody(CompFors, Expr) [macro]
  rule compBody(Gs:CompFors, ELT:Expr)
    => Assign(Name("$acc"), ListExpr(.Exprs)) compNest(Gs, ELT) Return(Name("$acc"))

  syntax Stmt ::= compNest(CompFors, Expr) [macro-rec]
  rule compNest(.CompFors, ELT:Expr)
    => Assign(Name("$acc"), BinOp("+", Name("$acc"), ListExpr(ELT)))
  rule compNest((CompFor(T:Expr, ITER:Expr, Fs:Exprs) GRest:CompFors), ELT:Expr)
    => For(T, ITER, If(compGuard(Fs), compNest(GRest, ELT), .Stmts))

  syntax Expr ::= compGuard(Exprs) [macro]
  rule compGuard(.Exprs)             => Bool(true)
  rule compGuard((F:Expr, Fs:Exprs)) => BoolOp("and", (F, Fs))
endmodule
