// semantics/minipy-lean.k — MINIPY-LEAN
//
// A klean-compatible K semantics for the Python-subset sample programs.
// Same AST constructors as the vendored MPY semantics (py2mpy output parses
// unchanged), but the configuration avoids every hooked collection sort
// (Map/List/Set have no klean translation): environments, the function table,
// call frames, and argument lists are ordinary constructor sorts, and their
// lookup/update helpers are K functions — which klean turns into COMPUTABLE
// Lean definitions, so rule hypotheses discharge by rfl/decide.
//
// Every rule carries a label: labels become the Lean constructor names of the
// generated `Rewrites` relation.

module MINIPY-LEAN-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX

  syntax Val ::= intV(Int) | boolV(Bool) | strV(String) | "noneVal"

  syntax Expr ::= Val
                | "Int" "(" Int ")"
                | "Bool" "(" Bool ")"
                | "Str" "(" String ")"
                | "NoneVal"
                | "Name" "(" String ")"
                | "BinOp" "(" String "," Expr "," Expr ")" [seqstrict(2, 3)]
                | "UnaryOp" "(" String "," Expr ")"        [strict(2)]
                | "Compare" "(" Expr "," CmpOp ")"
                | "Call" "(" Expr "," Exprs ")"
  syntax CmpOp ::= "CmpOp" "(" String "," Expr ")"
  syntax Exprs ::= List{Expr, ","}
  syntax Strings ::= List{String, ","}
  syntax Params ::= "Params" "(" Strings ")"

  syntax Stmt ::= "Assign" "(" Expr "," Expr ")"           [strict(2)]
                | "If" "(" Expr "," Stmts "," Stmts ")"    [strict(1)]
                | "While" "(" Expr "," Stmts ")"
                | "Return" "(" Expr ")"                    [strict]
                | "Assert" "(" Expr ")"                    [strict]
                | "FuncDef" "(" String "," Params "," Stmts ")"
  syntax Stmts ::= List{Stmt, ""}
  syntax Module ::= "Module" "(" Stmts ")"
endmodule

module MINIPY-LEAN
  imports MINIPY-LEAN-SYNTAX
  imports INT
  imports BOOL
  imports STRING

  syntax KResult ::= Val

  // ==== constructor-based environment =======================================
  syntax Env ::= ".Env" | bind(String, Val, Env)
  syntax OptVal ::= "noBind" | someVal(Val)
  syntax OptVal ::= lookup(Env, String) [function, total]
  rule lookup(.Env, _) => noBind
  rule lookup(bind(X, V, _), X) => someVal(V)
  rule lookup(bind(X, _, R), Y) => lookup(R, Y) requires X =/=String Y
  syntax Val ::= valOf(OptVal) [function]
  rule valOf(someVal(V)) => V
  syntax Bool ::= isBound(OptVal) [function, total]
  rule isBound(noBind) => false
  rule isBound(someVal(_)) => true

  syntax Env ::= update(Env, String, Val) [function, total]
  rule update(.Env, X, V) => bind(X, V, .Env)
  rule update(bind(X, _, R), X, V) => bind(X, V, R)
  rule update(bind(X, W, R), Y, V) => bind(X, W, update(R, Y, V)) requires X =/=String Y

  // ==== function table ======================================================
  syntax Funs ::= ".Funs" | fdef(String, Params, Stmts, Funs)
  syntax OptFun ::= "noFun" | someFun(Params, Stmts)
  syntax OptFun ::= flookup(Funs, String) [function, total]
  rule flookup(.Funs, _) => noFun
  rule flookup(fdef(F, PS, B, _), F) => someFun(PS, B)
  rule flookup(fdef(F, _, _, R), G) => flookup(R, G) requires F =/=String G
  syntax Bool ::= isFun(OptFun) [function, total]
  rule isFun(noFun) => false
  rule isFun(someFun(_, _)) => true
  syntax Strings ::= psOf(OptFun) [function]
  rule psOf(someFun(Params(PS), _)) => PS
  syntax Stmts ::= bodyOf(OptFun) [function]
  rule bodyOf(someFun(_, B)) => B

  // ==== evaluated-argument list =============================================
  syntax Vals ::= ".Vals" | vcons(Val, Vals)
  syntax Vals ::= vsnoc(Vals, Val) [function, total]
  rule vsnoc(.Vals, V) => vcons(V, .Vals)
  rule vsnoc(vcons(W, R), V) => vcons(W, vsnoc(R, V))

  // ==== call frames (continuation, caller env) ==============================
  syntax Frames ::= ".Frames" | frame(K, Env, Frames)

  configuration
    <k> $PGM:Module </k>
    <env> .Env </env>
    <funs> .Funs </funs>
    <stack> .Frames </stack>

  // ==== load & sequencing ===================================================
  rule <k> Module(SS) => SS ... </k>                    [label(load)]
  rule <k> (S:Stmt SS:Stmts):Stmts => S ~> SS ... </k>  [label(seq)]
  rule <k> .Stmts => .K ... </k>                        [label(seqDone)]

  // ==== literals ============================================================
  rule <k> Int(I:Int) => intV(I) ... </k>                     [label(litInt)]
  rule <k> Bool(B:Bool) => boolV(B) ... </k>                   [label(litBool)]
  rule <k> Str(S:String) => strV(S) ... </k>                   [label(litStr)]
  rule <k> NoneVal => noneVal ... </k>                  [label(litNone)]

  // ==== variables ===========================================================
  rule <k> Name(X) => valOf(lookup(Rho, X)) ... </k> <env> Rho </env>
       requires isBound(lookup(Rho, X))             [label(var)]

  rule <k> Assign(Name(X), V:Val) => .K ... </k>
       <env> Rho => update(Rho, X, V) </env>           [label(assign)]

  // ==== control =============================================================
  // execStmts keeps the rewrite at KItem sort: a bare `If(...) => T:Stmts`
  // would make the rule parser wrap the LHS into a singleton Stmts list,
  // which never occurs at the top of <k> (statements arrive as bare Stmt
  // items via `seq`).
  syntax KItem ::= execStmts(Stmts)
  rule <k> If(boolV(true),  T, _) => execStmts(T) ... </k>    [label(ifTrue)]
  rule <k> If(boolV(false), _, E) => execStmts(E) ... </k>    [label(ifFalse)]
  rule <k> execStmts(SS) => SS ... </k>                [label(execBlock)]

  // ==== assert ==============================================================
  // On failure the whole continuation is replaced by a terminal marker,
  // mirroring the traced MPY semantics (assert.k: `Assert(V) ~> _ => .K` with
  // <exc> AssertionError): execution halts at the raise, <env>/<stack> keep
  // the frame state at the failure point. `assertFailed` matches no rule, so
  // the configuration is final.
  syntax KItem ::= "assertFailed"
  rule <k> Assert(boolV(true)) => .K ... </k>                  [label(assertOk)]
  rule <k> Assert(boolV(false)) ~> _ => assertFailed </k>      [label(assertFail)]

  syntax Stmts ::= snocW(Stmts, Expr, Stmts) [function, total]
  rule snocW(.Stmts, C, B) => While(C, B) .Stmts
  rule snocW(S:Stmt SS, C, B) => S snocW(SS, C, B)
  rule <k> While(C, B) => If(C, snocW(B, C, B), .Stmts) ... </k> [label(whileUnfold)]

  // ==== operators ===========================================================
  rule <k> BinOp(OP, V1:Val, V2:Val) => applyBin(OP, V1, V2) ... </k> [label(binop)]
  syntax Val ::= applyBin(String, Val, Val) [function]
  rule applyBin("+", intV(I1), intV(I2)) => intV(I1 +Int I2)
  rule applyBin("-", intV(I1), intV(I2)) => intV(I1 -Int I2)
  rule applyBin("*", intV(I1), intV(I2)) => intV(I1 *Int I2)
  rule applyBin("//", intV(I1), intV(I2)) => intV(floorDiv(I1, I2)) requires I2 =/=Int 0
  rule applyBin("%", intV(I1), intV(I2)) => intV(floorMod(I1, I2)) requires I2 =/=Int 0

  // floored semantics matching Python // and % for positive divisors
  syntax Int ::= floorMod(Int, Int) [function]
  rule floorMod(A, B) => ((A modInt B) +Int B) modInt B requires B =/=Int 0
  syntax Int ::= floorDiv(Int, Int) [function]
  rule floorDiv(A, B) => (A -Int floorMod(A, B)) /Int B requires B =/=Int 0

  rule <k> UnaryOp("-", intV(I)) => intV(0 -Int I) ... </k>    [label(neg)]

  context Compare(HOLE, _)
  context Compare(_:Val, CmpOp(_, HOLE))
  rule <k> Compare(V1:Val, CmpOp(OP, V2:Val)) => applyCmp(OP, V1, V2) ... </k> [label(cmp)]
  syntax Val ::= applyCmp(String, Val, Val) [function]
  rule applyCmp("==", intV(I1), intV(I2)) => boolV(I1 ==Int I2)
  rule applyCmp("!=", intV(I1), intV(I2)) => boolV(I1 =/=Int I2)
  rule applyCmp("<", intV(I1), intV(I2)) => boolV(I1 <Int I2)
  rule applyCmp("<=", intV(I1), intV(I2)) => boolV(I1 <=Int I2)
  rule applyCmp(">", intV(I1), intV(I2)) => boolV(I1 >Int I2)
  rule applyCmp(">=", intV(I1), intV(I2)) => boolV(I1 >=Int I2)

  // ==== functions ===========================================================
  rule <k> FuncDef(F, PS, B) => .K ... </k>
       <funs> Fs => fdef(F, PS, B, Fs) </funs>         [label(defFun)]

  syntax KItem ::= evalArgs(Exprs, Vals, String) | evalArgsK(Exprs, Vals, String)
  rule <k> Call(Name(F), ARGS) => evalArgs(ARGS, .Vals, F) ... </k>  [label(callBegin)]
  rule <k> evalArgs((E:Expr, REST:Exprs), ACC, F) => E ~> evalArgsK(REST, ACC, F) ... </k>
                                                       [label(argNext)]
  rule <k> V:Val ~> evalArgsK(REST, ACC, F) => evalArgs(REST, vsnoc(ACC, V), F) ... </k>
                                                       [label(argCollect)]

  syntax KItem ::= bindP(Strings, Vals)
  rule <k> (evalArgs(.Exprs, VS, F) ~> CONT:K)
        => bindP(psOf(flookup(Fs, F)), VS) ~> bodyOf(flookup(Fs, F)) ~> Return(NoneVal) </k>
       <funs> Fs </funs>
       <env> Rho => .Env </env>
       <stack> St => frame(CONT, Rho, St) </stack>
       requires isFun(flookup(Fs, F))              [label(callPush)]

  rule <k> bindP((P:String, PR:Strings), vcons(V, VR)) => bindP(PR, VR) ... </k>
       <env> Rho => update(Rho, P, V) </env>           [label(bindParam)]
  rule <k> bindP(.Strings, .Vals) => .K ... </k>       [label(bindDone)]

  rule <k> (Return(V:Val) ~> _) => V ~> CONT </k>
       <env> _ => Rho' </env>
       <stack> frame(CONT, Rho', St) => St </stack>    [label(returnPop)]
endmodule
