import KMiniPy.Verification.C3BuggyAbsAt0

/-! C3: the absolute-value spec is REFUTED for `buggy_abs` (missing x == 0
case): there is an input on which the program terminates with result None —
not an integer at all, so `0 ≤ r ∧ (r = x ∨ r = -x)` cannot hold. Witness:
x = 0, whose full execution is the concrete trace theorem
`C3BuggyAbsAt0.trace`. -/

namespace C3Refutation

def init (x : SortInt) : SortGeneratedTopCell :=
  { k := { val := SortK.kseq (SortKItem.inj_SortModule (SortModule.«Module(_)_MINIPY-LEAN-SYNTAX_Module_Stmts» (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«FuncDef(_,_,_)_MINIPY-LEAN-SYNTAX_Stmt_String_Params_Stmts» "buggy_abs" (SortParams.«Params(_)_MINIPY-LEAN-SYNTAX_Params_Strings» (SortStrings.«_,__MINIPY-LEAN-SYNTAX_Strings_String_Strings» "x" SortStrings.«.List{"_,__MINIPY-LEAN-SYNTAX_Strings_String_Strings"}_Strings»)) (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«If(_,_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Stmts_Stmts» (SortExpr.«Compare(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_CmpOp» (SortExpr.«Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» "x") (SortCmpOp.«CmpOp(_,_)_MINIPY-LEAN-SYNTAX_CmpOp_String_Expr» "<" (SortExpr.«Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» 0))) (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«Return(_)_MINIPY-LEAN-SYNTAX_Stmt_Expr» (SortExpr.«UnaryOp(_,_)_MINIPY-LEAN-SYNTAX_Expr_String_Expr» "-" (SortExpr.«Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» "x"))) SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«If(_,_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Stmts_Stmts» (SortExpr.«Compare(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_CmpOp» (SortExpr.«Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» "x") (SortCmpOp.«CmpOp(_,_)_MINIPY-LEAN-SYNTAX_CmpOp_String_Expr» ">" (SortExpr.«Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» 0))) (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«Return(_)_MINIPY-LEAN-SYNTAX_Stmt_Expr» (SortExpr.«Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» "x")) SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)) SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)) (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«Assign(_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Expr» (SortExpr.«Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» "result") (SortExpr.«Call(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_Exprs» (SortExpr.«Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» "buggy_abs") (SortExprs.«_,__MINIPY-LEAN-SYNTAX_Exprs_Expr_Exprs» (SortExpr.«Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» x) SortExprs.«.List{"_,__MINIPY-LEAN-SYNTAX_Exprs_Expr_Exprs"}_Exprs»))) SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)))) SortK.dotk }, env := { val := SortEnv.«.Env_MINIPY-LEAN_Env» }, funs := { val := SortFuns.«.Funs_MINIPY-LEAN_Funs» }, stack := { val := SortFrames.«.Frames_MINIPY-LEAN_Frames» }, generatedCounter := { val := 0 } }

/-- Some input reaches a `None` result (spec-violating terminal state).
Witness: x = 0; `init 0` is definitionally `C3BuggyAbsAt0.init`, and the
46-step concrete trace theorem carries it to the `result ↦ None` state. -/
theorem spec_refuted :
    ∃ x : SortInt, Rewrites (init x) C3BuggyAbsAt0.final :=
  ⟨0, C3BuggyAbsAt0.trace⟩

end C3Refutation
