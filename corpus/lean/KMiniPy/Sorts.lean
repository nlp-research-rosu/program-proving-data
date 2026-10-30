import KMiniPy.Prelude

structure SortGeneratedCounterCell : Type where
  val : SortInt

inductive SortStrings : Type where
  | «.List{"_,__MINIPY-LEAN-SYNTAX_Strings_String_Strings"}_Strings» : SortStrings
  | «_,__MINIPY-LEAN-SYNTAX_Strings_String_Strings» (x0 : SortString) (x1 : SortStrings) : SortStrings

inductive SortVal : Type where
  | «boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» (x0 : SortBool) : SortVal
  | «intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» (x0 : SortInt) : SortVal
  | «noneVal_MINIPY-LEAN-SYNTAX_Val» : SortVal
  | «strV(_)_MINIPY-LEAN-SYNTAX_Val_String» (x0 : SortString) : SortVal

inductive SortParams : Type where
  | «Params(_)_MINIPY-LEAN-SYNTAX_Params_Strings» (x0 : SortStrings) : SortParams

inductive SortEnv : Type where
  | «.Env_MINIPY-LEAN_Env» : SortEnv
  | «bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» (x0 : SortString) (x1 : SortVal) (x2 : SortEnv) : SortEnv

mutual
  inductive SortCmpOp : Type where
    | «CmpOp(_,_)_MINIPY-LEAN-SYNTAX_CmpOp_String_Expr» (x0 : SortString) (x1 : SortExpr) : SortCmpOp

  inductive SortExpr : Type where
    | inj_SortVal (x : SortVal) : SortExpr
    | «BinOp(_,_,_)_MINIPY-LEAN-SYNTAX_Expr_String_Expr_Expr» (x0 : SortString) (x1 : SortExpr) (x2 : SortExpr) : SortExpr
    | «Bool(_)_MINIPY-LEAN-SYNTAX_Expr_Bool» (x0 : SortBool) : SortExpr
    | «Call(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_Exprs» (x0 : SortExpr) (x1 : SortExprs) : SortExpr
    | «Compare(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_CmpOp» (x0 : SortExpr) (x1 : SortCmpOp) : SortExpr
    | «Int(_)_MINIPY-LEAN-SYNTAX_Expr_Int» (x0 : SortInt) : SortExpr
    | «Name(_)_MINIPY-LEAN-SYNTAX_Expr_String» (x0 : SortString) : SortExpr
    | «NoneVal_MINIPY-LEAN-SYNTAX_Expr» : SortExpr
    | «Str(_)_MINIPY-LEAN-SYNTAX_Expr_String» (x0 : SortString) : SortExpr
    | «UnaryOp(_,_)_MINIPY-LEAN-SYNTAX_Expr_String_Expr» (x0 : SortString) (x1 : SortExpr) : SortExpr

  inductive SortExprs : Type where
    | «.List{"_,__MINIPY-LEAN-SYNTAX_Exprs_Expr_Exprs"}_Exprs» : SortExprs
    | «_,__MINIPY-LEAN-SYNTAX_Exprs_Expr_Exprs» (x0 : SortExpr) (x1 : SortExprs) : SortExprs
end

inductive SortVals : Type where
  | «.Vals_MINIPY-LEAN_Vals» : SortVals
  | «vcons(_,_)_MINIPY-LEAN_Vals_Val_Vals» (x0 : SortVal) (x1 : SortVals) : SortVals

inductive SortOptVal : Type where
  | «noBind_MINIPY-LEAN_OptVal» : SortOptVal
  | «someVal(_)_MINIPY-LEAN_OptVal_Val» (x0 : SortVal) : SortOptVal

inductive SortKResult : Type where
  | inj_SortVal (x : SortVal) : SortKResult

structure SortEnvCell : Type where
  val : SortEnv

mutual
  inductive SortStmt : Type where
    | «Assert(_)_MINIPY-LEAN-SYNTAX_Stmt_Expr» (x0 : SortExpr) : SortStmt
    | «Assign(_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Expr» (x0 : SortExpr) (x1 : SortExpr) : SortStmt
    | «FuncDef(_,_,_)_MINIPY-LEAN-SYNTAX_Stmt_String_Params_Stmts» (x0 : SortString) (x1 : SortParams) (x2 : SortStmts) : SortStmt
    | «If(_,_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Stmts_Stmts» (x0 : SortExpr) (x1 : SortStmts) (x2 : SortStmts) : SortStmt
    | «Return(_)_MINIPY-LEAN-SYNTAX_Stmt_Expr» (x0 : SortExpr) : SortStmt
    | «While(_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Stmts» (x0 : SortExpr) (x1 : SortStmts) : SortStmt

  inductive SortStmts : Type where
    | «.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts» : SortStmts
    | «___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (x0 : SortStmt) (x1 : SortStmts) : SortStmts
end

inductive SortOptFun : Type where
  | «noFun_MINIPY-LEAN_OptFun» : SortOptFun
  | «someFun(_,_)_MINIPY-LEAN_OptFun_Params_Stmts» (x0 : SortParams) (x1 : SortStmts) : SortOptFun

inductive SortFuns : Type where
  | «.Funs_MINIPY-LEAN_Funs» : SortFuns
  | «fdef(_,_,_,_)_MINIPY-LEAN_Funs_String_Params_Stmts_Funs» (x0 : SortString) (x1 : SortParams) (x2 : SortStmts) (x3 : SortFuns) : SortFuns

inductive SortModule : Type where
  | «Module(_)_MINIPY-LEAN-SYNTAX_Module_Stmts» (x0 : SortStmts) : SortModule

structure SortFunsCell : Type where
  val : SortFuns

mutual
  inductive SortFrames : Type where
    | «.Frames_MINIPY-LEAN_Frames» : SortFrames
    | «frame(_,_,_)_MINIPY-LEAN_Frames_K_Env_Frames» (x0 : SortK) (x1 : SortEnv) (x2 : SortFrames) : SortFrames

  structure SortGeneratedTopCell : Type where
    k : SortKCell
    env : SortEnvCell
    funs : SortFunsCell
    stack : SortStackCell
    generatedCounter : SortGeneratedCounterCell

  inductive SortK : Type where
    | dotk : SortK
    | kseq (x0 : SortKItem) (x1 : SortK) : SortK

  structure SortKCell : Type where
    val : SortK

  inductive SortKItem : Type where
    | inj_SortBool (x : SortBool) : SortKItem
    | inj_SortCmpOp (x : SortCmpOp) : SortKItem
    | inj_SortEnv (x : SortEnv) : SortKItem
    | inj_SortEnvCell (x : SortEnvCell) : SortKItem
    | inj_SortExpr (x : SortExpr) : SortKItem
    | inj_SortExprs (x : SortExprs) : SortKItem
    | inj_SortFrames (x : SortFrames) : SortKItem
    | inj_SortFuns (x : SortFuns) : SortKItem
    | inj_SortFunsCell (x : SortFunsCell) : SortKItem
    | inj_SortGeneratedCounterCell (x : SortGeneratedCounterCell) : SortKItem
    | inj_SortGeneratedTopCell (x : SortGeneratedTopCell) : SortKItem
    | inj_SortInt (x : SortInt) : SortKItem
    | inj_SortKCell (x : SortKCell) : SortKItem
    | inj_SortKResult (x : SortKResult) : SortKItem
    | inj_SortModule (x : SortModule) : SortKItem
    | inj_SortOptFun (x : SortOptFun) : SortKItem
    | inj_SortOptVal (x : SortOptVal) : SortKItem
    | inj_SortParams (x : SortParams) : SortKItem
    | inj_SortStackCell (x : SortStackCell) : SortKItem
    | inj_SortStmt (x : SortStmt) : SortKItem
    | inj_SortStmts (x : SortStmts) : SortKItem
    | inj_SortString (x : SortString) : SortKItem
    | inj_SortStrings (x : SortStrings) : SortKItem
    | inj_SortVal (x : SortVal) : SortKItem
    | inj_SortVals (x : SortVals) : SortKItem
    | «#freezerAssert(_)_MINIPY-LEAN-SYNTAX_Stmt_Expr0_» : SortKItem
    | «#freezerAssign(_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Expr1_» (x0 : SortK) : SortKItem
    | «#freezerBinOp(_,_,_)_MINIPY-LEAN-SYNTAX_Expr_String_Expr_Expr1_» (x0 : SortK) (x1 : SortK) : SortKItem
    | «#freezerBinOp(_,_,_)_MINIPY-LEAN-SYNTAX_Expr_String_Expr_Expr2_» (x0 : SortK) (x1 : SortK) : SortKItem
    | «#freezerCompare(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_CmpOp0_» (x0 : SortK) : SortKItem
    | «#freezerCompare(_,_)_MINIPY-LEAN-SYNTAX_Expr_Expr_CmpOp2_» (x0 : SortK) (x1 : SortK) : SortKItem
    | «#freezerIf(_,_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Stmts_Stmts0_» (x0 : SortK) (x1 : SortK) : SortKItem
    | «#freezerReturn(_)_MINIPY-LEAN-SYNTAX_Stmt_Expr0_» : SortKItem
    | «#freezerUnaryOp(_,_)_MINIPY-LEAN-SYNTAX_Expr_String_Expr1_» (x0 : SortK) : SortKItem
    | «assertFailed_MINIPY-LEAN_KItem» : SortKItem
    | «bindP(_,_)_MINIPY-LEAN_KItem_Strings_Vals» (x0 : SortStrings) (x1 : SortVals) : SortKItem
    | «evalArgs(_,_,_)_MINIPY-LEAN_KItem_Exprs_Vals_String» (x0 : SortExprs) (x1 : SortVals) (x2 : SortString) : SortKItem
    | «evalArgsK(_,_,_)_MINIPY-LEAN_KItem_Exprs_Vals_String» (x0 : SortExprs) (x1 : SortVals) (x2 : SortString) : SortKItem
    | «execStmts(_)_MINIPY-LEAN_KItem_Stmts» (x0 : SortStmts) : SortKItem

  structure SortStackCell : Type where
    val : SortFrames
end