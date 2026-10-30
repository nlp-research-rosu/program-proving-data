import KMiniPy.Sorts

instance : Inj SortGeneratedTopCell SortKItem where
  inj := SortKItem.inj_SortGeneratedTopCell
  retr
    | SortKItem.inj_SortGeneratedTopCell x => some x
    | _ => none

instance : Inj SortExpr SortKItem where
  inj
    | SortExpr.inj_SortVal x => SortKItem.inj_SortVal x
    | x => SortKItem.inj_SortExpr x
  retr
    | SortKItem.inj_SortVal x => some (SortExpr.inj_SortVal x)
    | SortKItem.inj_SortExpr x => some x
    | _ => none

instance : Inj SortBool SortKItem where
  inj := SortKItem.inj_SortBool
  retr
    | SortKItem.inj_SortBool x => some x
    | _ => none

instance : Inj SortFuns SortKItem where
  inj := SortKItem.inj_SortFuns
  retr
    | SortKItem.inj_SortFuns x => some x
    | _ => none

instance : Inj SortStmts SortKItem where
  inj := SortKItem.inj_SortStmts
  retr
    | SortKItem.inj_SortStmts x => some x
    | _ => none

instance : Inj SortVal SortKItem where
  inj := SortKItem.inj_SortVal
  retr
    | SortKItem.inj_SortVal x => some x
    | _ => none

instance : Inj SortFrames SortKItem where
  inj := SortKItem.inj_SortFrames
  retr
    | SortKItem.inj_SortFrames x => some x
    | _ => none

instance : Inj SortString SortKItem where
  inj := SortKItem.inj_SortString
  retr
    | SortKItem.inj_SortString x => some x
    | _ => none

instance : Inj SortFunsCell SortKItem where
  inj := SortKItem.inj_SortFunsCell
  retr
    | SortKItem.inj_SortFunsCell x => some x
    | _ => none

instance : Inj SortOptFun SortKItem where
  inj := SortKItem.inj_SortOptFun
  retr
    | SortKItem.inj_SortOptFun x => some x
    | _ => none

instance : Inj SortKCell SortKItem where
  inj := SortKItem.inj_SortKCell
  retr
    | SortKItem.inj_SortKCell x => some x
    | _ => none

instance : Inj SortEnvCell SortKItem where
  inj := SortKItem.inj_SortEnvCell
  retr
    | SortKItem.inj_SortEnvCell x => some x
    | _ => none

instance : Inj SortKResult SortKItem where
  inj
    | SortKResult.inj_SortVal x => SortKItem.inj_SortVal x
  retr
    | SortKItem.inj_SortVal x => some (SortKResult.inj_SortVal x)
    | SortKItem.inj_SortKResult x => some x
    | _ => none

instance : Inj SortStmt SortKItem where
  inj := SortKItem.inj_SortStmt
  retr
    | SortKItem.inj_SortStmt x => some x
    | _ => none

instance : Inj SortCmpOp SortKItem where
  inj := SortKItem.inj_SortCmpOp
  retr
    | SortKItem.inj_SortCmpOp x => some x
    | _ => none

instance : Inj SortInt SortKItem where
  inj := SortKItem.inj_SortInt
  retr
    | SortKItem.inj_SortInt x => some x
    | _ => none

instance : Inj SortEnv SortKItem where
  inj := SortKItem.inj_SortEnv
  retr
    | SortKItem.inj_SortEnv x => some x
    | _ => none

instance : Inj SortModule SortKItem where
  inj := SortKItem.inj_SortModule
  retr
    | SortKItem.inj_SortModule x => some x
    | _ => none

instance : Inj SortExprs SortKItem where
  inj := SortKItem.inj_SortExprs
  retr
    | SortKItem.inj_SortExprs x => some x
    | _ => none

instance : Inj SortStackCell SortKItem where
  inj := SortKItem.inj_SortStackCell
  retr
    | SortKItem.inj_SortStackCell x => some x
    | _ => none

instance : Inj SortStrings SortKItem where
  inj := SortKItem.inj_SortStrings
  retr
    | SortKItem.inj_SortStrings x => some x
    | _ => none

instance : Inj SortGeneratedCounterCell SortKItem where
  inj := SortKItem.inj_SortGeneratedCounterCell
  retr
    | SortKItem.inj_SortGeneratedCounterCell x => some x
    | _ => none

instance : Inj SortParams SortKItem where
  inj := SortKItem.inj_SortParams
  retr
    | SortKItem.inj_SortParams x => some x
    | _ => none

instance : Inj SortOptVal SortKItem where
  inj := SortKItem.inj_SortOptVal
  retr
    | SortKItem.inj_SortOptVal x => some x
    | _ => none

instance : Inj SortVals SortKItem where
  inj := SortKItem.inj_SortVals
  retr
    | SortKItem.inj_SortVals x => some x
    | _ => none

instance : Inj SortVal SortExpr where
  inj := SortExpr.inj_SortVal
  retr
    | SortExpr.inj_SortVal x => some x
    | _ => none

instance : Inj SortVal SortKResult where
  inj := SortKResult.inj_SortVal
  retr
    | SortKResult.inj_SortVal x => some x