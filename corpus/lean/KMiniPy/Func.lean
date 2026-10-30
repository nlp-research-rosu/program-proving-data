import KMiniPy.Inj

def _3a1937b : SortOptVal → Option SortBool
  | SortOptVal.«someVal(_)_MINIPY-LEAN_OptVal_Val» _Gen0 => some true
  | _ => none

def _c5cbb19 : SortOptVal → Option SortBool
  | SortOptVal.«noBind_MINIPY-LEAN_OptVal» => some false
  | _ => none

axiom «_==String__STRING-COMMON_Bool_String_String» (x0 : SortString) (x1 : SortString) : Option SortBool

def _53fc758 : SortBool → Option SortBool
  | true => some false
  | _ => none

def _17ebc68 : SortBool → Option SortBool
  | false => some true
  | _ => none

def _f3c9862 : SortEnv → SortString → SortVal → Option SortEnv
  | SortEnv.«.Env_MINIPY-LEAN_Env», X, V => some (SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X V SortEnv.«.Env_MINIPY-LEAN_Env»)
  | _, _, _ => none

def _effb95e : SortOptVal → Option SortVal
  | SortOptVal.«someVal(_)_MINIPY-LEAN_OptVal_Val» V => some V
  | _ => none

def _d4319ac : SortOptFun → Option SortStmts
  | SortOptFun.«someFun(_,_)_MINIPY-LEAN_OptFun_Params_Stmts» _Gen0 B => some B
  | _ => none

def _705cece : SortOptFun → Option SortBool
  | SortOptFun.«someFun(_,_)_MINIPY-LEAN_OptFun_Params_Stmts» _Gen0 _Gen1 => some true
  | _ => none

def _0e7f4fe : SortStmts → SortExpr → SortStmts → Option SortStmts
  | SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts», C, B => some (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» (SortStmt.«While(_,_)_MINIPY-LEAN-SYNTAX_Stmt_Expr_Stmts» C B) SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts»)
  | _, _, _ => none

def _61fbef3 : SortBool → SortBool → Option SortBool
  | false, _Gen0 => some false
  | _, _ => none

def _5b9db8d : SortBool → SortBool → Option SortBool
  | true, B => some B
  | _, _ => none

def _7fae170 : SortOptFun → Option SortStrings
  | SortOptFun.«someFun(_,_)_MINIPY-LEAN_OptFun_Params_Stmts» (SortParams.«Params(_)_MINIPY-LEAN-SYNTAX_Params_Strings» PS) _Gen0 => some PS
  | _ => none

def _efd7dee : SortFuns → SortString → Option SortOptFun
  | SortFuns.«.Funs_MINIPY-LEAN_Funs», _Gen0 => some SortOptFun.«noFun_MINIPY-LEAN_OptFun»
  | _, _ => none

def _f5f3f2e : SortFuns → SortString → Option SortOptFun
  | SortFuns.«fdef(_,_,_,_)_MINIPY-LEAN_Funs_String_Params_Stmts_Funs» F PS B _Gen0, _Uniq0 => match F == _Uniq0 with
    | true => some (SortOptFun.«someFun(_,_)_MINIPY-LEAN_OptFun_Params_Stmts» PS B)
    | _ => none
  | _, _ => none

def _f4c2469 : SortK → Option SortBool
  | SortK.kseq _Pat0 SortK.dotk => match (@retr SortKResult SortKItem) _Pat0 with
    | some KResult => some true
    | _ => none
  | _ => none

def _afefecb : SortK → Option SortBool
  | K => some false

def _b922119 : SortVals → SortVal → Option SortVals
  | SortVals.«.Vals_MINIPY-LEAN_Vals», V => some (SortVals.«vcons(_,_)_MINIPY-LEAN_Vals_Val_Vals» V SortVals.«.Vals_MINIPY-LEAN_Vals»)
  | _, _ => none

def _639b4ef : SortEnv → SortString → Option SortOptVal
  | SortEnv.«.Env_MINIPY-LEAN_Env», _Gen0 => some SortOptVal.«noBind_MINIPY-LEAN_OptVal»
  | _, _ => none

def _c952276 : SortEnv → SortString → SortVal → Option SortEnv
  | SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X _Gen0 R, _Uniq0, V => match X == _Uniq0 with
    | true => some (SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X V R)
    | _ => none
  | _, _, _ => none

def _27dc983 : SortOptFun → Option SortBool
  | SortOptFun.«noFun_MINIPY-LEAN_OptFun» => some false
  | _ => none

def _95e90d4 : SortEnv → SortString → Option SortOptVal
  | SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X V _Gen0, _Uniq0 => match X == _Uniq0 with
    | true => some (SortOptVal.«someVal(_)_MINIPY-LEAN_OptVal_Val» V)
    | _ => none
  | _, _ => none

def «isBound(_)_MINIPY-LEAN_Bool_OptVal» (x0 : SortOptVal) : Option SortBool := (_3a1937b x0) <|> (_c5cbb19 x0)

def notBool_ (x0 : SortBool) : Option SortBool := (_17ebc68 x0) <|> (_53fc758 x0)

def _4b97627 : SortString → SortVal → SortVal → Option SortVal
  | "-", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_-Int_» I1 I2
    return (SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» _Val0)
  | _, _, _ => none

def _0ddec05 : SortString → SortVal → SortVal → Option SortVal
  | "==", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_==Int_» I1 I2
    return (SortVal.«boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» _Val0)
  | _, _, _ => none

def _1a7b0ca : SortString → SortVal → SortVal → Option SortVal
  | ">", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_>Int_» I1 I2
    return (SortVal.«boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» _Val0)
  | _, _, _ => none

def «valOf(_)_MINIPY-LEAN_Val_OptVal» (x0 : SortOptVal) : Option SortVal := _effb95e x0

def _148f5b4 : SortString → SortVal → SortVal → Option SortVal
  | "<", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_<Int_» I1 I2
    return (SortVal.«boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» _Val0)
  | _, _, _ => none

def _7ef5a32 : SortString → SortVal → SortVal → Option SortVal
  | ">=", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_>=Int_» I1 I2
    return (SortVal.«boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» _Val0)
  | _, _, _ => none

def «bodyOf(_)_MINIPY-LEAN_Stmts_OptFun» (x0 : SortOptFun) : Option SortStmts := _d4319ac x0

def _3439d27 : SortString → SortVal → SortVal → Option SortVal
  | "+", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_+Int_» I1 I2
    return (SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» _Val0)
  | _, _, _ => none

mutual
  def _50a6500 : SortStmts → SortExpr → SortStmts → Option SortStmts
    | SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» S SS, C, B => do
      let _Val0 <- «snocW(_,_,_)_MINIPY-LEAN_Stmts_Stmts_Expr_Stmts» SS C B
      return (SortStmts.«___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts» S _Val0)
    | _, _, _ => none

  def «snocW(_,_,_)_MINIPY-LEAN_Stmts_Stmts_Expr_Stmts» (x0 : SortStmts) (x1 : SortExpr) (x2 : SortStmts) : Option SortStmts := (_0e7f4fe x0 x1 x2) <|> (_50a6500 x0 x1 x2)
end

def _andBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_5b9db8d x0 x1) <|> (_61fbef3 x0 x1)

def «psOf(_)_MINIPY-LEAN_Strings_OptFun» (x0 : SortOptFun) : Option SortStrings := _7fae170 x0

def _2d811e1 : SortString → SortVal → SortVal → Option SortVal
  | "*", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_*Int_» I1 I2
    return (SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» _Val0)
  | _, _, _ => none

def isKResult (x0 : SortK) : Option SortBool := (_f4c2469 x0) <|> (_afefecb x0)

mutual
  def «vsnoc(_,_)_MINIPY-LEAN_Vals_Vals_Val» (x0 : SortVals) (x1 : SortVal) : Option SortVals := (_b922119 x0 x1) <|> (_f20aa8c x0 x1)

  def _f20aa8c : SortVals → SortVal → Option SortVals
    | SortVals.«vcons(_,_)_MINIPY-LEAN_Vals_Val_Vals» W R, V => do
      let _Val0 <- «vsnoc(_,_)_MINIPY-LEAN_Vals_Vals_Val» R V
      return (SortVals.«vcons(_,_)_MINIPY-LEAN_Vals_Val_Vals» W _Val0)
    | _, _ => none
end

def _0f91d65 : SortString → SortVal → SortVal → Option SortVal
  | "<=", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_<=Int_» I1 I2
    return (SortVal.«boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» _Val0)
  | _, _, _ => none

def «isFun(_)_MINIPY-LEAN_Bool_OptFun» (x0 : SortOptFun) : Option SortBool := (_27dc983 x0) <|> (_705cece x0)

noncomputable def _f390a9b : SortString → SortString → Option SortBool
  | S1, S2 => do
    let _Val0 <- «_==String__STRING-COMMON_Bool_String_String» S1 S2
    let _Val1 <- notBool_ _Val0
    return _Val1

def _4de6e05 : SortInt → SortInt → Option SortBool
  | I1, I2 => do
    let _Val0 <- «_==Int_» I1 I2
    let _Val1 <- notBool_ _Val0
    return _Val1

noncomputable def «_=/=String__STRING-COMMON_Bool_String_String» (x0 : SortString) (x1 : SortString) : Option SortBool := _f390a9b x0 x1

def «_=/=Int_» (x0 : SortInt) (x1 : SortInt) : Option SortBool := _4de6e05 x0 x1

mutual
  noncomputable def «flookup(_,_)_MINIPY-LEAN_OptFun_Funs_String» (x0 : SortFuns) (x1 : SortString) : Option SortOptFun := (_ae92d99 x0 x1) <|> (_efd7dee x0 x1) <|> (_f5f3f2e x0 x1)

  noncomputable def _ae92d99 : SortFuns → SortString → Option SortOptFun
    | SortFuns.«fdef(_,_,_,_)_MINIPY-LEAN_Funs_String_Params_Stmts_Funs» F _Gen0 _Gen1 R, G => do
      let _Val0 <- «_=/=String__STRING-COMMON_Bool_String_String» F G
      let _Val1 <- «flookup(_,_)_MINIPY-LEAN_OptFun_Funs_String» R G
      guard _Val0
      return _Val1
    | _, _ => none
end

mutual
  noncomputable def «update(_,_,_)_MINIPY-LEAN_Env_Env_String_Val» (x0 : SortEnv) (x1 : SortString) (x2 : SortVal) : Option SortEnv := (_bd0f5e0 x0 x1 x2) <|> (_c952276 x0 x1 x2) <|> (_f3c9862 x0 x1 x2)

  noncomputable def _bd0f5e0 : SortEnv → SortString → SortVal → Option SortEnv
    | SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X W R, Y, V => do
      let _Val0 <- «_=/=String__STRING-COMMON_Bool_String_String» X Y
      let _Val1 <- «update(_,_,_)_MINIPY-LEAN_Env_Env_String_Val» R Y V
      guard _Val0
      return (SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X W _Val1)
    | _, _, _ => none
end

mutual
  noncomputable def _9ce0d02 : SortEnv → SortString → Option SortOptVal
    | SortEnv.«bind(_,_,_)_MINIPY-LEAN_Env_String_Val_Env» X _Gen0 R, Y => do
      let _Val0 <- «_=/=String__STRING-COMMON_Bool_String_String» X Y
      let _Val1 <- «lookup(_,_)_MINIPY-LEAN_OptVal_Env_String» R Y
      guard _Val0
      return _Val1
    | _, _ => none

  noncomputable def «lookup(_,_)_MINIPY-LEAN_OptVal_Env_String» (x0 : SortEnv) (x1 : SortString) : Option SortOptVal := (_639b4ef x0 x1) <|> (_95e90d4 x0 x1) <|> (_9ce0d02 x0 x1)
end

def _53572c8 : SortString → SortVal → SortVal → Option SortVal
  | "!=", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_=/=Int_» I1 I2
    return (SortVal.«boolV(_)_MINIPY-LEAN-SYNTAX_Val_Bool» _Val0)
  | _, _, _ => none

def _bd04896 : SortInt → SortInt → Option SortInt
  | A, B => do
    let _Val0 <- «_=/=Int_» B 0
    let _Val1 <- _modInt_ A B
    let _Val2 <- «_+Int_» _Val1 B
    let _Val3 <- _modInt_ _Val2 B
    guard _Val0
    return _Val3

def «applyCmp(_,_,_)_MINIPY-LEAN_Val_String_Val_Val» (x0 : SortString) (x1 : SortVal) (x2 : SortVal) : Option SortVal := (_0ddec05 x0 x1 x2) <|> (_0f91d65 x0 x1 x2) <|> (_148f5b4 x0 x1 x2) <|> (_1a7b0ca x0 x1 x2) <|> (_53572c8 x0 x1 x2) <|> (_7ef5a32 x0 x1 x2)

def «floorMod(_,_)_MINIPY-LEAN_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := _bd04896 x0 x1

def _08cef47 : SortInt → SortInt → Option SortInt
  | A, B => do
    let _Val0 <- «_=/=Int_» B 0
    let _Val1 <- «floorMod(_,_)_MINIPY-LEAN_Int_Int_Int» A B
    let _Val2 <- «_-Int_» A _Val1
    let _Val3 <- «_/Int_» _Val2 B
    guard _Val0
    return _Val3

def _969013d : SortString → SortVal → SortVal → Option SortVal
  | "%", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_=/=Int_» I2 0
    let _Val1 <- «floorMod(_,_)_MINIPY-LEAN_Int_Int_Int» I1 I2
    guard _Val0
    return (SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» _Val1)
  | _, _, _ => none

def «floorDiv(_,_)_MINIPY-LEAN_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := _08cef47 x0 x1

def _6c7c2e8 : SortString → SortVal → SortVal → Option SortVal
  | "//", SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I1, SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» I2 => do
    let _Val0 <- «_=/=Int_» I2 0
    let _Val1 <- «floorDiv(_,_)_MINIPY-LEAN_Int_Int_Int» I1 I2
    guard _Val0
    return (SortVal.«intV(_)_MINIPY-LEAN-SYNTAX_Val_Int» _Val1)
  | _, _, _ => none

def «applyBin(_,_,_)_MINIPY-LEAN_Val_String_Val_Val» (x0 : SortString) (x1 : SortVal) (x2 : SortVal) : Option SortVal := (_2d811e1 x0 x1 x2) <|> (_3439d27 x0 x1 x2) <|> (_4b97627 x0 x1 x2) <|> (_6c7c2e8 x0 x1 x2) <|> (_969013d x0 x1 x2)