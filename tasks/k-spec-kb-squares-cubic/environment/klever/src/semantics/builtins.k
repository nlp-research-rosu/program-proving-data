// reference/src/semantics/builtins.k — MPY-BUILTINS

module MPY-BUILTINS
  imports MPY-CORE
  imports MPY-STR
  imports MPY-SET
  imports MPY-ITER
  imports MPY-RANGE
  imports MPY-INT
  imports MPY-METHODS

  // the builtins REGISTRY is core.k's builtinsScope (the -1 frame); names resolve by lookup

  // Call routing + argument evaluation live in call.k, which also routes the fold
  // builtins (sum/all/any/max/min) to the #_Acc folds below and everything else to
  // applyBuiltin. This module owns applyBuiltin + the fold implementations.
  syntax Val ::= applyBuiltin(String, Vals) [function]

  // ==== len(obj) — O(1) per kind ============================================
  syntax Int ::= seqLen(Val) [function]
  rule applyBuiltin("len", OBJ:Val, .Vals) => seqLen(OBJ)
  rule seqLen(list(VS:ValSeq))                  => vsLen(VS)
  rule seqLen(tuple(VS:ValSeq))                 => vsLen(VS)
  rule seqLen(str(IS:IntSeq))                   => isLen(IS)
  rule seqLen(setV(DS:IntSeq))                  => isLen(DS)
  rule seqLen(rangeObj(LO:Int, HI:Int, ST:Int)) => rangeLen(LO, HI, ST)

  // ==== list(seq) — materialize a list/tuple into a list (e.g. list(d.keys())) ==
  // Minimal: the "copy a sequence" case (list of a list is itself; list of a tuple keeps order).
  // list() of other iterables (str/range/set/zip) is added via the iterator fold when needed.
  // (k-cell — list() constructs a NEW object)
  rule <k> #applyK(toCall(builtinV("list")), (list(VS:ValSeq),  .Vals)) => #alloc(list(VS)) ... </k>
  rule <k> #applyK(toCall(builtinV("list")), (tuple(VS:ValSeq), .Vals)) => #alloc(list(VS)) ... </k>
  rule <k> #applyK(toCall(builtinV("list")), .Vals)                     => #alloc(list(.ValSeq)) ... </k>
  rule <k> #applyK(toCall(builtinV("list")), (str(CS:IntSeq), .Vals))   => #alloc(list(charsOf(CS))) ... </k>
  syntax ValSeq ::= charsOf(IntSeq) [function, total]
  rule charsOf(.IntSeq)                => .ValSeq
  rule charsOf(iCons(C:Int, R:IntSeq)) => vCons(str(iCons(C, .IntSeq)), charsOf(R))

  // ==== set(str) — distinct character codes =================================
  rule applyBuiltin("set", str(CS:IntSeq), .Vals) => setV(dedupCodes(CS))

  // ==== abs(int) ============================================================
  rule applyBuiltin("abs", I:Int, .Vals) => absInt(I)

  // ==== sum(iterable) — one #iterNext fold; intOf = int value of an int/bool ==
  syntax KItem ::= #sumAcc(Iterable, Int) | #sumCont(Int)
  rule <k> #sumAcc(IT:Iterable, ACC:Int) => #iterNext(IT) ~> #sumCont(ACC) ... </k>
  rule <k> #iterDone ~> #sumCont(ACC:Int) => ACC ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #sumCont(ACC:Int)
        => #sumAcc(R, ACC +Int intOf(V)) ... </k>
       requires isInt(V) orBool isBool(V)

  syntax Int ::= intOf(Val) [function]
  rule intOf(I:Int)  => I
  rule intOf(B:Bool) => #if B #then 1 #else 0 #fi

  // ==== all / any (short-circuiting #iterNext folds) ========================
  syntax KItem ::= #allAcc(Iterable) | "#allCont"
  rule <k> #allAcc(IT:Iterable) => #iterNext(IT) ~> #allCont ... </k>
  rule <k> #iterDone ~> #allCont => true ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #allCont => #allAcc(R) ... </k>
       requires truthy(V)
  rule <k> #iterYield(V:Val, _:Iterable) ~> #allCont => false ... </k>
       requires notBool truthy(V)

  syntax KItem ::= #anyAcc(Iterable) | "#anyCont"
  rule <k> #anyAcc(IT:Iterable) => #iterNext(IT) ~> #anyCont ... </k>
  rule <k> #iterDone ~> #anyCont => false ... </k>
  rule <k> #iterYield(V:Val, _:Iterable) ~> #anyCont => true ... </k>
       requires truthy(V)
  rule <k> #iterYield(V:Val, R:Iterable) ~> #anyCont => #anyAcc(R) ... </k>
       requires notBool truthy(V)

  // ==== max / min over an iterable (#iterNext folds; first element seeds) ====
  syntax KItem ::= #maxAcc0(Iterable) | "#maxCont0" | #maxAcc(Iterable, Int) | #maxCont(Int)
  rule <k> #maxAcc0(IT:Iterable) => #iterNext(IT) ~> #maxCont0 ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #maxCont0 => #maxAcc(R, {V}:>Int) ... </k>
       requires isInt(V)
  rule <k> #maxAcc(IT:Iterable, M:Int) => #iterNext(IT) ~> #maxCont(M) ... </k>
  rule <k> #iterDone ~> #maxCont(M:Int) => M ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #maxCont(M:Int)
        => #maxAcc(R, maxInt(M, {V}:>Int)) ... </k>
       requires isInt(V)

  syntax KItem ::= #minAcc0(Iterable) | "#minCont0" | #minAcc(Iterable, Int) | #minCont(Int)
  rule <k> #minAcc0(IT:Iterable) => #iterNext(IT) ~> #minCont0 ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #minCont0 => #minAcc(R, {V}:>Int) ... </k>
       requires isInt(V)
  rule <k> #minAcc(IT:Iterable, M:Int) => #iterNext(IT) ~> #minCont(M) ... </k>
  rule <k> #iterDone ~> #minCont(M:Int) => M ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #minCont(M:Int)
        => #minAcc(R, minInt(M, {V}:>Int)) ... </k>
       requires isInt(V)

  // ==== variadic max / min (a Vals fold) ====================================
  syntax Int ::= maxVals(Int, Vals) [function]
  rule applyBuiltin("max", I:Int, REST:Vals) => maxVals(I, REST)
  rule maxVals(M:Int, .Vals)           => M
  rule maxVals(M:Int, (I:Int, R:Vals)) => maxVals(maxInt(M, I), R)

  syntax Int ::= minVals(Int, Vals) [function]
  rule applyBuiltin("min", I:Int, REST:Vals) => minVals(I, REST)
  rule minVals(M:Int, .Vals)           => M
  rule minVals(M:Int, (I:Int, R:Vals)) => minVals(minInt(M, I), R)

  // ==== bin(n) — "0b" + binary digit codes (promoted from 103's defined fold) ==
  rule applyBuiltin("bin", N:Int, .Vals) => str(iCons(48, iCons(98, binCodes(N))))
       requires N >=Int 0
  syntax IntSeq ::= binCodes(Int) [function, total]
  rule binCodes(0) => iCons(48, .IntSeq)
  rule binCodes(N:Int) => binAcc(N, .IntSeq) requires N >Int 0
  syntax IntSeq ::= binAcc(Int, IntSeq) [function, total]
  rule binAcc(0, ACC:IntSeq) => ACC
  rule binAcc(N:Int, ACC:IntSeq)
    => binAcc((N -Int pyMod(N, 2)) /Int 2, iCons(48 +Int pyMod(N, 2), ACC))
       requires N >Int 0

  // ==== enumerate(xs) — pairs (i, v); materialized eagerly over a list =========
  rule <k> #applyK(toCall(builtinV("enumerate")), (list(VS:ValSeq), .Vals))
        => #alloc(list(enumVS(VS, 0))) ... </k>
  syntax ValSeq ::= enumVS(ValSeq, Int) [function, total]
  rule enumVS(.ValSeq, _:Int) => .ValSeq
  rule enumVS(vCons(V:Val, R:ValSeq), I:Int)
    => vCons(tuple(vCons(I, vCons(V, .ValSeq))), enumVS(R, I +Int 1))

  // ==== map(str, xs) — eager (only the str case is in the subset) =============
  rule <k> #applyK(toCall(builtinV("map")), (typeV("str"), list(VS:ValSeq), .Vals))
        => #alloc(list(mapStrVS(VS))) ... </k>
  syntax ValSeq ::= mapStrVS(ValSeq) [function, total]
  rule mapStrVS(.ValSeq) => .ValSeq
  rule mapStrVS(vCons(I:Int, R:ValSeq)) => vCons(str(strToCodes(Int2String(I))), mapStrVS(R))
  rule mapStrVS(vCons(str(CS:IntSeq), R:ValSeq)) => vCons(str(CS), mapStrVS(R))

  // ==== int(x) identities (int(round(x)) composes through) ====================
  rule applyBuiltin("int", I:Int, .Vals) => I

  // ==== ord / chr ===========================================================
  rule applyBuiltin("ord", str(iCons(C:Int, .IntSeq)), .Vals) => C
  rule applyBuiltin("chr", I:Int, .Vals) => str(iCons(I, .IntSeq))
       requires 0 <=Int I andBool I <Int 128

  // ==== str(int) / str(str) =================================================
  rule applyBuiltin("str", I:Int, .Vals)       => str(strToCodes(Int2String(I)))
  rule applyBuiltin("str", str(CS:IntSeq), .Vals) => str(CS)

  // ==== int(str) — a single digit char ('0'..'9', code 48..57) to its value =====
  rule applyBuiltin("int", str(iCons(C:Int, .IntSeq)), .Vals) => C -Int 48
       requires 48 <=Int C andBool C <=Int 57

  // ==== int(str) — a multi-digit non-negative numeral (Horner fold; the single-char rule covers len 1)
  rule applyBuiltin("int", str(CS:IntSeq), .Vals) => intDigAcc(CS, 0)
       requires isLen(CS) >=Int 2
  syntax Int ::= intDigAcc(IntSeq, Int) [function, total]
  rule intDigAcc(.IntSeq, ACC:Int)             => ACC
  rule intDigAcc(iCons(C:Int, R:IntSeq), ACC:Int) => intDigAcc(R, (ACC *Int 10) +Int (C -Int 48))

  // ==== zip(a, b) — parallel iterable of pairs, truncating to the shorter =====
  rule applyBuiltin("zip", list(A:ValSeq), list(B:ValSeq), .Vals) => zipObj(A, B)
  rule applyBuiltin("zip", str(A:IntSeq), str(B:IntSeq), .Vals)   => zipObjS(A, B)

  // zip's iterator-protocol cases (zip is created here, so its #iterNext lives here)
  rule <k> #iterNext(zipObj(vCons(A:Val, As:ValSeq), vCons(B:Val, Bs:ValSeq)))
        => #iterYield(tuple(vCons(A, vCons(B, .ValSeq))), zipObj(As, Bs)) ... </k>
  rule <k> #iterNext(zipObj(.ValSeq, _:ValSeq))               => #iterDone ... </k>
  rule <k> #iterNext(zipObj(vCons(_:Val, _:ValSeq), .ValSeq)) => #iterDone ... </k>
  rule <k> #iterNext(zipObjS(iCons(A:Int, As:IntSeq), iCons(B:Int, Bs:IntSeq)))
        => #iterYield(tuple(vCons(str(iCons(A, .IntSeq)), vCons(str(iCons(B, .IntSeq)), .ValSeq))), zipObjS(As, Bs)) ... </k>
  rule <k> #iterNext(zipObjS(.IntSeq, _:IntSeq))              => #iterDone ... </k>
  rule <k> #iterNext(zipObjS(iCons(_:Int, _:IntSeq), .IntSeq)) => #iterDone ... </k>

  // ==== range(stop) / range(start, stop) / range(start, stop, step) =========
  rule applyBuiltin("range", I:Int, .Vals)               => rangeObj(0, I, 1)
  rule applyBuiltin("range", A:Int, B:Int, .Vals)        => rangeObj(A, B, 1)
  rule applyBuiltin("range", A:Int, B:Int, S:Int, .Vals) => rangeObj(A, B, S)
       requires S =/=Int 0

  // ==== eval(str) — arithmetic expressions (ints, + - * // **, spaces) ========
  // Python precedence: ** right-assoc, then * //, then + -. Promoted from 160's
  // trusted pass evaluator, now DEFINED in the reference and driven by a
  // code-level tokenizer. Reduces on concrete strings (krun); a symbolic
  // argument leaves the call unevaluated for problem-level folds.
  rule applyBuiltin("eval", str(CS:IntSeq), .Vals) => evalArith(CS)
  syntax Int ::= evalArith(IntSeq) [function]
  rule evalArith(CS:IntSeq)
    => firstNdE(passAddE(passMulE(passPowE(tokOps(CS), tokNds(CS)))))

  syntax OpSeq ::= ".OpSeq" | oCons(String, OpSeq)

  syntax Bool ::= evDigit(Int) [function, total]
  rule evDigit(C:Int) => C >=Int 48 andBool C <=Int 57
  syntax Bool ::= evHead42(IntSeq) [function, total]
  rule evHead42(iCons(42, _:IntSeq)) => true
  rule evHead42(_:IntSeq)            => false [owise]
  syntax Bool ::= evHead47(IntSeq) [function, total]
  rule evHead47(iCons(47, _:IntSeq)) => true
  rule evHead47(_:IntSeq)            => false [owise]

  syntax OpSeq ::= tokOps(IntSeq) [function, total]
  rule tokOps(.IntSeq)                 => .OpSeq
  rule tokOps(iCons(32, R:IntSeq))     => tokOps(R)
  rule tokOps(iCons(C:Int, R:IntSeq))  => tokOps(R) requires evDigit(C)
  rule tokOps(iCons(42, iCons(42, R:IntSeq))) => oCons("**", tokOps(R))
  rule tokOps(iCons(42, R:IntSeq))     => oCons("*", tokOps(R)) requires notBool evHead42(R)
  rule tokOps(iCons(47, iCons(47, R:IntSeq))) => oCons("//", tokOps(R))
  rule tokOps(iCons(47, R:IntSeq))     => oCons("/", tokOps(R)) requires notBool evHead47(R)
  rule tokOps(iCons(43, R:IntSeq))     => oCons("+", tokOps(R))
  rule tokOps(iCons(45, R:IntSeq))     => oCons("-", tokOps(R))

  syntax IntSeq ::= tokNds(IntSeq) [function, total]
                  | tokNdAcc(Int, IntSeq) [function, total]
  rule tokNds(.IntSeq)                => .IntSeq
  rule tokNds(iCons(32, R:IntSeq))    => tokNds(R)
  rule tokNds(iCons(C:Int, R:IntSeq)) => tokNdAcc(C -Int 48, R) requires evDigit(C)
  rule tokNds(iCons(C:Int, R:IntSeq)) => tokNds(R)
       requires notBool evDigit(C) andBool C =/=Int 32
  rule tokNdAcc(A:Int, iCons(C:Int, R:IntSeq)) => tokNdAcc(A *Int 10 +Int (C -Int 48), R)
       requires evDigit(C)
  rule tokNdAcc(A:Int, S:IntSeq) => iCons(A, tokNds(S)) [owise]

  syntax EvPair ::= evp(OpSeq, IntSeq)
  syntax Int ::= firstNdE(EvPair) [function, total]
  rule firstNdE(evp(_:OpSeq, iCons(N:Int, _:IntSeq))) => N
  rule firstNdE(_:EvPair) => 0 [owise]

  syntax Int ::= applyOpE(String, Int, Int) [function, total]
  rule applyOpE("+",  A:Int, B:Int) => A +Int B
  rule applyOpE("-",  A:Int, B:Int) => A -Int B
  rule applyOpE("*",  A:Int, B:Int) => A *Int B
  rule applyOpE("//", A:Int, B:Int) => A divInt B
  rule applyOpE("**", A:Int, B:Int) => A ^Int B
  rule applyOpE(_:String, A:Int, _:Int) => A [owise]

  syntax EvPair ::= passPowE(OpSeq, IntSeq) [function, total]
  rule passPowE(.OpSeq, NDS:IntSeq) => evp(.OpSeq, NDS)
  rule passPowE(oCons("**", OPS:OpSeq), iCons(N:Int, NDS:IntSeq)) => powCombE(N, passPowE(OPS, NDS))
  rule passPowE(oCons(O:String, OPS:OpSeq), iCons(N:Int, NDS:IntSeq)) => powCarryE(O, N, passPowE(OPS, NDS))
       requires O =/=String "**"
  rule passPowE(_:OpSeq, .IntSeq) => evp(.OpSeq, .IntSeq) [owise]
  syntax EvPair ::= powCombE(Int, EvPair) [function, total]
  rule powCombE(N:Int, evp(OPS:OpSeq, iCons(M:Int, REST:IntSeq))) => evp(OPS, iCons(N ^Int M, REST))
  rule powCombE(N:Int, evp(OPS:OpSeq, .IntSeq)) => evp(OPS, iCons(N, .IntSeq))
  syntax EvPair ::= powCarryE(String, Int, EvPair) [function, total]
  rule powCarryE(O:String, N:Int, evp(OPS:OpSeq, NDS:IntSeq)) => evp(oCons(O, OPS), iCons(N, NDS))

  syntax EvPair ::= passMulE(EvPair) [function, total] | passAddE(EvPair) [function, total]
  rule passMulE(evp(OPS:OpSeq, iCons(N0:Int, NDS:IntSeq))) => passLGoE("mul", N0, OPS, NDS, .OpSeq, .IntSeq)
  rule passMulE(evp(OPS:OpSeq, .IntSeq)) => evp(OPS, .IntSeq)
  rule passAddE(evp(OPS:OpSeq, iCons(N0:Int, NDS:IntSeq))) => passLGoE("add", N0, OPS, NDS, .OpSeq, .IntSeq)
  rule passAddE(evp(OPS:OpSeq, .IntSeq)) => evp(OPS, .IntSeq)
  syntax EvPair ::= passLGoE(String, Int, OpSeq, IntSeq, OpSeq, IntSeq) [function, total]
  rule passLGoE(_:String, CUR:Int, .OpSeq, _:IntSeq, OO:OpSeq, ON:IntSeq) => evp(OO, appendIE(ON, CUR))
  rule passLGoE(L:String, CUR:Int, oCons(O:String, OPS:OpSeq), iCons(N:Int, NDS:IntSeq), OO:OpSeq, ON:IntSeq)
    => passLGoE(L, applyOpE(O, CUR, N), OPS, NDS, OO, ON)
       requires inLevelE(L, O)
  rule passLGoE(L:String, CUR:Int, oCons(O:String, OPS:OpSeq), iCons(N:Int, NDS:IntSeq), OO:OpSeq, ON:IntSeq)
    => passLGoE(L, N, OPS, NDS, appendOpE(OO, O), appendIE(ON, CUR))
       requires notBool inLevelE(L, O)
  rule passLGoE(_:String, CUR:Int, oCons(_:String, _:OpSeq), .IntSeq, OO:OpSeq, ON:IntSeq)
    => evp(OO, appendIE(ON, CUR)) [owise]
  syntax Bool ::= inLevelE(String, String) [function, total]
  rule inLevelE("mul", O:String) => O ==String "*" orBool O ==String "//" orBool O ==String "/"
  rule inLevelE("add", O:String) => O ==String "+" orBool O ==String "-"
  rule inLevelE(_:String, _:String) => false [owise]
  syntax OpSeq ::= appendOpE(OpSeq, String) [function, total]
  rule appendOpE(.OpSeq, O:String) => oCons(O, .OpSeq)
  rule appendOpE(oCons(H:String, T:OpSeq), O:String) => oCons(H, appendOpE(T, O))
  syntax IntSeq ::= appendIE(IntSeq, Int) [function, total]
  rule appendIE(.IntSeq, N:Int) => iCons(N, .IntSeq)
  rule appendIE(iCons(H:Int, T:IntSeq), N:Int) => iCons(H, appendIE(T, N))

  // ==== hashlib.md5(S).hexdigest() — a trusted opaque digest ==================
  // The md5 value itself is a named shared trust (sortVS-style, no concrete
  // twin); proofs use the length/hex-charset lemmas (lemmas/builtins.k).
  syntax KItem ::= "#md5"
  rule <k> Call(Attribute(Name("hashlib"), "md5"), (E:Expr, .Exprs)) => E ~> #md5 ... </k>
       [priority(40)]
  rule <k> str(CS:IntSeq) ~> #md5 => md5Obj(CS) ... </k>
  syntax Val ::= md5Obj(IntSeq)
  rule applyMethod(md5Obj(CS:IntSeq), "hexdigest", .Vals) => str(md5hexCodes(CS))
  syntax IntSeq ::= md5hexCodes(IntSeq) [function, total, symbol(md5hexCodes), no-evaluators]

  // ==== isinstance(V, int|str) — an ordinary 2-arg builtin ===================
  // The type argument (int/str) is an ordinary name that resolves via the builtins frame to
  // typeV (see core.k's config); no Call-level special case. isIntV/isStrV mirror the old
  // owise-on-Val test (concrete-sort args decide; a symbolic Val stays owise, as before).
  rule applyBuiltin("isinstance", V:Val, typeV("int"), .Vals) => isIntV(V)
  rule applyBuiltin("isinstance", V:Val, typeV("str"), .Vals) => isStrV(V)
  syntax Bool ::= isIntV(Val) [function] | isStrV(Val) [function]
  rule isIntV(_:Int)         => true
  rule isIntV(_:Val)         => false [owise]
  rule isStrV(str(_:IntSeq)) => true
  rule isStrV(_:Val)         => false [owise]
endmodule
