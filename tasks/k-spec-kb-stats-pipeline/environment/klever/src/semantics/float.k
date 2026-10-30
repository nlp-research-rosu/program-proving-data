// reference/src/semantics/float.k — MPY-FLOAT
//
// Minimal, TRUSTED float support. K/Haskell (kprove) has no usable symbolic IEEE-754 theory and
// no Int2Float hook, so a float value stays an OPAQUE proof-domain primitive: `intFloatDiv(I, F)`
// (the Python true division I / F) is `[no-evaluators]` for kprove — it never reduces on symbolic
// input, and the proof verifies only the STRUCTURE (the result is the exact term the program
// builds). The `[concrete]` rule evaluates it for krun (llvm HAS the Int2Float / /Float hooks), so
// smoke tests run the real float value.
//
// Only the pieces needed so far: Float as a Val, the float literal, and Int / float true division
// (the `a * h / 2.0` idiom). More float ops (float +/-/*, comparison) are added as float problems
// need them — kept minimal + sound.

module MPY-FLOAT
  imports MPY-OPERATORS
  imports MPY-BUILTINS
  imports FLOAT

  // Float is a value; the float literal evaluates to the K Float.
  syntax Val ::= Float
  rule <k> Float(F:Float) => F ... </k>

  // Int / float true division. OPAQUE for kprove (no-evaluators); concrete for krun.
  syntax Float ::= intFloatDiv(Int, Float) [function, total, symbol(intFloatDiv), no-evaluators]
  rule intFloatDiv(I:Int, F:Float) => Int2Float(I, 53, 11) /Float F [concrete]

  rule applyBin("/", I:Int, F:Float) => intFloatDiv(I, F)

  // Int / Int true division (Python: always a float). OPAQUE for kprove; concrete for krun.
  syntax Float ::= divII(Int, Int) [function, total, symbol(divII), no-evaluators]
  rule divII(I1:Int, I2:Int) => Int2Float(I1, 53, 11) /Float Int2Float(I2, 53, 11) [concrete]
  rule applyBin("/", I1:Int, I2:Int) => divII(I1, I2)

  // float % float (e.g. `number % 1.0` = the fractional part). OPAQUE for kprove, concrete for
  // krun. Python's float `%` is floor-based: a % b = a - floor(a/b)*b (K's %Float is IEEE
  // remainder, which differs — 3.5 %Float 1.0 = -0.5 vs Python 0.5 — so it is NOT used).
  syntax Float ::= floatMod(Float, Float) [function, total, symbol(floatMod), no-evaluators]
  rule floatMod(F1:Float, F2:Float) => F1 -Float (floorFloat(F1 /Float F2) *Float F2) [concrete]
  rule applyBin("%", F1:Float, F2:Float) => floatMod(F1, F2)

  // float equality — for concrete krun asserts (e.g. `area == 7.5`); the FLOAT.eq hook is fine on
  // concrete floats. kprove proofs return floats structurally and do not compare them.
  rule applyCmp("==", F1:Float, F2:Float) => F1 ==Float F2
  rule applyCmp("!=", F1:Float, F2:Float) => notBool (F1 ==Float F2)

  // float `<` and abs — OPAQUE for kprove ([no-evaluators], so a SYMBOLIC float compare stays an
  // uninterpreted Bool a proof case-splits on — a SINGLE compare per branch, not a nonlinear cascade),
  // [concrete] for krun. Additive, sort-disjoint from the Int rules. (has_close_elements: the pairwise
  // `abs(a-b) < t` proximity test.)
  syntax Bool ::= floatLt(Float, Float) [function, total, symbol(floatLt), no-evaluators]
  rule floatLt(F1:Float, F2:Float) => F1 <Float F2 [concrete]
  rule applyCmp("<", F1:Float, F2:Float) => floatLt(F1, F2)

  syntax Float ::= absF(Float) [function, total, symbol(absF), no-evaluators]
  rule absF(F:Float) => absFloat(F) [concrete]
  rule applyBuiltin("abs", F:Float, .Vals) => absF(F)

  // ==== math.ceil ===========================================================
  // `import X` is a no-op (we intercept the specific math functions syntactically; `math` itself is
  // never bound as a value).
  rule <k> Import(_:String) => .K ... </k>

  // math.ceil(x): ceiling to an int. Intercepted at the Call BEFORE `math` is looked up (higher
  // priority than the generic Attribute/method dispatch in call.k).
  syntax KItem ::= "#mathCeil"
  rule <k> Call(Attribute(Name("math"), "ceil"), (E:Expr, .Exprs)) => E ~> #mathCeil ... </k> [priority(40)]
  rule <k> V:Val ~> #mathCeil => ceilF(V) ... </k>

  // math.floor(x) — same interception shape as math.ceil
  syntax KItem ::= "#mathFloor"
  rule <k> Call(Attribute(Name("math"), "floor"), (E:Expr, .Exprs)) => E ~> #mathFloor ... </k> [priority(40)]
  rule <k> V:Val ~> #mathFloor => floorFI(V) ... </k>
  syntax Int ::= floorFI(Val) [function, total, symbol(floorFI)]
  rule floorFI(I:Int)   => I                        [concrete]
  rule floorFI(F:Float) => Float2Int(floorFloat(F)) [concrete]

  // bare floor/ceil (bound by `from math import floor, ceil`)
  rule applyBuiltin("floor", V:Val, .Vals) => floorFI(V)
  rule applyBuiltin("ceil",  V:Val, .Vals) => ceilF(V)

  // math.pow(x, y) — a two-arg interception onto powF (ints promote)
  syntax KItem ::= #mathPow1(Expr) | #mathPow2(Val)
  rule <k> Call(Attribute(Name("math"), "pow"), (E1:Expr, E2:Expr, .Exprs)) => E1 ~> #mathPow1(E2) ... </k> [priority(40)]
  rule <k> V1:Val ~> #mathPow1(E2:Expr) => E2 ~> #mathPow2(V1) ... </k>
  rule <k> V2:Val ~> #mathPow2(V1:Val) => powF(toF(V1), toF(V2)) ... </k>
  syntax Float ::= toF(Val) [function, total, symbol(toF)]
  rule toF(F:Float) => F        [concrete]
  rule toF(I:Int)   => intToF(I) [concrete]

  // ceilF: math.ceil as an Int. TOTAL (K trusts it; a symbolic list element stays opaque for
  // kprove — structural). [concrete] so the Int2Float/ceilFloat hooks only run for krun (llvm).
  // Matches Python incl. negatives: ceil(-2.4) = -2 = Float2Int(ceilFloat(-2.4)).
  syntax Int ::= ceilF(Val) [function, total, symbol(ceilF)]
  rule ceilF(I:Int)   => I                       [concrete]
  rule ceilF(F:Float) => Float2Int(ceilFloat(F)) [concrete]

  // unary minus on a float (e.g. the literal -2.4 = UnaryOp("-", Float(2.4))). Concrete for krun;
  // proofs use symbolic elements, never a float literal.
  rule applyUn("-", F:Float) => 0.0 -Float F

  // ---- float - / / / + (OPAQUE for kprove [no-evaluators], concrete for krun) — for float-list
  // element maps (x - lo) / (hi - lo). Mirror intFloatDiv: additive, sort-disjoint from the Int rules.
  syntax Float ::= subF(Float, Float) [function, total, symbol(subF), no-evaluators]
  rule subF(F1:Float, F2:Float) => F1 -Float F2 [concrete]
  rule applyBin("-", F1:Float, F2:Float) => subF(F1, F2)

  syntax Float ::= divF(Float, Float) [function, total, symbol(divF), no-evaluators]
  rule divF(F1:Float, F2:Float) => F1 /Float F2 [concrete]
  rule applyBin("/", F1:Float, F2:Float) => divF(F1, F2)

  syntax Float ::= addF(Float, Float) [function, total, symbol(addF), no-evaluators]
  rule addF(F1:Float, F2:Float) => F1 +Float F2 [concrete]
  rule applyBin("+", F1:Float, F2:Float) => addF(F1, F2)

  syntax Float ::= mulF(Float, Float) [function, total, symbol(mulF), no-evaluators]
  rule mulF(F1:Float, F2:Float) => F1 *Float F2 [concrete]
  rule applyBin("*", F1:Float, F2:Float) => mulF(F1, F2)

  syntax Float ::= powF(Float, Float) [function, total, symbol(powF), no-evaluators]
  rule powF(F1:Float, F2:Float) => F1 ^Float F2 [concrete]
  rule applyBin("**", F1:Float, F2:Float) => powF(F1, F2)

  // ---- the remaining comparisons (gtF promoted from find_zero — its summaries
  //      case-split on the atom; >= / <= derive from the two opaque compares) ----
  syntax Bool ::= gtF(Float, Float) [function, total, symbol(gtF), no-evaluators]
  rule gtF(F1:Float, F2:Float) => F1 >Float F2 [concrete]
  rule applyCmp(">",  F1:Float, F2:Float) => gtF(F1, F2)
  rule applyCmp(">=", F1:Float, F2:Float) => notBool floatLt(F1, F2)
  rule applyCmp("<=", F1:Float, F2:Float) => notBool gtF(F1, F2)

  // ---- mixed Int/Float operators promote the Int side (n ** 0.5 etc.) ----
  rule applyBin("**", I:Int, F:Float) => powF(intToF(I), F)
  rule applyBin("**", F:Float, I:Int) => powF(F, intToF(I))
  rule applyBin("-",  I:Int, F:Float) => subF(intToF(I), F)
  rule applyBin("-",  F:Float, I:Int) => subF(F, intToF(I))
  rule applyBin("+",  I:Int, F:Float) => addF(intToF(I), F)
  rule applyBin("+",  F:Float, I:Int) => addF(F, intToF(I))
  rule applyBin("*",  I:Int, F:Float) => mulF(intToF(I), F)
  rule applyBin("*",  F:Float, I:Int) => mulF(F, intToF(I))

  // ---- mixed Int == Float (shared eqF; opaque symbolic / concrete twin) ----
  syntax Bool ::= eqF(Float, Float) [function, total, symbol(eqF), no-evaluators]
  rule eqF(F1:Float, F2:Float) => F1 ==Float F2 [concrete]
  rule applyCmp("==", I:Int, F:Float) => eqF(intToF(I), F)
  rule applyCmp("==", F:Float, I:Int) => eqF(F, intToF(I))
  rule applyCmp("!=", I:Int, F:Float) => notBool eqF(intToF(I), F)
  rule applyCmp("!=", F:Float, I:Int) => notBool eqF(F, intToF(I))
  rule applyCmp("<",  I:Int, F:Float) => floatLt(intToF(I), F)
  rule applyCmp("<",  F:Float, I:Int) => floatLt(F, intToF(I))
  rule applyCmp(">",  I:Int, F:Float) => gtF(intToF(I), F)
  rule applyCmp(">",  F:Float, I:Int) => gtF(F, intToF(I))

  // ---- x == None (promoted from 137; `is` cases live in operators.k) ----
  rule applyCmp("==", V:Val, noneV) => V ==K noneV
  rule applyCmp("!=", V:Val, noneV) => notBool (V ==K noneV)

  // ---- float(str): decimal parse (promoted from 137's defined chain) ----
  // digits '.' digits, optional leading '-'; concrete evaluation only (the
  // symbolic side stays an opaque decStrToF term a proof case-splits on).
  syntax Float ::= decStrToF(IntSeq) [function, total, symbol(decStrToF), no-evaluators]
  rule decStrToF(iCons(45, CS:IntSeq)) => 0.0 -Float decStrToF(CS) [concrete]
  rule decStrToF(CS:IntSeq)
    => intToF(intPart(CS)) +Float (intToF(fracPart(CS)) /Float intToF(fracScale(CS)))
       requires isLen(CS) >Int 0 andBool headIS(CS) =/=Int 45 [concrete]
  syntax Int ::= headIS(IntSeq) [function]
  rule headIS(iCons(C:Int, _:IntSeq)) => C
  syntax Int ::= intPart(IntSeq) [function, total] | intPartAcc(IntSeq, Int) [function, total]
  rule intPart(CS:IntSeq) => intPartAcc(CS, 0)
  rule intPartAcc(.IntSeq, A:Int) => A
  rule intPartAcc(iCons(46, _:IntSeq), A:Int) => A
  rule intPartAcc(iCons(C:Int, R:IntSeq), A:Int) => intPartAcc(R, A *Int 10 +Int (C -Int 48))
       requires C =/=Int 46
  syntax Int ::= fracPart(IntSeq) [function, total] | fracAcc(IntSeq, Int) [function, total]
  rule fracPart(.IntSeq) => 0
  rule fracPart(iCons(46, R:IntSeq)) => fracAcc(R, 0)
  rule fracPart(iCons(C:Int, R:IntSeq)) => fracPart(R) requires C =/=Int 46
  rule fracAcc(.IntSeq, A:Int) => A
  rule fracAcc(iCons(C:Int, R:IntSeq), A:Int) => fracAcc(R, A *Int 10 +Int (C -Int 48))
  syntax Int ::= fracScale(IntSeq) [function, total] | fscAcc(IntSeq, Int) [function, total]
  rule fracScale(.IntSeq) => 1
  rule fracScale(iCons(46, R:IntSeq)) => fscAcc(R, 1)
  rule fracScale(iCons(C:Int, R:IntSeq)) => fracScale(R) requires C =/=Int 46
  rule fscAcc(.IntSeq, A:Int) => A
  rule fscAcc(iCons(_:Int, R:IntSeq), A:Int) => fscAcc(R, A *Int 10)
  rule applyBuiltin("float", str(CS:IntSeq), .Vals) => decStrToF(CS)
  rule applyBuiltin("float", I:Int, .Vals)          => intToF(I)
  rule applyBuiltin("float", F:Float, .Vals)        => F

  // ---- float / int division (promoted from mean_absolute_deviation) ----
  syntax Float ::= divFloatIntV(Float, Int) [function, total, symbol(divFloatIntV), no-evaluators]
  rule divFloatIntV(F:Float, I:Int) => F /Float Int2Float(I, 53, 11) [concrete]
  rule applyBin("/", F:Float, I:Int) => divFloatIntV(F, I)

  // ---- int -> float promotion for the remaining mixed arithmetic/compares ----
  syntax Float ::= intToF(Int) [function, total, symbol(intToF), no-evaluators]
  rule intToF(I:Int) => Int2Float(I, 53, 11) [concrete]
  rule applyBin("+", I:Int, F:Float) => addF(intToF(I), F)
  rule applyBin("+", F:Float, I:Int) => addF(F, intToF(I))
  rule applyBin("-", I:Int, F:Float) => subF(intToF(I), F)
  rule applyBin("-", F:Float, I:Int) => subF(F, intToF(I))
  rule applyBin("*", I:Int, F:Float) => mulF(intToF(I), F)
  rule applyBin("*", F:Float, I:Int) => mulF(F, intToF(I))
  rule applyCmp("<", I:Int, F:Float) => floatLt(intToF(I), F)
  rule applyCmp("<", F:Float, I:Int) => floatLt(F, intToF(I))
  rule applyCmp(">", I:Int, F:Float) => gtF(intToF(I), F)
  rule applyCmp(">", F:Float, I:Int) => gtF(F, intToF(I))

  // ---- conversions: int(float) truncates toward zero; float(int); round; math.sqrt ----
  syntax Int ::= truncF(Float) [function, total, symbol(truncF), no-evaluators]
  rule truncF(F:Float) => #if F >=Float 0.0 #then Float2Int(floorFloat(F)) #else Float2Int(ceilFloat(F)) #fi [concrete]
  rule applyBuiltin("int", F:Float, .Vals) => truncF(F)

  rule applyBuiltin("float", I:Int, .Vals)   => intToF(I)
  rule applyBuiltin("float", F:Float, .Vals) => F

  // round: Python half-even (banker's); round(F, N) scales by 10^N
  syntax Int ::= roundF(Float) [function, total, symbol(roundF), no-evaluators]
  rule roundF(F:Float)
    => #if (F -Float floorFloat(F)) ==Float 0.5
       #then (#if Float2Int(floorFloat(F)) %Int 2 ==Int 0
              #then Float2Int(floorFloat(F)) #else Float2Int(ceilFloat(F)) #fi)
       #else Float2Int(floorFloat(F +Float 0.5)) #fi [concrete]
  syntax Float ::= roundFN(Float, Int) [function, total, symbol(roundFN), no-evaluators]
  rule roundFN(F:Float, N:Int)
    => Int2Float(roundF(F *Float Int2Float(10 ^Int N, 53, 11)), 53, 11)
       /Float Int2Float(10 ^Int N, 53, 11) [concrete]
  rule applyBuiltin("round", F:Float, .Vals)        => roundF(F)
  rule applyBuiltin("round", F:Float, N:Int, .Vals) => roundFN(F, N)

  syntax Float ::= sqrtF(Float) [function, total, symbol(sqrtF), no-evaluators]
  rule sqrtF(F:Float) => sqrtFloat(F) [concrete]
  syntax KItem ::= "#mathSqrt"
  rule <k> Call(Attribute(Name("math"), "sqrt"), (E:Expr, .Exprs)) => E ~> #mathSqrt ... </k> [priority(40)]
  rule <k> F:Float ~> #mathSqrt => sqrtF(F) ... </k>
  rule <k> I:Int ~> #mathSqrt => sqrtF(intToF(I)) ... </k>

  // ---- min / max over a FLOAT list — FLOAT branch of the shared #minCont0/#maxCont0 folds (which
  // seed/step with `requires isInt(V)`, so they are STUCK on floats). These add the `requires
  // isFloat(V)` seed + a Float-accumulator fold via K's minFloat/maxFloat — concrete for krun. A proof
  // over a SYMBOLIC float list intercepts min/max problem-locally to an opaque minVF/maxVF (at
  // #applyK, priority 40, in its verification.k) BEFORE #minAcc0, so this fold is krun-only. Additive:
  // the isFloat guard is disjoint from the existing isInt one.
  syntax KItem ::= #maxAccF(Iterable, Float) | #maxContF(Float)
  rule <k> #iterYield(V:Val, R:Iterable) ~> #maxCont0 => #maxAccF(R, {V}:>Float) ... </k> requires isFloat(V)
  rule <k> #maxAccF(IT:Iterable, M:Float) => #iterNext(IT) ~> #maxContF(M) ... </k>
  rule <k> #iterDone ~> #maxContF(M:Float) => M ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #maxContF(M:Float) => #maxAccF(R, maxFloat(M, {V}:>Float)) ... </k>
       requires isFloat(V)

  syntax KItem ::= #minAccF(Iterable, Float) | #minContF(Float)
  rule <k> #iterYield(V:Val, R:Iterable) ~> #minCont0 => #minAccF(R, {V}:>Float) ... </k> requires isFloat(V)
  rule <k> #minAccF(IT:Iterable, M:Float) => #iterNext(IT) ~> #minContF(M) ... </k>
  rule <k> #iterDone ~> #minContF(M:Float) => M ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #minContF(M:Float) => #minAccF(R, minFloat(M, {V}:>Float)) ... </k>
       requires isFloat(V)

  // ---- sum over a float list (krun; mirrors the min/max float paths). The Int-only shared
  // #sumCont sticks on a Float yield; switch to a Float-headed fold via addF (concrete twin).
  // The switch guard carries the SYNTACTIC negation of the Int rule's guard so a symbolic proof
  // with isInt(V) in its path condition refutes this branch without sort reasoning.
  syntax KItem ::= #sumAccF(Iterable, Float) | #sumContF(Float)
  rule <k> #iterYield(V:Val, R:Iterable) ~> #sumCont(ACC:Int)
        => #sumAccF(R, addF(intToF(ACC), {V}:>Float)) ... </k>
       requires isFloat(V) andBool notBool (isInt(V) orBool isBool(V))
  rule <k> #sumAccF(IT:Iterable, ACC:Float) => #iterNext(IT) ~> #sumContF(ACC) ... </k>
  rule <k> #iterDone ~> #sumContF(ACC:Float) => ACC ... </k>
  rule <k> #iterYield(V:Val, R:Iterable) ~> #sumContF(ACC:Float)
        => #sumAccF(R, addF(ACC, {V}:>Float)) ... </k>
       requires isFloat(V)
  rule <k> #iterYield(V:Val, R:Iterable) ~> #sumContF(ACC:Float)
        => #sumAccF(R, addF(ACC, intToF(intOf(V)))) ... </k>
       requires isInt(V) orBool isBool(V)
endmodule
