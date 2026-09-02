// reference/src/lemmas/builtins.k — BUILTINS-LEMMAS
// intOf on a symbolic int/bool Val, resolved by the element's sort (sum over List[int]/List[bool]).

requires "../semantics.k"
requires "casts.k"
requires "str.k"
requires "core.k"

module BUILTINS-LEMMAS
  imports MPY
  imports CASTS-LEMMAS
  imports STR-LEMMAS
  imports CORE-LEMMAS

  rule intOf(V:Val) => projectIntTotal(V)
    requires isInt(V)
    [simplification]
  rule intOf(V:Val) => #if projectBoolTotal(V) #then 1 #else 0 #fi
    requires isBool(V)
    [simplification]

  // chr of a symbolic code is the 1-char string of that code
  rule applyBuiltin("chr", I:Int, .Vals) => str(iCons(I, .IntSeq)) [simplification]

  // len of a symbolic str element bridges through the Str projection
  rule seqLen(V:Val) => isLen(codesProj(V)) requires isStr(V) [simplification]

  // a KNOWN-str receiver dispatches straight to applyMethod for the PURE
  // string predicates: the shared ref-deref narrower (call.k, priority 40)
  // would otherwise split an abstract receiver into ref junk branches first
  // (a str is never a ref). Methods with k-cell routes (split's alloc) must
  // NOT be captured here.
  rule <k> #applyK(toCall(boundMethodV(V:Val, "isdigit")), .Vals)
        => applyMethod(V, "isdigit", .Vals) ... </k>
    requires isStr(V)
    [priority(39)]

  // .isdigit() and int() on an abstract str element bridge the same way —
  // each echoes the shared str-constructor rule through codesProj
  rule applyMethod(V:Val, "isdigit", .Vals)
    => notBool (codesProj(V) ==K .IntSeq) andBool allDigit(codesProj(V))
    requires isStr(V) [simplification]
  rule applyBuiltin("int", V:Val, .Vals) => intDigAcc(codesProj(V), 0)
    requires isStr(V)
     andBool notBool (isLen(codesProj(V)) ==Int 0)
     andBool dgN(codesProj(V)) ==Int 1
    [simplification]
  // int() on an Int is the identity (the shared plain rule's twin, firing on
  // function-headed args like roundF terms)
  rule applyBuiltin("int", I:Int, .Vals) => I [simplification]
  // int() on a constructed str whose codes carry function terms (a subscript
  // element): the unguarded twin of the shared intDigAcc rule
  rule applyBuiltin("int", str(CS:IntSeq), .Vals) => intDigAcc(CS, 0) [simplification]

  // ==== md5hex trusted properties ============================================
  rule isLen(md5hexCodes(_:IntSeq)) => 32 [simplification]
  syntax Bool ::= allHexChar(IntSeq) [function, total]
  rule allHexChar(.IntSeq) => true
  rule allHexChar(iCons(C:Int, R:IntSeq))
    => ((C >=Int 48 andBool C <=Int 57) orBool (C >=Int 97 andBool C <=Int 102))
       andBool allHexChar(R)
  rule allHexChar(md5hexCodes(_:IntSeq)) => true [simplification]
endmodule
