// reference/src/lemmas/str-int-decimal.k — STR-INT-DECIMAL-LEMMAS

requires "../semantics.k"
requires "casts.k"

module STR-INT-DECIMAL-LEMMAS
  imports MPY
  imports CASTS-LEMMAS

  // the opaque carrier: an integer presented by its decimal digit-code sequence CS
  syntax Int ::= intOfD(IntSeq) [function, total, no-evaluators, symbol(intOfD)]

  syntax Bool ::= validDec(IntSeq) [function, total]
  rule validDec(.IntSeq)                              => false
  rule validDec(iCons(C:Int, .IntSeq))                => 48 <=Int C andBool C <=Int 57
  rule validDec(iCons(C:Int, iCons(D:Int, T:IntSeq))) => (49 <=Int C andBool C <=Int 57) andBool allDigit(iCons(D, T))

  // strToCodes and Int2String are reverse on intOfD(CS)
  rule strToCodes(Int2String(intOfD(CS:IntSeq))) => CS requires validDec(CS) [simplification]

  // the decimal digit codes of a non-negative int (the trusted model of the
  // shared str(int) route on a symbolic argument, where Int2String is
  // hookless; concrete unfolds agree with the hooked route)
  syntax IntSeq ::= digitCodes(Int) [function, total]
  rule digitCodes(N:Int) => iCons(48 +Int N, .IntSeq)
    requires N >=Int 0 andBool N <Int 10 [simplification]
  rule digitCodes(N:Int)
    => seqConcat(digitCodes((N -Int pyMod(N, 10)) /Int 10), iCons(48 +Int pyMod(N, 10), .IntSeq))
    requires N >=Int 10 [simplification]
  rule strToCodes(Int2String(I:Int)) => digitCodes(I) requires I >=Int 0 [simplification]
  // str() on an abstract int element: the composed shared route (plain str
  // dispatch + the bridge above) through the total Int projection
  rule applyBuiltin("str", V:Val, .Vals) => str(digitCodes(projectIntTotal(V)))
    requires isInt(V) andBool projectIntTotal(V) >=Int 0 [simplification]

  // digit number is non-negative
  rule absInt(intOfD(CS:IntSeq)) => intOfD(CS) requires allDigit(CS) [simplification]
  rule intOfD(CS:IntSeq) >=Int 0 => true       requires allDigit(CS) [simplification]
  rule intOfD(CS:IntSeq) <Int 0  => false      requires allDigit(CS) [simplification]
endmodule
