// reference/src/semantics/methods.k — MPY-METHODS

module MPY-METHODS
  imports MPY-CORE
  imports K-EQUAL
  imports MPY-STR
  imports MPY-LIST

  // method-call routing + arg-eval live in call.k; this module owns applyMethod.
  syntax Val ::= applyMethod(Val, String, Vals) [function]

  // ==== string predicates (Python semantics) =================================
  rule applyMethod(str(CS:IntSeq), "isupper", .Vals) => hasUpper(CS) andBool notBool hasLower(CS)
  rule applyMethod(str(CS:IntSeq), "islower", .Vals) => hasLower(CS) andBool notBool hasUpper(CS)
  rule applyMethod(str(CS:IntSeq), "isalpha", .Vals) => notBool (CS ==K .IntSeq) andBool allAlpha(CS)
  rule applyMethod(str(CS:IntSeq), "isdigit", .Vals) => notBool (CS ==K .IntSeq) andBool allDigit(CS)

  // ==== case maps ============================================================
  rule applyMethod(str(CS:IntSeq), "lower",    .Vals) => str(mapLower(CS))
  rule applyMethod(str(CS:IntSeq), "upper",    .Vals) => str(mapUpper(CS))
  rule applyMethod(str(CS:IntSeq), "swapcase", .Vals) => str(mapSwap(CS))

  // ==== join / count / strip / encode ========================================
  // S.join(list-of-str): fold with separator codes (receiver + arg deref'd by
  // the call layer; the result str is a value)
  rule applyMethod(str(SEP:IntSeq), "join", list(VS:ValSeq), .Vals) => str(joinCodes(SEP, VS))
  syntax IntSeq ::= joinCodes(IntSeq, ValSeq) [function, total]
  rule joinCodes(_:IntSeq, .ValSeq) => .IntSeq
  rule joinCodes(_:IntSeq, vCons(str(CS:IntSeq), .ValSeq)) => CS
  rule joinCodes(SEP:IntSeq, vCons(str(CS:IntSeq), vCons(V:Val, R:ValSeq)))
    => seqConcat(CS, seqConcat(SEP, joinCodes(SEP, vCons(V, R))))

  // S.count(sub): non-overlapping window scan (Python str.count)
  rule applyMethod(str(CS:IntSeq), "count", str(PC:IntSeq), .Vals) => cntSub(CS, PC)
  syntax Int ::= cntSub(IntSeq, IntSeq) [function]
  rule cntSub(.IntSeq, _:IntSeq) => 0
  rule cntSub(iCons(C:Int, R:IntSeq), PC:IntSeq) => 1 +Int cntSub(dropIS(iCons(C, R), isLen(PC)), PC)
       requires strPrefix(PC, iCons(C, R)) andBool isLen(PC) >Int 0
  rule cntSub(iCons(C:Int, R:IntSeq), PC:IntSeq) => cntSub(R, PC)
       requires notBool strPrefix(PC, iCons(C, R)) orBool isLen(PC) <=Int 0
  syntax IntSeq ::= dropIS(IntSeq, Int) [function, total]
  rule dropIS(S:IntSeq, N:Int) => S requires N <=Int 0
  rule dropIS(.IntSeq, _:Int) => .IntSeq [owise]
  rule dropIS(iCons(_:Int, R:IntSeq), N:Int) => dropIS(R, N -Int 1) requires N >Int 0

  // S.strip(): trim whitespace runs from both ends
  rule applyMethod(str(CS:IntSeq), "strip", .Vals) => str(revIS(trimWS(revIS(trimWS(CS)))))
  syntax IntSeq ::= trimWS(IntSeq) [function, total]
  rule trimWS(.IntSeq) => .IntSeq
  rule trimWS(iCons(C:Int, R:IntSeq)) => trimWS(R) requires isWSC(C)
  rule trimWS(iCons(C:Int, R:IntSeq)) => iCons(C, R) requires notBool isWSC(C)
  syntax IntSeq ::= revIS(IntSeq) [function, total] | revISAcc(IntSeq, IntSeq) [function, total]
  rule revIS(S:IntSeq) => revISAcc(S, .IntSeq)
  rule revISAcc(.IntSeq, A:IntSeq) => A
  rule revISAcc(iCons(C:Int, R:IntSeq), A:IntSeq) => revISAcc(R, iCons(C, A))

  // S.encode('ascii'): identity on the code-sequence model (bytes == codes)
  rule applyMethod(str(CS:IntSeq), "encode", str(_:IntSeq), .Vals) => str(CS)

  // ==== prefix ===============================================================
  rule applyMethod(str(XC:IntSeq), "startswith", str(PC:IntSeq), .Vals) => startsWith(PC, XC)

  // ==== list.count(v) — number of occurrences of v in the list (concrete for krun) ==========
  rule applyMethod(list(VS:ValSeq), "count", V:Val, .Vals) => cntOccVS(VS, V)
  syntax Int ::= cntOccVS(ValSeq, Val) [function, total]
  rule cntOccVS(.ValSeq, _:Val)                => 0
  rule cntOccVS(vCons(A:Val, R:ValSeq), V:Val) => 1 +Int cntOccVS(R, V) requires A ==K V
  rule cntOccVS(vCons(A:Val, R:ValSeq), V:Val) => cntOccVS(R, V)        requires notBool (A ==K V)

  // ==== split (no-arg: on whitespace runs, dropping empty tokens) + replace (single char) ==========
  // Concrete string ops for krun. A proof over a symbolic string intercepts the split problem-locally.
  rule <k> #applyK(toCall(boundMethodV(str(CS:IntSeq), "split")), .Vals)
        => #alloc(list(splitWS(CS, .IntSeq, .ValSeq))) ... </k>
       [priority(40)]
  syntax ValSeq ::= splitWS(IntSeq, IntSeq, ValSeq) [function]  // remaining, current token, result
  rule splitWS(.IntSeq, CUR:IntSeq, ACC:ValSeq) => flushTok(ACC, CUR)
  rule splitWS(iCons(C:Int, R:IntSeq), CUR:IntSeq, ACC:ValSeq) => splitWS(R, .IntSeq, flushTok(ACC, CUR))
       requires isWSC(C)
  rule splitWS(iCons(C:Int, R:IntSeq), CUR:IntSeq, ACC:ValSeq) => splitWS(R, seqConcat(CUR, iCons(C, .IntSeq)), ACC)
       requires notBool isWSC(C)
  // flush the current token to the result list iff non-empty.
  syntax ValSeq ::= flushTok(ValSeq, IntSeq) [function]
  rule flushTok(ACC:ValSeq, .IntSeq)            => ACC
  rule flushTok(ACC:ValSeq, iCons(C:Int, T:IntSeq)) => valSeqConcat(ACC, vCons(str(iCons(C, T)), .ValSeq))
  syntax Bool ::= isWSC(Int) [function, total]
  rule isWSC(C:Int) => C ==Int 32 orBool C ==Int 9 orBool C ==Int 10 orBool C ==Int 13

  // split(sep='x') keyword form delegates to the positional k-cell rule
  rule <k> #applyK(toCall(boundMethodV(str(CS:IntSeq), "split")), (kwV("sep", str(S:IntSeq)), .Vals))
        => #applyK(toCall(boundMethodV(str(CS), "split")), (str(S), .Vals)) ... </k>
       [priority(39)]

  // str.split(sep) — single-char separator, KEEPING empty parts (Python's sep-split; len == #sep + 1).
  rule <k> #applyK(toCall(boundMethodV(str(CS:IntSeq), "split")), (str(iCons(SEP:Int, .IntSeq)), .Vals))
        => #alloc(list(splitSep(CS, SEP, .IntSeq))) ... </k>
       [priority(40)]
  syntax ValSeq ::= splitSep(IntSeq, Int, IntSeq) [function]  // remaining, sep code, current token
  rule splitSep(.IntSeq, _SEP:Int, CUR:IntSeq)              => vCons(str(CUR), .ValSeq)
  rule splitSep(iCons(C:Int, R:IntSeq), SEP:Int, CUR:IntSeq) => vCons(str(CUR), splitSep(R, SEP, .IntSeq))
       requires C ==Int SEP
  rule splitSep(iCons(C:Int, R:IntSeq), SEP:Int, CUR:IntSeq) => splitSep(R, SEP, seqConcat(CUR, iCons(C, .IntSeq)))
       requires notBool (C ==Int SEP)

  rule applyMethod(str(CS:IntSeq), "replace", str(iCons(A:Int, .IntSeq)), str(iCons(B:Int, .IntSeq)), .Vals)
    => str(replaceC(CS, A, B))
  syntax IntSeq ::= replaceC(IntSeq, Int, Int) [function, total]
  rule replaceC(.IntSeq, _:Int, _:Int)             => .IntSeq
  rule replaceC(iCons(C:Int, R:IntSeq), A:Int, B:Int) => iCons(B, replaceC(R, A, B)) requires C ==Int A
  rule replaceC(iCons(C:Int, R:IntSeq), A:Int, B:Int) => iCons(C, replaceC(R, A, B)) requires notBool (C ==Int A)

  // ==== char helpers =========================================================
  syntax Bool ::= isUpperC(Int) [function, total]
  rule isUpperC(C:Int) => C >=Int 65 andBool C <=Int 90

  syntax Bool ::= isLowerC(Int) [function, total]
  rule isLowerC(C:Int) => C >=Int 97 andBool C <=Int 122

  syntax Bool ::= isAlphaC(Int) [function, total]
  rule isAlphaC(C:Int) => isUpperC(C) orBool isLowerC(C)

  syntax Bool ::= isDigitC(Int) [function, total]
  rule isDigitC(C:Int) => C >=Int 48 andBool C <=Int 57

  syntax Bool ::= hasUpper(IntSeq) [function, total]
  rule hasUpper(.IntSeq) => false
  rule hasUpper(iCons(C:Int, S:IntSeq)) => isUpperC(C) orBool hasUpper(S)

  syntax Bool ::= hasLower(IntSeq) [function, total]
  rule hasLower(.IntSeq) => false
  rule hasLower(iCons(C:Int, S:IntSeq)) => isLowerC(C) orBool hasLower(S)

  syntax Bool ::= allAlpha(IntSeq) [function, total]
  rule allAlpha(.IntSeq) => true
  rule allAlpha(iCons(C:Int, S:IntSeq)) => isAlphaC(C) andBool allAlpha(S)

  syntax Bool ::= allDigit(IntSeq) [function, total]
  rule allDigit(.IntSeq) => true
  rule allDigit(iCons(C:Int, S:IntSeq)) => isDigitC(C) andBool allDigit(S)

  syntax Int ::= lowerC(Int) [function, total]

  rule lowerC(C:Int) => C +Int 32 requires isUpperC(C)
  rule lowerC(C:Int) => C         [owise]

  syntax Int ::= upperC(Int) [function, total]
  rule upperC(C:Int) => C -Int 32 requires isLowerC(C)
  rule upperC(C:Int) => C         [owise]

  syntax Int ::= swapC(Int) [function, total]
  rule swapC(C:Int) => C +Int 32 requires isUpperC(C)
  rule swapC(C:Int) => C -Int 32 requires isLowerC(C)
  rule swapC(C:Int) => C         [owise]

  syntax IntSeq ::= mapLower(IntSeq) [function, total]
  rule mapLower(.IntSeq) => .IntSeq
  rule mapLower(iCons(C:Int, S:IntSeq)) => iCons(lowerC(C), mapLower(S))

  syntax IntSeq ::= mapUpper(IntSeq) [function, total]
  rule mapUpper(.IntSeq) => .IntSeq
  rule mapUpper(iCons(C:Int, S:IntSeq)) => iCons(upperC(C), mapUpper(S))

  syntax IntSeq ::= mapSwap(IntSeq) [function, total]
  rule mapSwap(.IntSeq) => .IntSeq
  rule mapSwap(iCons(C:Int, S:IntSeq)) => iCons(swapC(C), mapSwap(S))

  syntax Bool ::= startsWith(IntSeq, IntSeq) [function, total]
  rule startsWith(.IntSeq, _:IntSeq)               => true
  rule startsWith(iCons(_:Int, _:IntSeq), .IntSeq) => false
  rule startsWith(iCons(A:Int, As:IntSeq), iCons(B:Int, Bs:IntSeq)) => A ==Int B andBool startsWith(As, Bs)
endmodule
