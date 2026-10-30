// reference/src/semantics/subscript.k — MPY-SUBSCRIPT

module MPY-SUBSCRIPT
  imports MPY-CORE

  // ==== positional access + negative-index normalization (used only here) ===
  // valSeqAt is [total]: in-bounds vCons access reduces as usual; on an OPAQUE sequence (e.g.
  // a trusted sort's sortVS(VS)) or OOB it stays an abstract total value — so indexing the
  // opaque sorted list is DEFINED (no undischarged #Ceil), matching the old semantics' total
  // atK. K trusts the [total] annotation; valid programs index in-bounds.
  syntax Val ::= valSeqAt(ValSeq, Int) [function, total]
  rule valSeqAt(vCons(V:Val, _:ValSeq), 0)     => V
  rule valSeqAt(vCons(_:Val, S:ValSeq), I:Int) => valSeqAt(S, I -Int 1)
       requires I >Int 0

  syntax Int ::= intSeqAt(IntSeq, Int) [function]
  rule intSeqAt(iCons(C:Int, _:IntSeq), 0)     => C
  rule intSeqAt(iCons(_:Int, S:IntSeq), I:Int) => intSeqAt(S, I -Int 1)
       requires I >Int 0

  syntax Int ::= normIdx(Int, Int) [function, total]
  rule normIdx(I:Int, LEN:Int) => I +Int LEN requires I  <Int 0
  rule normIdx(I:Int, _:Int)   => I          requires I >=Int 0

  // ==== Subscript: indexing obj[i] (list / tuple / str) =====================
  // contexts (not strict attrs): the Index slot's Slice alternative must never heat
  context Subscript(HOLE, _)
  context Subscript(_:Val, HOLE:Expr)

  // heap-object deref (covers both the index and slice forms via the Index slot)
  rule <k> Subscript(ref(H:Int), IX:Index) => Subscript(V, IX) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]

  rule <k> Subscript(OBJ:Val, I:Int) => applyIndex(OBJ, I) ... </k>

  syntax Val ::= applyIndex(Val, Int) [function]
  rule applyIndex(list(VS:ValSeq),  I:Int) => valSeqAt(VS, normIdx(I, vsLen(VS)))
  rule applyIndex(tuple(VS:ValSeq), I:Int) => valSeqAt(VS, normIdx(I, vsLen(VS)))
  rule applyIndex(str(IS:IntSeq),   I:Int)
    => str(iCons(intSeqAt(IS, normIdx(I, isLen(IS))), .IntSeq))

  // ==== Slice: obj[lo:hi:step] (list / str) — CPython slice.indices ==========
  syntax KItem ::= #evalB(Bound) | "#toSome"
                 | #slLo(Val, Bound, Bound)
                 | #slHi(Val, OptInt, Bound)
                 | #slStep(Val, OptInt, OptInt)

  syntax OptInt ::= "noB" | someB(Int)
  rule <k> #evalB(NoBound)  => noB ... </k>
  rule <k> #evalB(E:Expr)   => E ~> #toSome ... </k>
  rule <k> I:Int ~> #toSome => someB(I) ... </k>

  rule <k> Subscript(OBJ:Val, Slice(LO:Bound, HI:Bound, ST:Bound)) => #evalB(LO) ~> #slLo(OBJ, HI, ST) ... </k>
  rule <k> LO:OptInt ~> #slLo(OBJ:Val, HI:Bound, ST:Bound)   => #evalB(HI) ~> #slHi(OBJ, LO, ST) ... </k>
  rule <k> HI:OptInt ~> #slHi(OBJ:Val, LO:OptInt, ST:Bound)  => #evalB(ST) ~> #slStep(OBJ, LO, HI) ... </k>
  // a list slice constructs a NEW object; a str slice stays a value
  rule <k> ST:OptInt ~> #slStep(list(VS:ValSeq), LO:OptInt, HI:OptInt)
        => #alloc(doSlice(list(VS), LO, HI, ST)) ... </k>
       [priority(45)]
  rule <k> ST:OptInt ~> #slStep(OBJ:Val, LO:OptInt, HI:OptInt) => doSlice(OBJ, LO, HI, ST) ... </k>

  syntax Val ::= doSlice(Val, OptInt, OptInt, OptInt) [function]
  rule doSlice(list(VS:ValSeq), LO:OptInt, HI:OptInt, ST:OptInt)
    => list(buildVS(VS, slStart(LO, ST, vsLen(VS)), slStop(HI, ST, vsLen(VS)), slStep(ST)))
  rule doSlice(tuple(VS:ValSeq), LO:OptInt, HI:OptInt, ST:OptInt)
    => tuple(buildVS(VS, slStart(LO, ST, vsLen(VS)), slStop(HI, ST, vsLen(VS)), slStep(ST)))
  rule doSlice(str(IS:IntSeq), LO:OptInt, HI:OptInt, ST:OptInt)
    => str(buildIS(IS, slStart(LO, ST, isLen(IS)), slStop(HI, ST, isLen(IS)), slStep(ST)))

  // ==== slice.indices: step / start / stop / clamp ==========================
  syntax Int ::= slStep(OptInt) [function, total]
  rule slStep(noB)          => 1
  rule slStep(someB(S:Int)) => S

  syntax Int ::= slStart(OptInt, OptInt, Int) [function]
  rule slStart(noB,          ST:OptInt, _LEN:Int) => 0
       requires slStep(ST) >Int 0
  rule slStart(noB,          ST:OptInt, LEN:Int)  => LEN -Int 1
       requires slStep(ST) <Int 0
  rule slStart(someB(I:Int), ST:OptInt, LEN:Int)  => slAdjust(I, LEN, slStep(ST))

  syntax Int ::= slStop(OptInt, OptInt, Int) [function]
  rule slStop(noB,          ST:OptInt, LEN:Int)  => LEN
       requires slStep(ST) >Int 0
  rule slStop(noB,          ST:OptInt, _LEN:Int) => -1
       requires slStep(ST) <Int 0
  rule slStop(someB(I:Int), ST:OptInt, LEN:Int)  => slAdjust(I, LEN, slStep(ST))

  syntax Int ::= slAdjust(Int, Int, Int) [function, total]
  rule slAdjust(I:Int, LEN:Int, STEP:Int) => clampLo(I +Int LEN, STEP)
       requires I  <Int 0
  rule slAdjust(I:Int, LEN:Int, STEP:Int) => clampHi(I, LEN, STEP)
       requires I >=Int 0

  syntax Int ::= clampLo(Int, Int) [function, total]
  rule clampLo(J:Int, _STEP:Int) => J
       requires J >=Int 0
  rule clampLo(J:Int, STEP:Int)  => #if STEP <Int 0 #then -1 #else 0 #fi
       requires J <Int 0

  syntax Int ::= clampHi(Int, Int, Int) [function, total]
  rule clampHi(I:Int, LEN:Int, _STEP:Int) => I
       requires I  <Int LEN
  rule clampHi(I:Int, LEN:Int, STEP:Int)  => #if STEP <Int 0 #then LEN -Int 1 #else LEN #fi
       requires I >=Int LEN

  // ==== build the strided sub-sequence (indices in range by construction) ====
  syntax ValSeq ::= buildVS(ValSeq, Int, Int, Int) [function]
  rule buildVS(VS:ValSeq, I:Int, STOP:Int, STEP:Int)
    => vCons(valSeqAt(VS, I), buildVS(VS, I +Int STEP, STOP, STEP))
       requires (STEP >Int 0 andBool I <Int STOP) orBool (STEP <Int 0 andBool I >Int STOP)
  rule buildVS(_:ValSeq, I:Int, STOP:Int, STEP:Int) => .ValSeq
       requires notBool ((STEP >Int 0 andBool I <Int STOP) orBool (STEP <Int 0 andBool I >Int STOP))

  syntax IntSeq ::= buildIS(IntSeq, Int, Int, Int) [function]
  rule buildIS(IS:IntSeq, I:Int, STOP:Int, STEP:Int)
    => iCons(intSeqAt(IS, I), buildIS(IS, I +Int STEP, STOP, STEP))
       requires (STEP >Int 0 andBool I <Int STOP) orBool (STEP <Int 0 andBool I >Int STOP)
  rule buildIS(_:IntSeq, I:Int, STOP:Int, STEP:Int) => .IntSeq
       requires notBool ((STEP >Int 0 andBool I <Int STOP) orBool (STEP <Int 0 andBool I >Int STOP))
endmodule
