// reference/src/lemmas/subscript.k — SUBSCRIPT-LEMMAS
// Element bridges over valSeqAt (semantics/subscript.k): an indexed element of an all-int
// list casts to Int one side at a time, so applyBin/applyCmp reduce. isInt(valSeqAt(..)) is
// never syntactically known — the allInt domain premise carries it instead.

requires "../semantics.k"
requires "casts.k"
requires "preconds.k"

module SUBSCRIPT-LEMMAS
  imports MPY
  imports CASTS-LEMMAS
  imports PRECONDS-LEMMAS

  rule applyBin(OP:String, valSeqAt(VS:ValSeq, I:Int), W:Val)
    => applyBin(OP, projectIntTotal(valSeqAt(VS, I)), W)
    requires allInt(VS)
    [simplification]
  rule applyBin(OP:String, V:Val, valSeqAt(VS:ValSeq, J:Int))
    => applyBin(OP, V, projectIntTotal(valSeqAt(VS, J)))
    requires allInt(VS)
    [simplification]

  rule applyCmp(OP:String, valSeqAt(VS:ValSeq, I:Int), W:Val)
    => applyCmp(OP, projectIntTotal(valSeqAt(VS, I)), W)
    requires allInt(VS)
    [simplification]
  rule applyCmp(OP:String, V:Val, valSeqAt(VS:ValSeq, J:Int))
    => applyCmp(OP, V, projectIntTotal(valSeqAt(VS, J)))
    requires allInt(VS)
    [simplification]

  // ==== slice-bound clamps on symbolic lengths ===============================
  // clampHi's defining rules split strictly at LEN (undecidable when the PC
  // only bounds I <= LEN); for a positive step both sides agree at I == LEN,
  // so the non-strict form decides
  rule clampHi(I:Int, LEN:Int, STEP:Int) => I
    requires I <=Int LEN andBool STEP >Int 0 [simplification]

  // ==== forward lo:hi slice ==================================================
  // an in-bounds step-1 buildIS walk is take-after-drop; takeIS/dropIS stay
  // opaque on symbolic bounds, so window-equality atoms remain #branch-liftable
  // where the partial buildIS blocks lifting
  syntax IntSeq ::= takeIS(IntSeq, Int) [function, total]
  rule takeIS(_:IntSeq, B:Int) => .IntSeq requires B <=Int 0 [simplification]
  rule takeIS(.IntSeq, B:Int) => .IntSeq requires B >Int 0 [simplification]
  rule takeIS(iCons(C:Int, CS:IntSeq), B:Int) => iCons(C, takeIS(CS, B -Int 1))
    requires B >Int 0 [simplification]
  rule buildIS(IS:IntSeq, B:Int, E:Int, 1) => takeIS(dropIS(IS, B), E -Int B)
    requires 0 <=Int B andBool E <=Int isLen(IS) [simplification]

  // suffix [B:] and prefix [:B] with an UNDECIDED clamp (no length bound in
  // the path condition): python's clamping agrees with drop/take on both
  // sides of the length, so the identities hold for every B >= 0
  rule buildIS(IS:IntSeq, clampHi(B:Int, isLen(IS), 1), isLen(IS), 1) => dropIS(IS, B)
    requires 0 <=Int B [simplification]
  rule buildIS(IS:IntSeq, 0, clampHi(B:Int, isLen(IS), 1), 1) => takeIS(IS, B)
    requires 0 <=Int B [simplification]
  // drop's length, when in range; take of the whole length is identity
  rule isLen(dropIS(IS:IntSeq, B:Int)) => isLen(IS) -Int B
    requires 0 <=Int B andBool B <=Int isLen(IS) [simplification]
  rule takeIS(IS:IntSeq, isLen(IS)) => IS [simplification]

  // ==== the total code accessor ==============================================
  // intSeqAt is partial, so its #Ceil sticks implications whenever an element
  // atom lands in a claim's constraint; atI is the total twin, and the bridge
  // rewrites in-range occurrences
  syntax Int ::= atI(IntSeq, Int) [function, total]
  rule atI(.IntSeq, _:Int) => 0 [simplification]
  rule atI(iCons(C:Int, _:IntSeq), I:Int) => C requires I <=Int 0 [simplification]
  rule atI(iCons(_:Int, CS:IntSeq), I:Int) => atI(CS, I -Int 1) requires I >Int 0 [simplification]
  rule intSeqAt(CS:IntSeq, I:Int) => atI(CS, I)
    requires 0 <=Int I andBool I <Int isLen(CS) [simplification]

  // ==== whole-reverse slice ==================================================
  // [::-1] over a str lands on buildIS walking isLen-1 .. 0 by -1 — exactly
  // reversal; revIS is total, so the reshaped atom is #branch-liftable where
  // the partial buildIS blocks lifting (both -Int spellings of the start)
  rule buildIS(IS:IntSeq, isLen(IS) -Int 1, -1, -1) => revIS(IS) [simplification]
  rule buildIS(IS:IntSeq, isLen(IS) +Int -1, -1, -1) => revIS(IS) [simplification]

  // ==== sort-disjointness killers (generic) ==================================
  // an element KNOWN float/int/str (a PC sort atom) is never a heap
  // reference; the deref layer's narrowing branches carry {V #Equals ref(H)}
  // conjuncts that Z3 cannot refute (sort predicates abstract) — kill them
  // at the ML level (probed on Q4's abstract comp element)
  rule { V:Val #Equals ref(_:Int) } => #Bottom requires isFloat(V) [simplification]
  rule { ref(_:Int) #Equals V:Val } => #Bottom requires isFloat(V) [simplification]
  rule { V:Val #Equals cellRef(_:Int) } => #Bottom requires isFloat(V) [simplification]
  rule { cellRef(_:Int) #Equals V:Val } => #Bottom requires isFloat(V) [simplification]
  rule { V:Val #Equals ref(_:Int) } => #Bottom requires isInt(V) [simplification]
  rule { ref(_:Int) #Equals V:Val } => #Bottom requires isInt(V) [simplification]
  rule { V:Val #Equals cellRef(_:Int) } => #Bottom requires isInt(V) [simplification]
  rule { cellRef(_:Int) #Equals V:Val } => #Bottom requires isInt(V) [simplification]
  rule { V:Val #Equals ref(_:Int) } => #Bottom requires isStr(V) [simplification]
  rule { ref(_:Int) #Equals V:Val } => #Bottom requires isStr(V) [simplification]
  rule { V:Val #Equals cellRef(_:Int) } => #Bottom requires isStr(V) [simplification]
  rule { cellRef(_:Int) #Equals V:Val } => #Bottom requires isStr(V) [simplification]

  // ==== ref-disjointness (heap deref narrowing killers) ======================
  // The k-cell deref layer (operators.k etc.) matches ref(H) at operand
  // positions; the prover NARROWS an opaque element term into that constructor
  // and the junk branch must be refuted (probed on 26-remove-duplicates: the
  // inner compare branched per iteration and timed out). Under allInt the
  // element is an Int (the OOB completion of valSeqAt is CHOSEN non-ref —
  // consistent, per the declare-then-guard idiom).
  rule { ref(_:Int) #Equals valSeqAt(VS:ValSeq, _:Int) } => #Bottom
    requires allInt(VS)
    [simplification]
  rule { valSeqAt(VS:ValSeq, _:Int) #Equals ref(_:Int) } => #Bottom
    requires allInt(VS)
    [simplification]
  // same for the list constructor (BinOp("+", list, list) is a k-cell rule now)
  rule { list(_:ValSeq) #Equals valSeqAt(VS:ValSeq, _:Int) } => #Bottom
    requires allInt(VS)
    [simplification]
  rule { valSeqAt(VS:ValSeq, _:Int) #Equals list(_:ValSeq) } => #Bottom
    requires allInt(VS)
    [simplification]
endmodule
