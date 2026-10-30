// reference/src/semantics.k — the CANONICAL `.mpy` semantics, ASSEMBLED.
//
//   kompile verification/humaneval/reference/src/semantics.k --backend llvm \
//     --main-module MPY --syntax-module MPY-SYNTAX \
//     --output-definition verification/humaneval/reference/src/semantics-kompiled
//   bash verification/humaneval/reference/tests/run.sh   # CPython oracle + K per test
//
// Everything krun reaches lives under semantics/ — dispatch, evaluation, and the opaque
// primitives with their [concrete] twins. Proof-only rules live under lemmas/ (see lemmas.k).
//
// Files (dependency order — everything imports MPY-CORE):
//   semantics/syntax.k         MPY-SYNTAX       AST productions
//   semantics/core.k           MPY-CORE         values, config, load, lookup, shared helpers   [required]
//   semantics/iter.k           MPY-ITER         the iterator protocol (#iterNext/#iterYield/#iterDone) decl
//   semantics/range.k          MPY-RANGE        rangeObj: inRange / rangeLen / its #iterNext
//   semantics/operators.k      MPY-OPERATORS    operator DISPATCH (UnaryOp/BinOp/Compare/BoolOp) — domain files own the cases
//   semantics/int.k            MPY-INT          Int operator cases; floored // and % (pyMod)
//   semantics/bool.k           MPY-BOOL         Bool operator cases + truthy not/and/or (BoolOp)
//   semantics/float.k          MPY-FLOAT        Float Val: literal + opaque float ops ([concrete] for krun)
//   semantics/str.k            MPY-STR          str(IntSeq): literal, +, ==, in
//   semantics/set.k            MPY-SET          set(str): distinct char codes (len / membership)
//   semantics/list.k           MPY-LIST         ListExpr, list(ValSeq): +, ==, in
//   semantics/tuple.k          MPY-TUPLE        TupleExpr, tuple ==, target-binding + unpacking
//   semantics/subscript.k      MPY-SUBSCRIPT    Subscript indexing + Slice
//   semantics/comprehension.k  MPY-COMPREHENSION  list comprehensions [ELT for T in ITER if COND]
//   semantics/methods.k        MPY-METHODS      pure str methods: is*/lower/upper/swapcase/startswith
//   semantics/controls.k       MPY-CONTROLS     Assign/AugAssign, If, IfExp, For, While, break/continue
//   semantics/functions.k      MPY-FUNCTIONS    def / call / return (frame stack)
//   semantics/builtins.k       MPY-BUILTINS     builtins as calls: len/sum/abs/min/max/ord/chr/str
//   semantics/call.k           MPY-CALL         ALL Call routing + argument evaluation
//   semantics/sort.k           MPY-SORT         trusted sorted(): opaque sortVS + concrete insertion sort
//   semantics/assert.k         MPY-ASSERT       Assert oracle (smoke programs only)
//   semantics/dict.k           MPY-DICT         order-preserving dictV(KS,VS) + .keys() + list()

requires "semantics/syntax.k"
requires "semantics/core.k"
requires "semantics/iter.k"
requires "semantics/range.k"
requires "semantics/operators.k"
requires "semantics/int.k"
requires "semantics/bool.k"
requires "semantics/float.k"
requires "semantics/str.k"
requires "semantics/set.k"
requires "semantics/list.k"
requires "semantics/tuple.k"
requires "semantics/subscript.k"
requires "semantics/comprehension.k"
requires "semantics/methods.k"
requires "semantics/controls.k"
requires "semantics/functions.k"
requires "semantics/builtins.k"
requires "semantics/call.k"
requires "semantics/sort.k"
requires "semantics/assert.k"
requires "semantics/dict.k"
requires "semantics/concrete.k"

module MPY
  imports MPY-CORE
  imports MPY-ITER
  imports MPY-RANGE
  imports MPY-OPERATORS
  imports MPY-INT
  imports MPY-BOOL
  imports MPY-FLOAT
  imports MPY-STR
  imports MPY-SET
  imports MPY-LIST
  imports MPY-TUPLE
  imports MPY-SUBSCRIPT
  imports MPY-COMPREHENSION
  imports MPY-METHODS
  imports MPY-CONTROLS
  imports MPY-FUNCTIONS
  imports MPY-BUILTINS
  imports MPY-CALL
  imports MPY-SORT
  imports MPY-ASSERT
  imports MPY-DICT
endmodule

// The krun (llvm) main module: MPY plus the concrete-only legs (keyed sort's
// real key calls, deep list equality). Verification builds import MPY and
// never see MPY-CONCRETE. The llvm kompile MUST use --main-module MPY-KRUN —
// with plain MPY the concrete legs are silently absent (this was live for a
// while: sorted-key stuck and comprehension asserted wrong under krun).
module MPY-KRUN
  imports MPY
  imports MPY-CONCRETE
endmodule
