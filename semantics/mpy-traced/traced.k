// semantics/mpy-traced/traced.k — MPY-TRACED: the vendor MPY semantics + trace overlay.
//
// Mirrors vendor/klever/src/semantics.k with exactly three requires swapped to
// patched/ copies (core.k: +<trace> cell in the configuration; call.k: +callEvt
// on user-function frame push; functions.k: +retEvt on #pop) plus trace.k
// (LineMark statement + lineEvt rule). `make vendor-diff` shows every delta.
//
//   kompile semantics/mpy-traced/traced.k --backend llvm \
//     --main-module MPY-TRACED --syntax-module MPY-TRACED-SYNTAX \
//     --output-definition build/traced

requires "../../vendor/klever/src/semantics/syntax.k"
requires "patched/core.k"
requires "../../vendor/klever/src/semantics/iter.k"
requires "../../vendor/klever/src/semantics/range.k"
requires "../../vendor/klever/src/semantics/operators.k"
requires "../../vendor/klever/src/semantics/int.k"
requires "../../vendor/klever/src/semantics/bool.k"
requires "../../vendor/klever/src/semantics/float.k"
requires "../../vendor/klever/src/semantics/str.k"
requires "../../vendor/klever/src/semantics/set.k"
requires "../../vendor/klever/src/semantics/list.k"
requires "../../vendor/klever/src/semantics/tuple.k"
requires "../../vendor/klever/src/semantics/subscript.k"
requires "../../vendor/klever/src/semantics/comprehension.k"
requires "../../vendor/klever/src/semantics/methods.k"
requires "../../vendor/klever/src/semantics/controls.k"
requires "patched/functions.k"
requires "../../vendor/klever/src/semantics/builtins.k"
requires "patched/call.k"
requires "../../vendor/klever/src/semantics/sort.k"
requires "../../vendor/klever/src/semantics/assert.k"
requires "../../vendor/klever/src/semantics/dict.k"
requires "../../vendor/klever/src/semantics/concrete.k"
requires "trace.k"

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

module MPY-KRUN
  imports MPY
  imports MPY-CONCRETE
endmodule

module MPY-TRACED
  imports MPY-KRUN
  imports MPY-TRACE
endmodule

// Symbolic-tracing main module: the trace overlay WITHOUT MPY-CONCRETE —
// concrete.k's k-cell rules over value constructors narrow abstract Vals on
// the haskell backend (see concrete.k's header comment). Used by the
// B-family (symbolic execution with line-tagged symbolic locals).
module MPY-TRACED-SYM
  imports MPY
  imports MPY-TRACE
endmodule
