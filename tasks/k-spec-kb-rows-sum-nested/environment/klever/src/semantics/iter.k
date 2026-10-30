// reference/src/semantics/iter.k — MPY-ITER
// The iterator protocol, DECLARATION ONLY. Each iterable's #iterNext case lives in that
// iterable's own module (list/tuple/str in their modules, rangeObj in range.k, zip in
// builtins.k). Consumers (the for-loop, `x in _`, sum/all/any/max/min) import this.

module MPY-ITER
  imports MPY-CORE
  syntax KItem ::= #iterNext(Iterable) | "#iterDone" | #iterYield(Val, Iterable)
endmodule
