// semantics/mpy-traced/trace.k — the CWM-trace overlay (concrete traced builds only).
//
// LineMark(N) statements are interleaved by scripts/py2mpy_traced.py before every
// statement (plus at loop-body ends, mirroring sys.settrace's per-iteration re-log
// of the loop-header line). Each LineMark dissolves into a lineEvt recording
// (line, current-scope map, heap snapshot) BEFORE the marked statement executes —
// exactly CWM's "observation immediately prior to executing the line".
// callEvt/retEvt are appended by the patched frame rules (patched/call.k,
// patched/functions.k). Assertion failures need no event rule: the extractor
// synthesizes the exception event from the final <exc>/<exit-code> cells.
//
// The verification/symbolic pipelines use the UNTOUCHED vendor semantics; this
// module never enters those kompilations.

module MPY-TRACED-SYNTAX
  imports MPY-SYNTAX
  syntax Stmt ::= "LineMark" "(" Int ")"
endmodule

module MPY-TRACE
  imports MPY-TRACED-SYNTAX
  imports MPY-CORE

  syntax TraceEvt ::= lineEvt(Int, Map, Map)   // line, scope map (locals), heap snapshot
                    | callEvt(Vals)            // evaluated args at user-function frame push
                    | retEvt(Val, Map, Map)    // return value, callee scope map, heap snapshot

  rule <k> LineMark(N:Int) => .K ... </k>
       <env> L:Int </env>
       <scopes> ... L |-> scope(M:Map, _) ... </scopes>
       <heap> H:Map </heap>
       <trace> T:List => T ListItem(lineEvt(N, M, H)) </trace>

  // callee-scope projection for retEvt (the #pop rule reads <scopes> before
  // deallocating the callee frame)
  syntax Map ::= scopeMapOf(Map, Int) [function]
  rule scopeMapOf(SC:Map, L:Int) => mapOfScope({SC[L]}:>Scope)
  syntax Map ::= mapOfScope(Scope) [function]
  rule mapOfScope(scope(M:Map, _)) => M
endmodule
