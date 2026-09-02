// reference/src/lemmas/float.k — FLOAT-LEMMAS
// Float twins of the Int bridge infra: the total Float projection and the List[float]
// domain predicate. Float ops themselves stay opaque (semantics/float.k) — kprove has no
// float hooks; proofs verify structure only.

requires "../semantics.k"

module FLOAT-LEMMAS
  imports MPY

  syntax Float ::= projectFloatTotal(Val) [function, total, symbol(projectFloatTotal), no-evaluators]
  rule projectFloatTotal(F:Float) => F [simplification]

  syntax Bool ::= allFloat(ValSeq) [function, total]
  rule allFloat(.ValSeq)                => true
  rule allFloat(vCons(V:Val, R:ValSeq)) => isFloat(V) andBool allFloat(R)

  // K's minFloat/maxFloat are unrecognized hooks in the haskell backend —
  // kore CRASHES (missing hook) if evaluation ever touches them, and the
  // documented workaround is to give the symbols rules; expressed via the
  // shared opaque compares
  rule minFloat(A:Float, B:Float) => #if floatLt(A, B) #then A #else B #fi [simplification]
  rule maxFloat(A:Float, B:Float) => #if gtF(A, B) #then A #else B #fi [simplification]

  // Float compares reduce to the shared opaque atoms AT THE K-CELL: the
  // applyCmp function route never receives simplification rewriting on
  // function-term operands (k-cell rules unify where function matching
  // refuses), and eqF/gtF are the semantics' own symbolic equality/order.
  // (dispatch happens via the cooling echo in lemmas/core.k; sort-typed
  // k-cell Compare patterns coerce Val operands — probed on P26.) Val-sorted
  // variable patterns + structural isFloat guards fire on Float-injected
  // fn-term operands.
  rule applyCmp("==", V:Val, W:Val) => eqF(projectFloatTotal(V), projectFloatTotal(W))
    requires isFloat(V) andBool isFloat(W) [simplification]
  rule applyCmp(">", V:Val, W:Val) => gtF(projectFloatTotal(V), projectFloatTotal(W))
    requires isFloat(V) andBool isFloat(W) [simplification]
  rule applyCmp("<", V:Val, W:Val) => floatLt(projectFloatTotal(V), projectFloatTotal(W))
    requires isFloat(V) andBool isFloat(W) [simplification]
  // the mixed Float/Int spellings echo the shared applyCmp promotions
  rule applyCmp("==", V:Val, W:Val) => eqF(projectFloatTotal(V), intToF({W}:>Int))
    requires isFloat(V) andBool isInt(W) [simplification]
  rule applyCmp(">", V:Val, W:Val) => gtF(projectFloatTotal(V), intToF({W}:>Int))
    requires isFloat(V) andBool isInt(W) [simplification]
  rule applyCmp("<", V:Val, W:Val) => floatLt(projectFloatTotal(V), intToF({W}:>Int))
    requires isFloat(V) andBool isInt(W) [simplification]

  // ==Float is a missing hook in kprove (the plain applyCmp Float rule forms
  // it on concrete operands); eqF is the semantics' own equality — its
  // [concrete] rule is the inverse of this equation
  rule F1:Float ==Float F2:Float => eqF(F1, F2) [simplification]

  // the zero promotion as a literal (the Int2Float hook is missing in kprove)
  rule intToF(0) => 0.0 [simplification]
  rule Int2Float(0, 53, 11) => 0.0 [simplification]
  // unary minus forms 0.0 -Float F (applyUn), and the -Float hook is missing
  // in kprove — give the literal instance a rule (the kore workaround)
  rule 0.0 -Float 1.0 => -1.0 [simplification]

  // dispatch echoes of the shared float builtins: plain dispatch refuses
  // function-headed args under the injections; these simplification twins
  // are the same equations and unify
  rule applyBuiltin("round", F:Float, .Vals) => roundF(F)  [simplification]
  rule applyBuiltin("floor", V:Val, .Vals)   => floorFI(V) [simplification]
  rule applyBuiltin("ceil",  V:Val, .Vals)   => ceilF(V)   [simplification]
  rule applyBuiltin("int",   F:Float, .Vals) => truncF(F)  [simplification]
endmodule
