// reference/src/lemmas/casts.k — CASTS-LEMMAS
// The total casts (RV .../ceils.k idiom): projectIntTotal/projectBoolTotal as [total] twins of
// the partial {_}:>Int / {_}:>Bool, with #Ceil characterization and orientation at the boundary.

requires "../semantics.k"

module CASTS-LEMMAS
  imports MPY

  // ==== the total Int cast ==================================================
  syntax Bool ::= definedProjectInt(KItem) [function, total]
  rule definedProjectInt(K:KItem) => isInt(K)

  syntax Int ::= projectIntTotal(KItem)
    [function, total, symbol(projectIntTotal), no-evaluators]

  rule #Ceil({@Arg0:KItem}:>Int) => ({ definedProjectInt(@Arg0) #Equals true } #And #Ceil(@Arg0))
    [simplification]

  rule projectIntTotal(Arg0:KItem) => {Arg0}:>Int
    requires definedProjectInt(Arg0)
    [concrete, simplification(10), preserves-definedness]

  rule {Arg0:KItem}:>Int => projectIntTotal(Arg0)
    requires definedProjectInt(Arg0)
    [symbolic(Arg0), simplification, preserves-definedness]

  // round-trip: an int-valued Val IS the injection of its own projection
  rule { V:Val #Equals projectIntTotal(V) } => #Top requires isInt(V) [simplification]
  rule { projectIntTotal(V) #Equals V:Val } => #Top requires isInt(V) [simplification]

  // sort-based collapse: the [concrete] rule above never fires on a SYMBOLIC Int-sorted term
  rule projectIntTotal(I:Int) => I [simplification]
  // idempotence with an FN-HEADED pattern: the sort-based collapse's subsort
  // cast (I:Int) does not capture fn terms, so a re-projection of an already
  // projected operand (the shared compare echoes over locally pre-projected
  // atoms — P90 class) needs this spelling to collapse
  rule projectIntTotal(projectIntTotal(K:KItem)) => projectIntTotal(K) [simplification]

  // ==== the total Bool cast =================================================
  syntax Bool ::= definedProjectBool(KItem) [function, total]
  rule definedProjectBool(K:KItem) => isBool(K)

  syntax Bool ::= projectBoolTotal(KItem)
    [function, total, symbol(projectBoolTotal), no-evaluators]

  rule #Ceil({@Arg0:KItem}:>Bool) => ({ definedProjectBool(@Arg0) #Equals true } #And #Ceil(@Arg0))
    [simplification]

  rule projectBoolTotal(Arg0:KItem) => {Arg0}:>Bool
    requires definedProjectBool(Arg0)
    [concrete, simplification(10), preserves-definedness]

  rule {Arg0:KItem}:>Bool => projectBoolTotal(Arg0)
    requires definedProjectBool(Arg0)
    [symbolic(Arg0), simplification, preserves-definedness]
endmodule
