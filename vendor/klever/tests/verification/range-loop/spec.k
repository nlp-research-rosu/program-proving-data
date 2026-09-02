requires "verification.k"

module RANGE-LOOP-SPEC
  imports RANGE-LOOP-VERIFICATION

  // ---- Loop invariant (circularity), induction on the bound (I climbs to N) ----
  claim
    <k>
      #loop(rangeObj(I:Int, N:Int, 1), Name("i"), AugAssign(Name("total"), "+", Name("i")))
    => .K ... </k>
    <scopes>
      ... L |-> (
        scope(.Map [ "n" <- NV:Val ] [ "total" <- B:Int ] [ "i" <- _:Val ], P:Parent) =>
        scope(.Map [ "n" <- NV ] [ "total" <- ?T:Int ] [ "i" <- ?_:Val ], P)
      ) ...
    </scopes>
    <env> L:Int </env>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires 0 <=Int I andBool I <=Int N
    ensures ?T ==Int B +Int ((N *Int (N -Int 1)) -Int (I *Int (I -Int 1))) /Int 2
    [all-path]

  // ---- Entry claim — result = f(N) == N*(N-1)/2. ----
  claim
    <k>
      FuncDef("f", Params("n"),
        Assign(Name("total"), Int(0))
        Assign(Name("i"), Int(0))
        For(Name("i"), Call(Name("range"), Name("n")),
          AugAssign(Name("total"), "+", Name("i")))
        Return(Name("total")))
      Assign(Name("result"), Call(Name("f"), N:Int))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "f" <- ?_:Val ] [ "result" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    requires N >=Int 0
    ensures ?R ==Int (N *Int (N -Int 1)) /Int 2
    [all-path]
endmodule
