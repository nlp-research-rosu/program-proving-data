requires "verification.k"

module KB-ARITH-MIX-SPEC
  imports KB-ARITH-MIX-VERIFICATION

  // ---- Entry claim: res ends as a*b + a - b, a and b unchanged, for all ints a, b ----
  // KleverBench problems/imp/arith-mix: `res = a * b + a - b ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(
        Name("res"),
        BinOp(
          "-",
          BinOp("+", BinOp("*", Name("a"), Name("b")), Name("a")),
          Name("b")))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- A ] [ "b" <- B ] [ "res" <- ?R:Int ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    ensures ?R ==Int (A *Int B) +Int A -Int B
    [all-path]
endmodule
