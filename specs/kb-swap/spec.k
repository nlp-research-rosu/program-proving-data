requires "verification.k"

module KB-SWAP-SPEC
  imports KB-SWAP-VERIFICATION

  // ---- Entry claim: swap a and b via temporary r; afterwards a = B, b = A, r = A ----
  // KleverBench problems/imp/swap: `r = a ; a = b ; b = r ;`
  claim
    <k>
      Assign(Name("a"), A:Int)
      Assign(Name("b"), B:Int)
      Assign(Name("r"), Name("a"))
      Assign(Name("a"), Name("b"))
      Assign(Name("b"), Name("r"))
    => .K ... </k>
    <env> 0 </env>
    <scopes>
      -1 |-> builtinsScope
      0 |-> scope(.Map, parent(-1))
    =>
      -1 |-> builtinsScope
      0 |-> scope(.Map [ "a" <- B ] [ "b" <- A ] [ "r" <- A ], parent(-1))
    </scopes>
    <scopeLoc> 1 </scopeLoc>
    <stack> .List </stack>
    <ret> noRet </ret>
    <exc> NoExc </exc>
    <exit-code> 0 </exit-code>
    [all-path]
endmodule
