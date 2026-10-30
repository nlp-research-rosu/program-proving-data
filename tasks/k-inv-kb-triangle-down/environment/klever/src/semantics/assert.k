// reference/src/semantics/assert.k — MPY-ASSERT

module MPY-ASSERT
  imports MPY-CORE

  rule <k> Assert(V:Val) => .K ... </k>
       requires truthy(V)
  rule <k> Assert(V:Val) ~> _ => .K </k>
       <exc> NoExc => AssertionError </exc>
       <exit-code> _ => 1 </exit-code>
       requires notBool truthy(V)

  rule <k> Assert(ref(H:Int)) => Assert(V) ... </k>
       <heap> ... H |-> V:Val ... </heap>
       [priority(40)]
endmodule
