module SMOKE2
  imports INT
  imports BOOL
  syntax State ::= run(Int) | done(Int)
  configuration <k> $PGM:State </k>
  rule run(I) => run(I +Int 1) requires I <Int 10  [label(bump)]
  rule run(I) => done(I)       requires I >=Int 10 [label(finish)]
endmodule
