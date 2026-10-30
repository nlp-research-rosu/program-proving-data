// reference/src/semantics/int.k — MPY-INT
// Int cases of the operator dispatch; Python // and % are floored (pyMod).

module MPY-INT
  imports MPY-CORE

  rule applyUn("-", I:Int) => 0 -Int I

  rule applyBin("+",  I1:Int, I2:Int) => I1 +Int I2
  // Bool participates in int arithmetic (x += (a == b))
  rule applyBin("+",  I:Int, B:Bool) => I +Int #if B #then 1 #else 0 #fi
  rule applyBin("+",  B:Bool, I:Int) => #if B #then 1 #else 0 #fi +Int I
  rule applyBin("-",  I1:Int, I2:Int) => I1 -Int I2
  rule applyBin("*",  I1:Int, I2:Int) => I1 *Int I2
  rule applyBin("%",  I1:Int, I2:Int) => pyMod(I1, I2)
  rule applyBin("//", I1:Int, I2:Int) => (I1 -Int pyMod(I1, I2)) /Int I2
  rule applyBin("**", I1:Int, I2:Int) => I1 ^Int I2 requires I2 >=Int 0

  syntax Int ::= pyMod(Int, Int) [function]
  rule pyMod(I1:Int, I2:Int) => ((I1 %Int I2) +Int I2) %Int I2

  rule applyCmp("<",  I1:Int, I2:Int)   => I1 <Int  I2
  rule applyCmp("<=", I1:Int, I2:Int)   => I1 <=Int I2
  rule applyCmp(">",  I1:Int, I2:Int)   => I1 >Int  I2
  rule applyCmp(">=", I1:Int, I2:Int)   => I1 >=Int I2
  rule applyCmp("==", I1:Int, I2:Int)   => I1 ==Int I2
  rule applyCmp("!=", I1:Int, I2:Int)   => I1 =/=Int I2
endmodule
