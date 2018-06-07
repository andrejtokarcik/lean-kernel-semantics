module LEAN-SYNTAX
  imports DOMAINS

  syntax NIdx ::= r"[0-9]+"  [token]

  // FIXME the Id sort is a hack -- String would be preferable
  // but it expects the value to be wrapped in quotation marks
  syntax NDef ::= NIdx "#NS" NIdx Id
                | NIdx "#NI" NIdx Int

  syntax Instrs ::= NDef
                  | Instrs Instrs  [right]
endmodule

module LEAN
  imports LEAN-SYNTAX

  rule I1:Instrs I2:Instrs => I1 ~> I2  [structural]

  //syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Instrs </k>
                  <names color="red"> .Map </names>
                  <exit-code exit="true"> 0 </exit-code>
                </T>

  rule Tgt #NI Src TgtN => Tgt #NS Src String2Id(Int2String(TgtN))

  rule <k> Tgt #NS Src TgtN => . ...</k>
       <names>
         Src |-> SrcN
         Names => Names[Tgt <- SrcN +String "." +String Id2String(TgtN)]
       </names>

  rule <k> Tgt #NS 0 TgtN => . ...</k>
       <names> Names => Names[Tgt <- Id2String(TgtN)] </names>

endmodule
