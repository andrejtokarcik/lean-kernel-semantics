module LEAN-SYNTAX
  imports DOMAINS-SYNTAX

  syntax NIdx ::= Int
  syntax UIdx ::= Int

  syntax NDef ::= NIdx "#NS" NIdx Id
                | NIdx "#NI" NIdx Int

  syntax Instrs ::= NDef
                  | Instrs Instrs  [right]
endmodule

module LEAN
  imports LEAN-SYNTAX
  imports DOMAINS

  rule Is1:Instrs Is2:Instrs => Is1 ~> Is2  [structural]

  //syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Instrs </k>
                  <names color="red"> .Map </names>
                  <exit-code exit="true"> 0 </exit-code>
                </T>

  syntax HName ::= Id | HName Id

  rule Tgt #NI Src X => Tgt #NS Src String2Id(Int2String(X))

  rule <k> Tgt #NS 0 Name => . ...</k>
     <names> Names => Names[Tgt <- Name] </names>

  rule <k> Tgt #NS Src Name => . ...</k>
       <names>
         (Src |-> SrcHName)
         (Names => Names[Tgt <- SrcHName Name])
       </names>
    when Tgt =/=K Src

  rule <k> Tgt #NS Src Name => . ...</k>
       <names>... Src |-> (SrcHName => SrcHName Name) ...</names>
    when Tgt ==K Src

endmodule
