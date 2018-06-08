module LEAN-SYNTAX
  imports DOMAINS-SYNTAX

  syntax NIdx ::= Int
  syntax UIdx ::= Int

  syntax NDef ::= NIdx "#NS" NIdx Id
                | NIdx "#NI" NIdx Int

  syntax UDef ::= UIdx "#US"  UIdx
                | UIdx "#UM"  UIdx UIdx
                | UIdx "#UIM" UIdx UIdx
                | UIdx "#UP"  NIdx

  syntax Instrs ::= NDef | UDef
                  | Instrs Instrs  [right]
endmodule

module LEAN
  imports LEAN-SYNTAX
  imports DOMAINS

  rule Is1:Instrs Is2:Instrs => Is1 ~> Is2  [structural]

  //syntax KResult ::= Int | Bool

  configuration <T>
                  <k color="green"> $PGM:Instrs </k>
                  <names color="orange"> 0 |-> *empty* </names>
                  <universes color="cyan"> 0 |-> 0 </universes>
                  <exit-code exit="true"> 0 </exit-code>
                </T>

  /*** Hierarchical names ***/

  syntax HName ::= "*empty*" | Id | HName Id

  rule *empty* Name => Name  [structural, anywhere]

  rule Tgt #NI Src X => Tgt #NS Src String2Id(Int2String(X))  [structural]

  rule <k> Tgt #NS Src Name => . ...</k>
       <names> Names (Src |-> SrcHName) (. => Tgt |-> SrcHName Name) </names>
    requires notBool(Tgt in_keys(Names) orBool Tgt ==K Src)

  /*** Universe terms ***/

  syntax Universe ::= Named(HName) | Int | Succ(Universe)
                    | Max(Universe, Universe) | IMax(Universe, Universe)

  rule Succ(U::Int) => U +Int 1                           [structural, anywhere]
  rule Max(U1::Int, U2::Int) => maxInt(U1, U2)            [structural, anywhere]
  rule IMax(_, 0) => 0                                    [structural, anywhere]
  rule IMax(U1, U2::Int) => Max(U1, U2) when U2 =/=Int 0  [structural, anywhere]

  rule <k> Tgt #UP Src:NIdx => . ...</k>
       <names>... Src |-> SrcHName ...</names>
       <universes> Universes (. => Tgt |-> Named(SrcHName)) </universes>
    requires notBool(Tgt in_keys(Universes))

  rule <k> Tgt #US Src => . ...</k>
       <universes> Universes (Src |-> SrcU) (. => Tgt |-> Succ(SrcU)) </universes>
    requires notBool(Tgt in_keys(Universes) orBool Tgt ==K Src)

  rule <k> Tgt #UM Src1 Src2 => . ...</k>
       <universes> Universes (Src1 |-> Src1U) (Src2 |-> Src2U)
                   (. => Tgt |-> Max(Src1U, Src2U)) </universes>
    requires notBool(Tgt in_keys(Universes) orBool Tgt ==K Src1 orBool Tgt ==K Src2)

  rule <k> Tgt #UIM Src1 Src2 => . ...</k>
       <universes> Universes (Src1 |-> Src1U) (Src2 |-> Src2U)
                 (. => Tgt |-> IMax(Src1U, Src2U)) </universes>
    requires notBool(Tgt in_keys(Universes) orBool Tgt ==K Src1 orBool Tgt ==K Src2)

endmodule
