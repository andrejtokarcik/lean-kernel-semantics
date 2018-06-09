module LEAN-KERNEL-SYNTAX
  imports DOMAINS-SYNTAX

  syntax NIdx  ::= Int
  syntax UIdx  ::= Int
  syntax UIdxs ::= List{UIdx," "}
  syntax EIdx  ::= Int

  syntax NDef ::= NIdx "#NS" NIdx Id
                | NIdx "#NI" NIdx Int

  syntax UDef ::= UIdx "#US"  UIdx
                | UIdx "#UM"  UIdx UIdx
                | UIdx "#UIM" UIdx UIdx
                | UIdx "#UP"  NIdx

  syntax EInfo ::= "#BD" | "#BI" | "#BS" | "#BC"
  syntax EDef ::= EIdx "#EV" Int
                | EIdx "#ES" UIdx
                | EIdx "#EC" NIdx UIdxs
                | EIdx "#EA" EIdx EIdx
                | EIdx "#EL" EInfo NIdx EIdx EIdx
                | EIdx "#EP" EInfo NIdx EIdx EIdx

  syntax Instrs ::= NDef | UDef | EDef
                  | Instrs Instrs  [right]
endmodule

module LEAN-KERNEL
  imports LEAN-KERNEL-SYNTAX
  imports DOMAINS

  syntax List ::= lookupMulti(Map, Set)  [function]
  rule lookupMulti(M, Keys) => values(removeAll(M, keys(M) -Set Keys))

  syntax Set ::= UIdxs2Set(UIdxs)  [function]
  rule UIdxs2Set(.UIdxs) => .Set
  rule UIdxs2Set(UIdx UIdxs) => SetItem(UIdx) UIdxs2Set(UIdxs)

  rule Is1:Instrs Is2:Instrs => Is1 ~> Is2  [structural]

  //syntax KResult ::= Int | Bool

  configuration <T>
                  <k color="green"> $PGM:Instrs </k>
                  <names color="orange"> 0 |-> *empty* </names>
                  <universes color="cyan"> 0 |-> 0 </universes>
                  <expressions> .Map </expressions>
                  <exit-code exit="true"> 0 </exit-code>
                </T>

  /*** Hierarchical names ***/

  syntax HierName ::= "*empty*" | Id | HierName Id

  rule *empty* Id => Id  [structural, anywhere]

  rule Tgt #NI NIdx X => Tgt #NS NIdx String2Id(Int2String(X))  [structural]

  rule <k> Tgt #NS NIdx Id => . ...</k>
       <names> Names (NIdx |-> N) (. => Tgt |-> N Id) </names>
    requires notBool(Tgt in_keys(Names) orBool Tgt ==K NIdx)

  /*** Universe terms ***/

  syntax Universe ::= Named(HierName) | Int | Succ(Universe)
                    | Max(Universe, Universe) | IMax(Universe, Universe)

  rule Succ(U:Int) => U +Int 1                           [structural, anywhere]
  rule Max(U1:Int, U2:Int) => maxInt(U1, U2)             [structural, anywhere]
  rule IMax(_, 0) => 0                                   [structural, anywhere]
  rule IMax(U1, U2:Int) => Max(U1, U2) when U2 =/=Int 0  [structural, anywhere]

  rule <k> Tgt #UP NIdx => . ...</k>
       <names>... NIdx |-> N ...</names>
       <universes> Us (. => Tgt |-> Named(N)) </universes>
    requires notBool(Tgt in_keys(Us))

  rule <k> Tgt #US UIdx => . ...</k>
       <universes> Us (UIdx |-> U) (. => Tgt |-> Succ(U)) </universes>
    requires notBool(Tgt in_keys(Us) orBool Tgt ==K UIdx)

  rule <k> Tgt #UM UIdx1 UIdx2 => . ...</k>
       <universes> Us (UIdx1 |-> U1) (UIdx2 |-> U2)
                   (. => Tgt |-> Max(U1, U2)) </universes>
    requires notBool(Tgt in_keys(Us) orBool Tgt ==K UIdx1 orBool Tgt ==K UIdx2)

  rule <k> Tgt #UIM UIdx1 UIdx2 => . ...</k>
       <universes> Us (UIdx1 |-> U1) (UIdx2 |-> U2)
                   (. => Tgt |-> IMax(U1, U2)) </universes>
    requires notBool(Tgt in_keys(Us) orBool Tgt ==K UIdx1 orBool Tgt ==K UIdx2)

  /*** Expressions ***/

  syntax Exp ::= Sort(Universe) | DeBruijn(Int) | Const(HierName, List) | App(Exp, Exp)
               | Lambda(EInfo, HierName, Exp, Exp)
               | Pi    (EInfo, HierName, Exp, Exp)

  rule <k> Tgt #ES UIdx => . ...</k>
       <universes>... UIdx |-> U ...</universes>
       <expressions> Exps (. => Tgt |-> Sort(U)) </expressions>
    requires notBool(Tgt in_keys(Exps))

  rule <k> Tgt #EV X => . ...</k>
       <expressions> Exps (. => Tgt |-> DeBruijn(X)) </expressions>
    requires notBool(Tgt in_keys(Exps))

  rule <k> Tgt #EC NIdx UIdxs => . ...</k>
       <names>... NIdx |-> N ...</names>
       <universes> Us </universes>
       <expressions> Exps (. => Tgt |-> Const(N, lookupMulti(Us, UIdxs2Set(UIdxs)))) </expressions>
    requires notBool(Tgt in_keys(Exps))

  rule <k> Tgt #EA FIdx AIdx => . ...</k>
       <expressions> Exps (FIdx |-> F) (AIdx |-> A)
                     (. => Tgt |-> App(F, A)) </expressions>
    requires notBool(Tgt in_keys(Exps) orBool Tgt ==K FIdx orBool Tgt ==K AIdx)

  // pros of expanding the definition components upon storing in config
  // (as opposed to keeping just the indices in the config and looking up / expanding
  // only when needed):
  // - reference to non-existent index reported immediately, not delayed until use
  // - easier to understand the current config
  // - streamlining the typecheck stage: no unnecessary lookups then
  // cons:
  // - duplicating structures / memory waste / performance hit
  // - may needlessly expand what does not get used at all

  rule <k> Tgt #EL Info NIdx TIdx EIdx => . ...</k>
       <names>... NIdx |-> N ...</names>
       <expressions> Exps (TIdx |-> T) (EIdx |-> E)
                     (. => Tgt |-> Lambda(Info, N, T, E)) </expressions>
    requires notBool(Tgt in_keys(Exps) orBool Tgt ==K TIdx orBool Tgt ==K EIdx)

  rule <k> Tgt #EP Info NIdx TIdx EIdx => . ...</k>
       <names>... NIdx |-> N ...</names>
       <expressions> Exps (TIdx |-> T) (EIdx |-> E)
                     (. => Tgt |-> Pi(Info, N, T, E)) </expressions>
    requires notBool(Tgt in_keys(Exps) orBool Tgt ==K TIdx orBool Tgt ==K EIdx)

endmodule
