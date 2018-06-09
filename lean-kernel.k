module LEAN-KERNEL-SYNTAX
  imports DOMAINS-SYNTAX

  syntax NIdx  ::= Int
  syntax NIdxs ::= List{NIdx," "}
  syntax UIdx  ::= Int
  syntax UIdxs ::= List{UIdx," "}
  syntax EIdx  ::= Int

  syntax NCmd ::= NIdx "#NS" NIdx Id
                | NIdx "#NI" NIdx Int

  syntax UCmd ::= UIdx "#US"  UIdx
                | UIdx "#UM"  UIdx UIdx
                | UIdx "#UIM" UIdx UIdx
                | UIdx "#UP"  NIdx

  syntax EInfo ::= "#BD" | "#BI" | "#BS" | "#BC"
  syntax ECmd ::= EIdx "#EV" Int
                | EIdx "#ES" UIdx
                | EIdx "#EC" NIdx UIdxs
                | EIdx "#EA" EIdx EIdx
                | EIdx "#EL" EInfo NIdx EIdx EIdx
                | EIdx "#EP" EInfo NIdx EIdx EIdx

  syntax DefCmd ::= "#DEF" NIdx EIdx EIdx NIdxs
                  | "#AX"  NIdx EIdx      NIdxs

  syntax Cmds ::= NCmd | UCmd | ECmd | DefCmd
                | Cmds Cmds  [right]
endmodule

module LEAN-KERNEL
  imports LEAN-KERNEL-SYNTAX
  imports DOMAINS

  syntax List ::= lookupMulti(Map, Set)  [function]
  rule lookupMulti(M, Keys) => values(removeAll(M, keys(M) -Set Keys))

  syntax Set ::= NIdxs2Set(NIdxs)  [function]
  rule NIdxs2Set(.NIdxs) => .Set
  rule NIdxs2Set(NIdx NIdxs) => SetItem(NIdx) NIdxs2Set(NIdxs)

  syntax Set ::= UIdxs2Set(UIdxs)  [function]
  rule UIdxs2Set(.UIdxs) => .Set
  rule UIdxs2Set(UIdx UIdxs) => SetItem(UIdx) UIdxs2Set(UIdxs)

  rule Is1:Cmds Is2:Cmds => Is1 ~> Is2  [structural]

  //syntax KResult ::= Int | Bool

  configuration <T>
                  <k color="green"> $PGM:Cmds </k>
                  <names color="orange"> 0 |-> *empty* </names>
                  <universes color="cyan"> 0 |-> 0 </universes>
                  <expressions> .Map </expressions>
                  <def-types> .Map </def-types>
                  <def-values> .Map </def-values>
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

  /*** Exprressions ***/

  syntax Expr ::= Sort(Universe)
                | "#" Int  [klabel(DeBruijn)]
                | Const(HierName, List)
                | App(Expr, Expr)
                | Lambda(EInfo, HierName, Expr, Expr)
                | Pi    (EInfo, HierName, Expr, Expr)

  rule <k> Tgt #ES UIdx => . ...</k>
       <universes>... UIdx |-> U ...</universes>
       <expressions> Exprs (. => Tgt |-> Sort(U)) </expressions>
    requires notBool(Tgt in_keys(Exprs))

  rule <k> Tgt #EV X => . ...</k>
       <expressions> Exprs (. => Tgt |-> # X) </expressions>
    requires notBool(Tgt in_keys(Exprs))

  rule <k> Tgt #EC NIdx UIdxs => . ...</k>
       <names>... NIdx |-> N ...</names>
       <universes> Us </universes>
       <expressions> Exprs (. => Tgt |-> Const(N, lookupMulti(Us, UIdxs2Set(UIdxs)))) </expressions>
    requires notBool(Tgt in_keys(Exprs))

  rule <k> Tgt #EA FIdx AIdx => . ...</k>
       <expressions> Exprs (FIdx |-> F) (AIdx |-> A)
                     (. => Tgt |-> App(F, A)) </expressions>
    requires notBool(Tgt in_keys(Exprs) orBool Tgt ==K FIdx orBool Tgt ==K AIdx)

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
       <expressions> Exprs (TIdx |-> T) (EIdx |-> E)
                     (. => Tgt |-> Lambda(Info, N, T, E)) </expressions>
    requires notBool(Tgt in_keys(Exprs) orBool Tgt ==K TIdx orBool Tgt ==K EIdx)

  rule <k> Tgt #EP Info NIdx TIdx EIdx => . ...</k>
       <names>... NIdx |-> N ...</names>
       <expressions> Exprs (TIdx |-> T) (EIdx |-> E)
                     (. => Tgt |-> Pi(Info, N, T, E)) </expressions>
    requires notBool(Tgt in_keys(Exprs) orBool Tgt ==K TIdx orBool Tgt ==K EIdx)

  /*** Definitions and Axioms ***/

  syntax DefObj ::= Expr | UPolymorphic(Expr, List)

  rule UPolymorphic(E, .List) => E  [structural, anywhere]

  rule <k> #DEF NIdx TIdx EIdx NIdxs => . ...</k>
       <names> Names (NIdx |-> N) </names>
       <expressions>... (TIdx |-> T) (EIdx |-> E) ...</expressions>
       <def-types> DefTypes (. => N |-> UPolymorphic(T, lookupMulti(Names, NIdxs2Set(NIdxs)))) </def-types>
       <def-values> DefVals (. => N |-> E) </def-values>
    requires notBool(N in_keys(DefTypes)) andBool notBool(N in_keys(DefVals))

  rule <k> #AX NIdx TIdx NIdxs => . ...</k>
       <names> Names (NIdx |-> N) </names>
       <expressions>... TIdx |-> T ...</expressions>
       <def-types> DefTypes (. => N |-> UPolymorphic(T, lookupMulti(Names, NIdxs2Set(NIdxs)))) </def-types>
    requires notBool(N in_keys(DefTypes))

endmodule
