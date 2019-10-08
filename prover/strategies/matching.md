```k
module STRATEGY-MATCHING
  imports PROVER-CORE
  imports PROVER-HORN-CLAUSE-SYNTAX
  imports PROVER-CONFIGURATION
  imports KORE-HELPERS
  imports MAP

  rule <claim> \implies(\and(LSPATIAL, LHS) , \exists { Vs } \and(RSPATIAL, RHS)) </claim>
       <strategy> match => #match( term: LSPATIAL
                                 , pattern: RSPATIAL
                                 , variables: Vs
                                 )
                        ~> match
                  ...
       </strategy>
    requires isSpatialPattern(LSPATIAL)
     andBool isSpatialPattern(RSPATIAL)

  rule <claim> \implies( \and( LSPATIAL, LHS)
                       ,  \exists { Vs } \and( RHS )
                       => \exists { Vs -Patterns fst(unzip(SUBST)) } substMap(\and(RHS), SUBST)
                       )
       </claim>
       <strategy> ( #matchResult( subst: SUBST
                                , rest:  .Patterns
                                )
                  , .MatchResults
                 ~> match
                  )
               => noop
                  ...
       </strategy>

                                         /* Subst, Rest */
  syntax MatchResult ::= "#matchResult" "(" "subst:" Map "," "rest:" Patterns ")" [format(%1%2%i%n%3%i%n%4%d%n%5%i%6%n%7%d%d%8)]
  syntax MatchResult ::= "#matchFailure" "(" String ")"
  syntax MatchResults ::= List{MatchResult, ","} [klabel(MatchResults), format(%1%n%2 %3)]

  syntax MatchResults ::= "#match" "(" "term:"      Pattern
                                   "," "pattern:"   Pattern
                                   "," "variables:" Patterns
                                   ")" [function]
  syntax Maps ::= "#matchAux" "(" "terms:"     Patterns
                              "," "pattern:"   Pattern
                              "," "variables:" Patterns
                              "," "results:"   Maps
                              "," "subst:"     Map
                              ")" [function]

  syntax Maps ::= List{Map, ";"} [klabel(Maps)]

  syntax Maps ::= "#matchStuck" "(" K ")"

  syntax Maps ::= Maps "++Maps" Maps [function, right]
  rule (MR1; MR1s) ++Maps MR2s => MR1; (MR1s ++Maps MR2s)
  rule .Maps ++Maps MR2s => MR2s

  syntax MatchResults ::= #getMatchResults(Pattern, Pattern, Maps) [function]
  rule #getMatchResults(T, P, .Maps) => .MatchResults
  rule #getMatchResults(S(ARGs), S(P_ARGs), SUBST; SUBSTs)
    => #matchResult(subst: SUBST, rest: .Patterns)
     , #getMatchResults(sep(ARGs), sep(P_ARGs), SUBSTs)
    requires S =/=K sep
  rule #getMatchResults(sep(ARGs), sep(P_ARGs), SUBST; SUBSTs)
    => #matchResult(subst: SUBST, rest: ARGs -Patterns substPatternsMap(P_ARGs, SUBST))
     , #getMatchResults(sep(ARGs), sep(P_ARGs), SUBSTs)

  rule #match( term: T , pattern: P, variables: Vs )
    => #getMatchResults( T, P, #matchAux( terms: T , pattern: P, variables: Vs, results: .Maps, subst: .Map ) )
    requires getFreeVariables(T) intersect Vs ==K .Patterns

  rule #match( term: T, pattern: _, variables: Vs )
    => #matchFailure( "AlphaRenaming not done" )
     , .MatchResults

  rule #matchAux( terms: Ts , pattern: P, variables: Vs, results: MRs, subst: SUBST )
    => #matchStuck( "terms:" ~> Ts ~> "pattern:" ~> P ~> "vars:" ~> Vs ~> "results:" ~> MRs ~> "subst:" ~> SUBST )
    [owise]
    
  rule #matchAux( terms:     S:Symbol(ARGs), .Patterns
                , pattern:   S:Symbol(P_ARGs)
                , variables: Vs
                , results:   .Maps
                , subst:     SUBST
             )
    => (SUBST removeIdentityMappings(zip(P_ARGs, ARGs))); .Maps
    requires S =/=K sep
    andBool checkSubstitution(removeIdentityMappings(zip(P_ARGs, ARGs)), Vs)

  rule #matchAux( terms:     S:Symbol(ARGs), .Patterns
                , pattern:   S:Symbol(P_ARGs)
                , variables: Vs
                , results:   .Maps
                , subst:     _
                )
    => .Maps
    requires S =/=K sep
    andBool notBool(checkSubstitution(removeIdentityMappings(zip(P_ARGs, ARGs)), Vs))

  rule #matchAux( terms:     sep(ARGs), .Patterns
                , pattern:   sep(.Patterns)
                , variables: Vs
                , results:   .Maps
                , subst:     SUBST
                )
    => SUBST; .Maps

  rule #matchAux( terms:     sep(.Patterns), .Patterns
                , pattern:   sep(P, Ps)
                , variables: Vs
                , results:   .Maps
                , subst:     SUBST
                )
    => .Maps

  rule #matchAux( terms:     sep(ARGs), .Patterns
                , pattern:   sep(P_ARG, P_ARGs)
                , variables: Vs
                , results:   .Maps
                , subst:     SUBST
                )
    => #matchAux( terms:     sep(ARGs)
                , pattern:   sep(P_ARGs)
                , variables: Vs
                , results:   #matchAux( terms:     ARGs
                                      , pattern:   P_ARG
                                      , variables: Vs
                                      , results:  .Maps
                                      , subst:    SUBST
                                      )
                , subst:     SUBST
                )
    requires ARGs =/=K .Patterns

  rule #matchAux( terms:     Ts
                , pattern:   P
                , variables: Vs
                , results:   MR; MRs
                , subst:     SUBST
                )
    => #matchAux( terms:     Ts
                , pattern:   P
                , variables: Vs
                , results:   MR
                , subst:     SUBST
                ) ++Maps
       #matchAux( terms:     Ts
                , pattern:   P
                , variables: Vs
                , results:   MRs
                , subst:     SUBST
                )
    requires MRs =/=K .Maps

  // TODO: don't want to call substUnsafe directly (obviously)
  rule #matchAux( terms:     Ts
                , pattern:   P
                , variables: Vs
                , results:   SUBST1; .Maps
                , subst:     SUBST2
                )
    => #matchAux( terms:     Ts
                , pattern:   substUnsafe(P, SUBST1)
                , variables: Vs -Patterns fst(unzip(SUBST1))
                , results:   .Maps
                , subst:     SUBST1 SUBST2
                )

  rule #matchAux( terms:     T, Ts
                , pattern:  P
                , variables: Vs
                , results:   RESULTS
                , subst:     SUBST
                )
    => #matchAux( terms:     T
                , pattern:   P
                , variables: Vs
                , results:   RESULTS
                , subst:     SUBST
                ) ++Maps
       #matchAux( terms:     Ts
                , pattern:   P
                , variables: Vs
                , results:   RESULTS
                , subst:     SUBST
                )
    requires Ts =/=K .Patterns

  syntax Bool ::= checkSubstitution(Map, Patterns) [function] 
  rule checkSubstitution( .Map , Vs ) => true
  rule checkSubstitution( V |-> _ REST:Map , Vs ) => false
    requires notBool V in Vs
  rule checkSubstitution( V |-> _ REST:Map , Vs ) => checkSubstitution( REST, Vs )
    requires V in Vs
endmodule

module TEST-MATCHING-SYNTAX
    imports TOKENS-SYNTAX
    imports TEST-MATCHING
    imports PROVER-SYNTAX

    syntax KItem ::= Pattern // TODO: Explain why we're doing this
    syntax VariableName ::= "W" [token] | "X" [token] | "Y" [token] | "Z" [token]
                          | "W1" [token]
                          | "W2" [token]
                          | "X1" [token]
                          | "X2" [token]
                          | "Y1" [token]
                          | "Y2" [token]
                          | "Z1" [token]
                          | "Z2" [token]
    syntax Sort         ::= "Data" [token] | "Loc" [token]
endmodule

module TEST-MATCHING
  imports STRATEGY-MATCHING
  imports PROVER-DRIVER

  syntax Sort         ::= "Data" | "Loc"
  syntax Declaration ::= "assert" "(" MatchResults "==" MatchResults ")" [format(%1%2%i%i%n%3%d%n%4%i%n%5%d%d%6%n)]
  rule assert(EXPECTED == EXPECTED) => .K
endmodule
```

