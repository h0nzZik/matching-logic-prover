```k
module STRATEGY-MATCHING
  imports PROVER-CORE
  imports PROVER-HORN-CLAUSE-SYNTAX
  imports PROVER-CONFIGURATION
  imports KORE-HELPERS
  imports MAP
  
//  rule <claim> \implies(\and(LSPATIAL, LHS) , \exists { Vs } \and(RSPATIAL, RHS)) </claim>
//       <strategy> match => #matchAux( term: LSPATIAL
//                                 , pattern: RSPATIAL
//                                 , vars: Vs
//                                 , rest: .Patterns
//                                 , results: .MatchResults
//                                 )
//                  ...
//       </strategy>
//    requires isSpatialPattern(LSPATIAL)
//     andBool isSpatialPattern(RSPATIAL)

                                         /* Subst, Rest */
  syntax MatchResult ::= "#matchResult" "(" "subst:" Map "," "rest:" Patterns ")"
  syntax MatchResult ::= "#matchFailure" "(" String ")"
  syntax MatchResults ::= List{MatchResult, ","} [klabel(MatchResults)]

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
                                      , subst:    .Map
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

  // rule #matchAux( terms:     (sep(ARGs), .Patterns) #as Ts
  //               , patterns:  sep(P_ARG, P_ARGs)
  //               , variables: Vs
  //               )
  //   => #matchAux( terms:     ARGs
  //               , patterns:  P_ARG, .Patterns
  //               , variables: Vs
  //               , subst:     .Map
  //               )
  //    , .MatchResults
  //   requires notBool(getFreeVariables(Ts) intersect Vs =/=K .Patterns)

  syntax Bool ::= checkSubstitution(Map, Patterns) [function] 
  rule checkSubstitution( .Map , Vs ) => true
  rule checkSubstitution( V |-> _ REST:Map , Vs ) => false
    requires notBool V in Vs
  rule checkSubstitution( V |-> _ REST:Map , Vs ) => checkSubstitution( REST, Vs )
    requires V in Vs
    



//#matchAux( term:    S(ARGs)
//        pattern: S(P_ARGs)
//        vars: VARS
//      )
//=> #checksomthing(zip(P_ARGs, ARGs))
//    requires S =/=K sep
//
//#matchAux( term:    S1(_)
//        pattern: S2(_)
//        vars: VARS
//      )
//=> .MatchResults
//   requires S1 =/=K sep
//    andBool S2 =/=K sep
//    andBool S1 =/=K S2
//    
// #matchAux( term:   sep(ARGs)
//         pattern: sep(P_ARG, P_ARGs)
//         vars: VARS
//      )
//=> #matchAux( term:   sep(ARGs)
//           pattern: sep(P_ARGs)
//           vars: VARS
//           rest: 
//           num_rotations: length(P_ARGs) 
//           recursive_results: 
//         )

//  rule #matchAux( term:    TERM
//             , pattern: sep(P, Ps)
//             , vars:    VARs
//             , rest:    REST
//             , results: .MatchResults
//                     => #matchAux( term:    term
//                              , pattern: sep(p)
//                              , vars:    vars
//                              , rest:    .pattern
//                              , results: .matchresults
//                              )
//             )
//    requires notBool Ps ==K .Patterns
//    
//  rule #matchAux( term:    TERM
//             , pattern: PATTERN  
//             , vars:    VARs
//             , rest:    REST
//             , results: M, Ms
//             )    
//  rule #matchAux( term:    sep(TERMs)
//             , pattern: sep(P:Pattern)  
//             , vars:    VARs
//             , results: .MatchResults
//             )
//    => #matchesTermIn( terms: TERMS
//                       pattern: P
//                     )

endmodule

module TEST-MATCHING-SYNTAX
    imports TOKENS-SYNTAX
    imports TEST-MATCHING
    imports PROVER-SYNTAX
    
    syntax KItem ::= Pattern // TODO: Explain why we're doing this
    syntax VariableName ::= "W" [token] | "X" [token] | "Y" [token] | "Z" [token]
    syntax Sort         ::= "Data" [token] | "Loc" [token]
endmodule

module TEST-MATCHING
  imports STRATEGY-MATCHING
  imports PROVER-DRIVER

  syntax Sort         ::= "Data" | "Loc"
  syntax Declaration ::= "assert" "(" MatchResults "==" MatchResults ")"
  rule assert(EXPECTED == EXPECTED) => .K
endmodule
```


```
```
#matchAux( term:    S(ARGs)
        pattern: S(P_ARGs)
        vars: VARS
      )
=> #checksomthing(zip(P_ARGs, ARGs))
    requires S =/=K sep

#matchAux( term:    S1(_)
        pattern: S2(_)
        vars: VARS
      )
=> .MatchResults
   requires S1 =/=K sep
    andBool S2 =/=K sep
    andBool S1 =/=K S2
    
 #matchAux( term:   sep(ARGs)
         pattern: sep(P_ARG, P_ARGs)
         vars: VARS
      )
=> #matchAux( term:   sep(ARGs)
           pattern: sep(P_ARGs)
           vars: VARS
           rest: 
           num_rotations: length(P_ARGs) 
           recursive_results: 
         )
  ++

#match ( term:    sep ( pto ( Vy { RefGTyp } , c_GTyp ( Vz { RefGTyp } ) ) , pto ( Vx { RefGTyp } , c_GTyp ( Vy { RefGTyp } ) ) ) 
       , pattern: sep ( pto ( Vx { RefGTyp } , c_GTyp ( F9 { RefGTyp } ) ) , pto ( F9 { RefGTyp } , c_GTyp ( Vz { RefGTyp } ) ) ) 
       , free:    F9 { RefGTyp }
       )
       
 --- Get list of terms that "sep( pto ( Vx { RefGTyp } , c_GTyp ( F9 { RefGTyp } ) ), REST )" can match with in TERM
      --- Get list of terms that "sep( pto ( Vx { RefGTyp } , c_GTyp ( F9 { RefGTyp } ) ), REST )" can match with in "sep( pto ( Vy { RefGTyp } , c_GTyp ( Vz { RefGTyp } ) ))"
          => .MatchResults
      --- Get list of terms that "sep( pto ( Vx { RefGTyp } , c_GTyp ( F9 { RefGTyp } ) ), REST )" can match with in "pto ( F9 { RefGTyp } , c_GTyp ( Vz { RefGTyp } ) )"
          => Result: Match: pto ( Vx { RefGTyp } , c_GTyp ( Vy { RefGTyp } ) )
                     Subst: F9 |-> Vy
                 Rest:  pto ( Vy { RefGTyp } , c_GTyp ( Vz { RefGTyp } ) )
 --- For each result above result, apply substitution and recurse
