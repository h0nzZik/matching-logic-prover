```k
module STRATEGY-MATCHING
  imports PROVER-CORE
  imports PROVER-HORN-CLAUSE-SYNTAX
  imports PROVER-CONFIGURATION
  imports KORE-HELPERS
  imports MAP
  
//  rule <claim> \implies(\and(LSPATIAL, LHS) , \exists { Vs } \and(RSPATIAL, RHS)) </claim>
//       <strategy> match => #match( term: LSPATIAL
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

  syntax MatchResults ::= "#match" "(" "terms:"      Patterns
                                   "," "patterns:"   Patterns
                                   "," "variables:" Patterns
                                   ")" [function]
  syntax MatchResult ::= "#matchStuck" "(" K ")"
  rule #match( terms: Ts , patterns: Ps, variables: Vs)
    => #matchStuck( "terms:" ~> Ts ~> "patterns:" ~> Ps ~> "vars:" ~> Vs )
     , .MatchResults
    [owise]
    
  rule #match( terms: Ts, patterns: _, variables: Vs)
    => #matchFailure( "..." )
     , .MatchResults
    requires getFreeVariables(Ts) intersect Vs =/=K .Patterns 

  rule #match( terms:     (S:Symbol(ARGs), .Patterns) #as Ts
             , patterns:  S:Symbol(P_ARGs)
             , variables: Vs
             )
    => #matchResult( subst: removeIdentityMappings(zip(P_ARGs, ARGs)), rest: .Patterns )
     , .MatchResults
    requires S =/=K sep
    andBool notBool( getFreeVariables(Ts) intersect Vs =/=K .Patterns )
    andBool checkSubstitution(removeIdentityMappings(zip(P_ARGs, ARGs)), Vs)

  syntax Bool ::= checkSubstitution(Map, Patterns) [function] 
  rule checkSubstitution( .Map , Vs ) => true
  rule checkSubstitution( V |-> _ REST:Map , Vs ) => false
    requires notBool V in Vs
  rule checkSubstitution( V |-> _ REST:Map , Vs ) => checkSubstitution( REST, Vs )
    requires V in Vs
    



//#match( term:    S(ARGs)
//        pattern: S(P_ARGs)
//        vars: VARS
//      )
//=> #checksomthing(zip(P_ARGs, ARGs))
//    requires S =/=K sep
//
//#match( term:    S1(_)
//        pattern: S2(_)
//        vars: VARS
//      )
//=> .MatchResults
//   requires S1 =/=K sep
//    andBool S2 =/=K sep
//    andBool S1 =/=K S2
//    
// #match( term:   sep(ARGs)
//         pattern: sep(P_ARG, P_ARGs)
//         vars: VARS
//      )
//=> #match( term:   sep(ARGs)
//           pattern: sep(P_ARGs)
//           vars: VARS
//           rest: 
//           num_rotations: length(P_ARGs) 
//           recursive_results: 
//         )

//  rule #match( term:    TERM
//             , pattern: sep(P, Ps)
//             , vars:    VARs
//             , rest:    REST
//             , results: .MatchResults
//                     => #match( term:    term
//                              , pattern: sep(p)
//                              , vars:    vars
//                              , rest:    .pattern
//                              , results: .matchresults
//                              )
//             )
//    requires notBool Ps ==K .Patterns
//    
//  rule #match( term:    TERM
//             , pattern: PATTERN  
//             , vars:    VARs
//             , rest:    REST
//             , results: M, Ms
//             )    
//  rule #match( term:    sep(TERMs)
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
  syntax Declaration ::= assertEqual(MatchResults, MatchResults)
  rule assertEqual(EXPECTED, EXPECTED) => .K
endmodule
```


```
```
#match( term:    S(ARGs)
        pattern: S(P_ARGs)
        vars: VARS
      )
=> #checksomthing(zip(P_ARGs, ARGs))
    requires S =/=K sep

#match( term:    S1(_)
        pattern: S2(_)
        vars: VARS
      )
=> .MatchResults
   requires S1 =/=K sep
    andBool S2 =/=K sep
    andBool S1 =/=K S2
    
 #match( term:   sep(ARGs)
         pattern: sep(P_ARG, P_ARGs)
         vars: VARS
      )
=> #match( term:   sep(ARGs)
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
