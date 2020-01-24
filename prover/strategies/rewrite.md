```k
module STRATEGY-REWRITE
  imports PROVER-CORE
  imports STRATEGIES-EXPORTED-SYNTAX
  imports HEATCOOL-SYNTAX

  rule <strategy> rewrite N => rewrite -> N ...</strategy>

  rule <strategy> (.K => loadNamed(Name))
               ~> rewrite D Name ...
       </strategy>

  syntax KItem ::= loadNamed(AxiomOrClaimName)
  rule <strategy> loadNamed(Name) => P ...</strategy>
       <goal>
         ...
         <claim-name> Name </claim-name>
         <claim> P </claim>
         <strategy> success </strategy>
         ...
       </goal>

  rule <strategy> loadNamed(Name) => P ...</strategy>
       <declaration> axiom Name : P </declaration>

  rule <strategy> (P:Pattern ~> rewrite D _) => #rewrite1(P, D)
       ...</strategy>


  syntax KItem ::= #rewrite1(Pattern, RewriteDirection)

  syntax Bool ::= rewriteCheckShape(Pattern) [function]
  rule rewriteCheckShape(\equals(_, _)) => true
  rule rewriteCheckShape(\forall{_} P)
       => rewriteCheckShape(P)
  // TODO Curently we support only equalities
  //rule rewriteCheckShape(\implies(_, P))
  //     => rewriteCheckShape(P)
  rule rewriteCheckShape(_) => false [owise]

  rule <strategy> #rewrite1(P, D) => 
                  #if D ==K -> #then
                    #rewrite2(rewriteGetLeft(P), rewriteGetRight(P))
                  #else
                    #rewrite2(rewriteGetRight(P), rewriteGetLeft(P))
                  #fi
                  ...
       </strategy>
       requires rewriteCheckShape(P)

  syntax Pattern ::= rewriteGetLeft(Pattern) [function]
                 | rewriteGetRight(Pattern) [function]

  rule rewriteGetLeft(\equals(L,_)) => L
  rule rewriteGetRight(\equals(_,R)) => R
  rule rewriteGetLeft(\forall{_} P)
       => rewriteGetLeft(P)
  rule rewriteGetRight(\forall{_} P)
       => rewriteGetRight(P)
  rule rewriteGetLeft(\implies(_,P))
       => rewriteGetLeft(P)
  rule rewriteGetRight(\implies(_,P))
       => rewriteGetRight(P)

  syntax KItem ::= #rewrite2(Pattern, Pattern)


  // TODO how do we know which variables should heat use?
  // Should we just extract them from the pattern?
  rule <strategy> #rewrite2(L, R)
               => #rewrite3(heat(
                              term: T,
                              pattern: L,
                              variables: getFreeVariables(L),
                              index: 0
                            ), R)
                  ...
       </strategy>
       <claim> T </claim>

  syntax KItem ::= #rewrite3(HeatResult, Pattern)

  // TODO subgoals from implications
  rule <strategy> #rewrite3(heatResult(Heated, Subst), R)
               => noop
       ...</strategy>
       <claim> _ => cool(
                      heated: Heated,
                      term: substMap(R, Subst))
       </claim>

endmodule
```
