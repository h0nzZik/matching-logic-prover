SMT Driver
==========

This file is responsible for loading definitions in the SMT2 format.

```k
module SMT-DRIVER
  imports KORE-SUGAR
  imports KORE-HELPERS
  imports PROVER-CONFIGURATION
  imports SMTLIB2
  imports SMTLIB-SL
  imports PROVER-CORE-SYNTAX
  imports PROVER-HORN-CLAUSE-SYNTAX

  syntax GoalBuilder ::= "#goal" "(" "goal:"     Pattern
                                 "," "strategy:" Strategy
                                 "," "expected:" K
                                 ")"

  rule <k> S:SMTLIB2Script
        => #goal( goal: \exists { .Patterns } \and( .Patterns )
                , strategy: search-sl(bound: 5)
                , expected: success
                )
        ~> S
           ...
       </k>

  rule <k> _:GoalBuilder
        ~> (C Cs:SMTLIB2Script => C ~> Cs)
           ...
       </k>

  rule <k> _:GoalBuilder ~> ((set-logic _) => .) ... </k>
  rule <k> _:GoalBuilder ~> ((set-info ATTR _) => .) ... </k>
    requires ATTR =/=K :mlprover-strategy
     andBool ATTR =/=K :status

  rule <k> #goal( goal:     _
                , strategy: _
                , expected: _ => #statusToTerminalStrategy(STATUS)
                )
        ~> ((set-info :status STATUS) => .)
          ...
      </k>

  rule <k> #goal( goal:     _
                , strategy: _ => STRAT
                , expected: _
                )
        ~> ((set-info :mlprover-strategy STRAT) => .)
          ...
      </k>

  rule <k> #goal( goal: \exists { Us }
                        \and(Ps => (SMTLIB2TermToPattern(TERM, Us), Ps))
                , strategy: _
                , expected: _
                )
        ~> ( (assert TERM) => .K )
           ...
       </k>

  rule <k> _:GoalBuilder ~> ((declare-sort SORT 0) => .) ... </k>
       <declarations> ( .Bag
                     => <declaration> sort SMTLIB2SortToSort(SORT) </declaration>
                      ) ...
       </declarations>

  rule <k> #goal( goal: \exists { Us
                               => (SMTLIB2SimpleSymbolToVariableName(ID) { SMTLIB2SortToSort(SORT) }, Us)
                                }
                        \and(Ps)
                , strategy: _
                , expected: _
                )
        ~> ( (declare-const ID SORT) => .K )
           ...
       </k>

  rule <k> _:GoalBuilder
        ~> ( (declare-heap .SMTLIB2SortPairList)
          => .K
           )
           ...
       </k>
       <declarations> ( .Bag
                     => <declaration> sort Heap </declaration>
                        <declaration> symbol sep(Heap, Heap) : Heap </declaration>
                        <declaration> symbol emp ( .Sorts ) : Heap </declaration>
                      ) ...
       </declarations>

  rule <k> _:GoalBuilder
        ~> ( (declare-heap (LOC DATA) SORTPAIRs)
          => (declare-heap SORTPAIRs)
           )
           ...
       </k>
       <declarations> ( .Bag
                     => <declaration> symbol pto(SMTLIB2SortToSort(LOC), SMTLIB2SortToSort(DATA)) : Heap </declaration>
                        <declaration> symbol parameterizedSymbol(nil, SMTLIB2SortToSort(LOC)) ( .Sorts ) : SMTLIB2SortToSort(LOC) </declaration>
                        <declaration> axiom  heap(SMTLIB2SortToSort(LOC), SMTLIB2SortToSort(DATA)) </declaration>
                        <declaration> axiom  functional(parameterizedSymbol(nil, SMTLIB2SortToSort(LOC))) </declaration>
                      ) ...
       </declarations>

  rule <k> _:GoalBuilder
        ~> ((declare-datatypes ( .SMTLIB2SortDecList ) ( .SMTLIB2DatatypeDecList )) => .)
           ...
       </k>

  rule <k> _:GoalBuilder
        ~> ( (declare-datatypes ( (SORT1 0) SDECs ) ( ( ( CTOR SELDECs ) .SMTLIB2ConstructorDecList ) DDECs ) )
          => (declare-datatypes ( SDECs ) ( DDECs ))
           )
           ...
       </k>
       <declarations> ( .Bag
                     => <declaration> sort SMTLIB2SortToSort(SORT1) </declaration>
                        <declaration> symbol SMTLIB2SimpleSymbolToSymbol(CTOR)(SelectorDecListToSorts(SELDECs)) : SMTLIB2SortToSort(SORT1) </declaration>
                      ) ...
       </declarations>

  syntax Sorts ::= SelectorDecListToSorts(SMTLIB2SelectorDecList) [function]
  rule SelectorDecListToSorts(.SMTLIB2SelectorDecList) => .Sorts
  rule SelectorDecListToSorts((_ SORT) SELDECs) => SMTLIB2SortToSort(SORT), SelectorDecListToSorts(SELDECs)

  rule <k> _:GoalBuilder
        ~> ( (define-fun-rec ID (ARGS) RET BODY)
          => .K
           )
           ...
       </k>
       <declarations> ( .Bag
                     => <declaration> symbol SMTLIB2SimpleSymbolToSymbol(ID)(SMTLIB2SortedVarListToSorts(ARGS))
                                             : #returnSort(SMTLIB2TermToPattern(BODY, SMTLIB2SortedVarListToPatterns(ARGS)), SMTLIB2SortToSort(RET), SMTLIB2SimpleSymbolToSymbol(ID))
                        </declaration>
                        <declaration> axiom \forall { SMTLIB2SortedVarListToPatterns(ARGS) }
                                         \iff-lfp( SMTLIB2SimpleSymbolToSymbol(ID)(SMTLIB2SortedVarListToPatterns(ARGS))
                                                 , #normalizeDefinition(SMTLIB2TermToPattern(BODY, SMTLIB2SortedVarListToPatterns(ARGS)))
                                                 )
                        </declaration>
                        <declaration> axiom functional(SMTLIB2SimpleSymbolToSymbol(ID)) </declaration>
                      ) ...
       </declarations>

  // Note: We cannot call isPredicatePattern because that requires knowing the return type of the
  // symbols inside before calling. This is not feasible since they may be recursive symbols.
  syntax Sort ::= #returnSort(Pattern, Sort, Symbol) [function]
  rule #returnSort(P, Bool, S) => Heap
    requires #containsSpatial(P, S)
  rule #returnSort(P, Bool, _) => Bool
    [owise]

  syntax Bool ::= #containsSpatial(Pattern, Symbol)          [function]
  syntax Bool ::= #containsSpatialPatterns(Patterns, Symbol) [function]
  rule #containsSpatial(_{_}, _) => false
  rule #containsSpatial(_:Int, _) => false
  rule #containsSpatial(sep(_), _) => true
  rule #containsSpatial(pto(_), _) => true
  rule #containsSpatial(\equals(P1, P2), S) => #containsSpatial(P1, S) orBool #containsSpatial(P2, S)
  rule #containsSpatial(\forall{_}(P), S) => #containsSpatial(P, S)
  rule #containsSpatial(\exists{_}(P), S) => #containsSpatial(P, S)
  rule #containsSpatial(\not(P), S) => #containsSpatial(P, S)
  rule #containsSpatial(\and(Ps), S) => #containsSpatialPatterns(Ps, S)
  rule #containsSpatial(\or(Ps), S) => #containsSpatialPatterns(Ps, S)

  // For recursive calls: must only check arguments of calls to avoid infinite looping
  rule #containsSpatial(S(Ps), S) => #containsSpatialPatterns(Ps, S)
    requires S =/=K sep andBool S =/=K pto

  // If S2 calls another symbol S1 that returns a heap, then S2 is spatial
  rule #containsSpatial(S1(Ps), S2) => true
    requires S1 =/=K sep andBool S1 =/=K pto andBool S1 =/=K S2 andBool getReturnSort(S1(Ps)) ==K Heap

  // If S2 calls another symbol S1 that does not return a heap, then recurse on the arguments of S1
  rule #containsSpatial(S1(Ps), S2) => #containsSpatialPatterns(Ps, S2)
    requires S1 =/=K sep andBool S1 =/=K pto andBool S1 =/=K S2 andBool getReturnSort(S1(Ps)) =/=K Heap

  rule #containsSpatialPatterns(.Patterns, _) => false
  rule #containsSpatialPatterns((P, Ps), S) => #containsSpatial(P, S) orBool #containsSpatialPatterns(Ps, S)

  rule <k> #goal( goal: (\exists{Vs} \and(Ps)) #as PATTERN, strategy: STRAT, expected: EXPECTED)
        ~> (check-sat)
        => #goal( goal: PATTERN, strategy: STRAT, expected: EXPECTED)
           ...
       </k>
       <goals>
         ( .Bag =>
           <goal>
             <id> root </id>
             <active> true:Bool </active>
             <parent> .K </parent>
             <claim> \implies(\and(#filterPositive(Ps)), \and(\or(#filterNegative(Ps)))) </claim>
             <strategy> STRAT </strategy>
             <expected> EXPECTED </expected>
             <trace> .K </trace>
           </goal>
         )
         ...
       </goals>
   requires notBool PATTERN ==K  \exists { .Patterns } \and ( .Patterns )
```

```k
  syntax Patterns ::= "#filterNegative" "(" Patterns ")" [function]
  rule #filterNegative(\not(P), Ps) => P, #filterNegative(Ps)
  rule #filterNegative(P, Ps)       => #filterNegative(Ps) [owise]
  rule #filterNegative(.Patterns)   => .Patterns

  syntax Patterns ::= "#filterPositive" "(" Patterns ")" [function]
  rule #filterPositive(\not(P), Ps) => #filterPositive(Ps)
  rule #filterPositive(P, Ps)       => P, #filterPositive(Ps) [owise]
  rule #filterPositive(.Patterns)   => .Patterns
```

Some of the SL-COMP18 benchmarks call `(check-sat)` when the assertion set is empty,
and have the expected result set to `unsat`. This is just plain wrong. The following
works around that issue:

```k
  rule <k> #goal( goal: \exists { .Patterns } \and ( .Patterns )
                , strategy: _
                , expected: _
                ) #as GOAL:GoalBuilder
        ~> (check-sat)
        => GOAL
           ...
       </k>
```

Clear the `<k>` cell once we are done:

```k
  rule <k> _:GoalBuilder ~> .SMTLIB2Script
        => .K
       </k>
```

```k
  syntax Pattern ::= #normalizeDefinition(Pattern) [function]
  rule #normalizeDefinition(\or(Ps)) => \or(#exists(#flattenOrs(#dnfPs(Ps)), .Patterns))

  syntax Strategy ::= #statusToTerminalStrategy(CheckSATResult) [function]
  rule #statusToTerminalStrategy(unsat)      => success
  rule #statusToTerminalStrategy(sat)        => fail
  rule #statusToTerminalStrategy(unknown)    => fail
  rule #statusToTerminalStrategy(unknown(_)) => fail

  syntax Pattern ::= SMTLIB2TermToPattern(SMTLIB2Term, Patterns) [function]
  rule SMTLIB2TermToPattern( (exists ( ARGS ) T), Vs ) => \exists { SMTLIB2SortedVarListToPatterns(ARGS) } SMTLIB2TermToPattern(T, SMTLIB2SortedVarListToPatterns(ARGS) ++Patterns Vs)
  rule SMTLIB2TermToPattern((and Ts), Vs) => \and(SMTLIB2TermListToPatterns(Ts, Vs))
  rule SMTLIB2TermToPattern((or Ts), Vs) => \or(SMTLIB2TermListToPatterns(Ts, Vs))
  rule SMTLIB2TermToPattern((distinct L R), Vs) => \not(\equals(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs)))
  rule SMTLIB2TermToPattern((= L R), Vs) => \equals(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((< L R), Vs) => lt(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((> L R), Vs) => gt(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((<= L R), Vs) => lte(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((>= L R), Vs) => gte(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((+ L R), Vs) => plus(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((- L R), Vs) => minus(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((* L R), Vs) => mult(SMTLIB2TermToPattern(L, Vs), SMTLIB2TermToPattern(R, Vs))
  rule SMTLIB2TermToPattern((not T), Vs) => \not(SMTLIB2TermToPattern(T, Vs))
  rule SMTLIB2TermToPattern((ite C L R), Vs) => \or( \and(SMTLIB2TermToPattern(C, Vs), SMTLIB2TermToPattern(L, Vs))
                                                   , \and(\not(SMTLIB2TermToPattern(C, Vs)), SMTLIB2TermToPattern(R, Vs)))
  rule SMTLIB2TermToPattern(I:Int, _) => I
  rule SMTLIB2TermToPattern(#token("true", "LowerName"), _) => \top()
  rule SMTLIB2TermToPattern(#token("false", "LowerName"), _) => \bottom()
  rule SMTLIB2TermToPattern((as nil SORT), _) => parameterizedSymbol(nil, SMTLIB2SortToSort(SORT))(.Patterns)
  rule SMTLIB2TermToPattern((underscore emp _ _), _) => emp(.Patterns)

  rule SMTLIB2TermToPattern((ID Ts), Vs) => SMTLIB2SimpleSymbolToSymbol(ID)(SMTLIB2TermListToPatterns(Ts, Vs))
    [owise]
  rule SMTLIB2TermToPattern(ID:SMTLIB2SimpleSymbol, Vs) => SMTLIB2SimpleSymbolToVariableName(ID) { getSortForVariableName(SMTLIB2SimpleSymbolToVariableName(ID), Vs) }
    [owise]

  syntax Patterns ::= SMTLIB2TermListToPatterns(SMTLIB2TermList, Patterns) [function]
  rule SMTLIB2TermListToPatterns(.SMTLIB2TermList, _) => .Patterns
  rule SMTLIB2TermListToPatterns(T Ts, Vs) => SMTLIB2TermToPattern(T, Vs), SMTLIB2TermListToPatterns(Ts, Vs)

  syntax Patterns ::= SMTLIB2SortedVarListToPatterns(SMTLIB2SortedVarList) [function]
  rule SMTLIB2SortedVarListToPatterns(.SMTLIB2SortedVarList) => .Patterns
  rule SMTLIB2SortedVarListToPatterns((SYMBOL SORT) Ss) => SMTLIB2SimpleSymbolToVariableName(SYMBOL) { SMTLIB2SortToSort(SORT) }, SMTLIB2SortedVarListToPatterns(Ss)

  syntax Sorts ::= SMTLIB2SortedVarListToSorts(SMTLIB2SortedVarList) [function]
  rule SMTLIB2SortedVarListToSorts(.SMTLIB2SortedVarList) => .Sorts
  rule SMTLIB2SortedVarListToSorts((SYMBOL SORT) Ss) => SMTLIB2SortToSort(SORT), SMTLIB2SortedVarListToSorts(Ss)
```

```k
endmodule
```

```k
module PROVER-SMT-SYNTAX
  imports PROVER-COMMON-SYNTAX
  imports SMTLIB2-SYNTAX
  imports SMTLIB-SL

  // HACK: We disallow open parenthesis to reduce conflicts when tokenizing strategies
  syntax PipeQID ::= r"\\|[^\\|(]*\\|" [priority(100), token, autoReject]
```

When parsing with the SMTLIB2 syntax, we use semicolons as comments:

```k
  syntax #Layout ::= r"(;[^\\n\\r]*)"     // SMTLIB2 style semicolon comments
                   | r"([\\ \\n\\r\\t])"  // whitespace

endmodule
```

