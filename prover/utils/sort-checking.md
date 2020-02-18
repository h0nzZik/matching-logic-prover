# Simple sort checking

The algorithm implemented by `isSortOf` is very simple.
It returns `true` only if the term surely falls into
the inhabitant set of given sort. If the function returns `false`,
the term still may or may not have given sort; thus, `false` 
means 'unknown'.

```k
module SORT-CHECKING-SYNTAX
  syntax Pattern
  syntax GoalId

  syntax Bool ::= isSortOf(GoalId, Pattern, Pattern) [function]

endmodule

module SORT-CHECKING-RULES
  imports SORT-CHECKING-SYNTAX
  imports KORE-HELPERS

/*
  rule isSortOf(_, _:Int, S:Symbol) => true
       requires SymbolToString(S) ==String "Int"

  rule isSortOf(_, _, _) => false [owise]

  rule isSortOf(_, \or(.Patterns), _) => true
  rule isSortOf(_, \or(P, Ps), S)
    => #if isSortOf(P, S) #then
         isSortOf(\or(Ps), S)
       #else
         false
       #fi

  // There may be a case where all the universe is one sort.
  // But this simple algorithm does not count with tha about sorts.
  rule isSortOf(\and(.Patterns), _) => false

  rule isSortOf(_, \and(P, Ps), S)
    => #if isSortOf(P, S) #then
         true
       #else
         isSortOf(_, \and(Ps), S)
       #fi

  // TODO quantifiers

  // TODO symbols and applications

  syntax Bool ::= "allSortsOf" "(" "patterns:" Patterns
                               "," "sorts:" Patterns
                               ")" [function]

  rule allSortsOf(patterns: .Patterns, sorts: .Patterns)
       => true

  rule allSortsOf(patterns: P, Ps, sorts: S, Ss)
       => #if isSortOf(P, S)
          #then true
          #else allSortsOf(patterns: Ps, sorts: Ss)
          #fi
*/
endmodule
```
