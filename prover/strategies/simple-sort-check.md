```k
module STRATEGY-SIMPLE-SORT-CHECK
  imports PROVER-CORE
  imports STRATEGIES-EXPORTED-SYNTAX
  imports SORT-CHECKING-SYNTAX

  rule <strategy> simple-sort-check
               => #if isSortOf(GId, Term, Sort)
                  #then success #else fail #fi
                  ...
       </strategy>
       <id> GId </id>
       <claim> \typeof(Term, Sort) </claim>

 rule <strategy> simple-sort-check => fail </strategy>
      <claim> P </claim>
      requires \typeof(_,_) :/=K P

endmodule
```
