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


endmodule

module SORT-CHECKING-RULES
  imports SORT-CHECKING-SYNTAX
  imports KORE-HELPERS

endmodule
```
