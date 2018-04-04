IVy Bugs:

  - Many runtime exceptions in the model checking tool
  - Runtime excetpions when using enumerated types
  - Can't build their sharded ht example (doc/examples/sht)! (python runtime exception) ----> FIXED!
  - Some bugs with generalization/minimization tool (see custom queue)? Hypothesis: model checker doesn't take some after init procedures into account

--

Possible research:

  - Improving invariant synthesis (folder invariant_synthesis)
  - Semi-automated transformations to avoid some quantifier-alternation cycles by introducing new relations (but already done in the OOPSLA paper)
  - Semi-automated fragmentation of code to avoid some quantifier-alternation cycles. Each fragment can use a different decidable frgament of 1st order logic

--

Other Possible Improvements:

  - More (interpreted) types! Sum types, tuples, etc
  - Way to abstract custom types representation (for instance queue) -> directives to change display (example: transitive flag)
  - Ivy_to_cpp : store relations using other ways in order to allow more things on non-iterable type (like structs) + permit to use functions if of the form (default value + finite nb of exceptions)
  - Fix some bugs
