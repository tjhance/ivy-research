
Possible research:

  - Improving invariant synthesis (https://www.cs.tau.ac.il/~maon/pubs/cav15.pdf)
  - Semi-automated transformations to avoid some quantifier-alternation cycles by introducing new relations (https://www.cs.tau.ac.il/~odedp/paxos-made-epr-oopsla17.pdf)
  - Semi-automated fragmentation of code to avoid some quantifier-alternation cycles. Each fragment can use a different decidable frgament of 1st order logic (Modularity for Decidability paper)
  - Transformation of liveness properties into first order formulas (https://www.cs.tau.ac.il/~odedp/reducing-liveness-to-safety-in-first-order-logic/popl18-reducing-liveness-to-safety-in-first-order-logic.pdf)


Other Possible Improvements:

  - More (interpreted) types if possible! Sum types (~ enumerated types), tuples (~ struct), etc
  - Adding a way to abstract the representation of custom types in order to have a better representation of counterexamples (for instance when using a queue) -> add directives to change representation (example: transitive flag, how to display values and relations, etc)
  - Ivy_to_cpp : store relations using other ways in order to allow more things on non-iterable type (like structs) + allow the use of functions if of the form (default value + finite nb of exceptions)
  - Fix some bugs


IVy Bugs:

  - Many runtime exceptions in the model checking tool
  - Runtime exceptions when using enumerated types
  - Can't build the sht example (doc/examples/sht)! (python runtime exception) ----> FIXED!
  - Some bugs with generalization/minimization tool (see custom queue)? Hypothesis: model checker doesn't take some "after init" procedures into account
