# Counterexample generalization algorithm

## Definitions

**The environment:** A map that associate every variable and function to a concrete value

**A constraint:** A property of the form:

- Variable = concrete value, or
- Function(concrete values) = concrete value

An environment can also be considered as a list of constraints.

**A mark:** A "pointer" to:

- A variable, or
- A function entry ( that is something of the form Function(concrete values) )

We use marks to "highlight" important constraints at a given point of the execution.

## AST

Our AST is decomposed into 4 main types:

- **Value**, that represents an expression without side effect (it can be evaluated to a boolean or to a user-defined uninterpreted type). Note: this should not be counfounded with what we call "concrete value". At runtime (within a given environment), a "value" is evaluated to a "concrete value".
Formulas are represented with values.

- **Expression**, that represents an expression with possibly side effects.

- **Statement**, that represent a statement (with, of course, side effects).

For the complete definition, please see:
https://github.com/E-Sh4rk/ivy-research/blob/master/invariant_synthesis/InvariantSynthesis/InvariantSynthesis/AST.fs

It is important to have a difference between Value (without side effect) and Expression (with side effects) at the AST level, because:

- In some places, it makes no sense to allow side effects (like in a formula for instance).
- Having the guarantee that a Value has no side effect allows us to compute a better generalization in many cases.

## Algorithm

**Input:** A counterexample, that is:

- A would-be invariant
- An initial environment that satisfies the invariant
- An IVy action, that is a transition, such that the invariant is broken after executing it with the initial environment

**Output:** A subset of the constraints of the initial environment,
such that every environment matching these constraints will broke the invariant after executing the IVy action.
From this subset, we can then easily generate a general formula that describe all configurations that lead to an execution breaking the invariant "in the same way than the counterexample".

**Method:**
We start by computing a subset of constraints of the final environment (post-execution) that is suficient to ensure that the invariant is false.
For that, we use the function *Marks_For_Value* (see below).

Then, we "roll back" through the execution of the action, by maintaining and updating the list of highlighted constraints (the *marks*).
For that, we use the function *RollBack_Statement* (see below).

```
Marks_For_Value =
	Input:	an environment, a value
	Output:	the evaluated concrete value in the environment,
		and a subset of constraints ensuring that the formula has this value
	For the computation of the "marks" (= the subset of constraints) :
	match value with
	| ValueConst c -> We mark nothing
	| ValueVar var -> We mark "var"
	| ValueFun fun args ->
		We evaluate the concrete values "vs" of the args
		and their marks "ms" by recursively calling Marks_For_Value.
		Then we compute the union of all "ms" and we add a mark to "fun(vs)".
	| ValueEqual (Value v1, Value v2) ->
		We compute marks for "v1" and "v2" using Marks_For_Value.
		We compute the union of these marks.
	| ValueOr (Value f1, Value f2) ->
		Depending on the evaluation of "f1" and "f2":
		- If both evaluate to the boolean false, we compute the marks for "f1" and for "f2", and we compute the union
		- If only "f1" is true, we compute the marks for "f1"
		- If only "f2" is true, we compute the marks for "f2"
		- If both "f1" and "f2" are true, we have the choice between computing the marks for "f1" and computing the marks for "f2".
		(in the current implementation, we compute both and choose the one that seems the better)
	| ValueNot (Value f) -> We compute marks for "f"
	| ValueForall (VarDecl d, Value f) ->
		We consider all possible concrete values for "d" (depending on its type).
		- If at least one of these values leads to a negative evaluation of "f", we can just compute marks for one of these values
		(in the current implementation, we compute them all and choose the one that seems the better)
		- Otherwise, we should compute the marks for ALL the possible concrete values of "d" and compute the union.
		However, it is not relevant, because if the model of the counterexample was different
		(in particular, the number of possible values for the type of "d"), then some more constraints could need to be marked (or unmarked).
		It is not acceptable because we want it to be general (our final counterexample generalization
		must be valid for all possible models).
		For now, we can consider that in this case, the algorithm fails. A solution will be proposed later.
		(in the current implementation, the algorithm doesn't fail but use special marks to indicate that they are model-dependent)
	| ... (ValueAnd and ValueExists can be expressed with previous operators)

RollBack_Statement =
	Input:	a statement, an environment before the execution of the statement, a list of marks after the execution of the statement
	Output:	an updated list of marks, before the execution of the statement
	match statement with
	| VarAssign (Variable var, Expression e) ->
		If "var" is already marked:
			We remove the mark on "var".
			We compute the marks before the expression using RollBack_Expression, by specifiing the result as important
		Else:
			We compute the marks before the expression using RollBack_Expression, by specifiing the result as non-important
	| IfSomeElse (VarDecl d, Value f, Statement if_st, Statement else_st) ->
		We consider all possible concrete values for "d" (depending on its type).
		- If at least one of these values satisfy the formula "f", we recursively compute the marks before the execution of the "if_st" statement.
		Then we compute the marks for the formula "f" (with the corresponding value for the variable "d") by using Marks_For_Value.
		We compute the union of these two lists of marks.
		Note that we make here the assumption that there always is at most one value that satisfy the formula "f",
		please see the implementation for more details.
		- Otherwise, we recursively compute the marks before the execution of the "else_st" statement.
		Then we compute the marks for the formula "Forall d. f" by using Marks_For_Value. We compute the union of these two lists of marks.
	| ...

NOTE: Some details are hidden here, for instance:
	- We must always (compute and) provide the right environment when calling Marks_For_Value/RollBack_Statement/RollBack_Expression.
	- In the IfSomeElse case, we have to be careful concerning the living variables in the environment
	(because the variable "d" is only living in the sif statement).
	It is necessary sometimes to replace/restore some parts of the environment/marks when entering/leaving a new block.


RollBack_Expression =
	Input:	an expression, an environment before the execution of the expression, a list of marks after the execution of the expression,
		a boolean that indicates whether the result (the concrete value) of this expression is important
	Output:	an updated list of marks, before the execution of the execution
	It looks like Marks_For_Value, but with the structure of RollBack_Statement (because expressions can have side effects).
	It will be detailled later.
```