import «Cs2120f24».Lectures.«02_prop_logic».formal.properties
import «Cs2120f24».Lectures.«02_prop_logic».formal.interpretation
import «Cs2120f24».Lectures.«02_prop_logic».formal.models_counterexamples
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.syntax
namespace cs2120f24

open PLExpr


/-!
SYNTAX

Suppose I want to write some propositional logic expressions
using the variable expressions, P, Q, and R, and building up
larger propositions using the propositional logic expression-
constructing operators. Here's how you do it.
-/

-- First define a disting variable for each variable expression
def v₀ : BoolVar := BoolVar.mk 0    -- abstract syntax
def v₁ : BoolVar := ⟨1⟩             -- Lean notation for mk
def v₂ : BoolVar := ⟨2⟩

/-!
Now you define the variable expressions you want to use. The
first line is using abstract syntax. The next two use our own
(non-standard) notation, desugaring to exactly that abstract
syntax.

These variables are already declared at this point. This is a
small design glitch that could be cleaned up. We comment them
out for now so as not to introduce conflicting definitions.
-/

def P : PLExpr := PLExpr.var_expr v₀
def Q : PLExpr := { v₁ }  -- our notation for var_expr constructor
def R : PLExpr := { v₂ }

/-
Now that you have three variable expressions to work with,
you can use logical expression "connectives" (operators) to
build bigger expressions. Consider the expression, P ∧ Q,
for example. First we'll write it using abstract syntax,
then using concrete syntax.
-/

/-!
Here we show the equivalence of abstract and concrete syntax.
-/
def P_and_Q_abstract : PLExpr :=
  (PLExpr.bin_op_expr BinOp.and P Q)

/-!
Standard concrete infix notation for (PLExpr.bin_op_expr BinOp.and
That is the actual desugarad representation of ∧. Other propositional
logic concrete notations (and the concepts they represent) reduce to
these abstract sybtax repreesentations.
-/
def P_and_Q_concrete := P ∧ Q
#reduce P_and_Q_concrete
/-!
(bin_op_expr BinOp.and) -- this is ∧
  (var_expr { index := 0 }) -- the first conjunct, P
  (var_expr { index := 1 }) -- the second conjunct, Q
-/


/-! SEMANTICS UNDER INTERPRETATIONS

We can easily enumerate all possible interpretations.
That's jsut the "input" side of a truth table. Notice
that this part doesn't depend on the details of e (an
expression) at all. The driving factor is the number
number of *variables* (columns). The number of rows is
then 2^#columns. But there's more. What relationship
do you see between the row indices and the row contents?
-/

/-!
            var
           0   1
  index  | P | Q | e
    0    | 0 | 0 | _
    1    | 0 | 1 | _
    2    | 1 | 0 | _
    3    | 1 | 1 | _
-/

/-!
Recall that we represent each interpretation (each row)
as a function. That function takes a variable (it's index)
as an actual parameter, and returns the Boolean value for
that variable *in that row* ("under that interpretation").

But of course the value for that variable in that row is
just the (0 for false / 1 for true) Boolean value in the
*binary expansion* of the row index. Is everyone okay with
base 2 arithmetic? So all of this can easily programmed.

Here we compute the interpretation in row index 2 in the
preceding example. Note that e's not involved except to
the extent that it determines the number of variables in
one.
-/

def i := InterpFromRowCols 2 2
#check i

/-!
Applying i to a *variable*, with indices 0 or 1, should
return the values in row 2, namely 1 and 0. Does it work?
(Remember ⟨⟩ notation for applying structure constructor,
so here ⟨0⟩ is (BoolVar.mk 0), a "variable" in our lexicon.)
-/

#eval! i ⟨0⟩    -- expect true
#eval! i ⟨1⟩    -- expect false

/-!
 It's exactly this trick that is used in the semantic
evaluation function that defines for us an operational
semantics for propositional logic. That means that we
have a *function* for computing an expression's meaning
given an interpretation, i, giving the semantic values
of the variables in the expression.
-/

def e := P_and_Q_concrete

#eval! evalPLExpr e i

/-!
Given the semantic meanings (Boolean functions) that
we've given our syntactic operators, we see that the
proposition/expression e evaluates to true under the
interpretation, i. We will thus say that i is a model
of e. It represents a world in which e is true.
-/

/-!
Convenience functions for working with our representations of interpretations

An interpretation, i, is a function. It's generally not
helpful to print functions in Lean. If you want to see a
string representation of an interpretation, we do have a
function for that. You pass it the interpretation and how
many columns you want to see. An interpretation function
is technicallky defined as false for all column indices
beyond those of interest in a given case.
-/

#eval! bitStringsFromInterp i 2

/-!
We also provide a function for converting a list of Bool
values into an interpretation.
-/

def i2 := interpFromBools [true, false, true]
#eval! bitStringsFromInterp i2 3

/-!
And finally a way to get a printable list of multiple
(typically all) interpretations.
-/

/-!
All interpretations

Up to now we've been working with one interpretation, i.
We can also easily obtain, and provide a function, for
getting a list of *all* interpretations for an expression
with "n" variables, for any number, n. This function first
counts the number of variables in e and then constructs a
list of interpretatins, one for each index from 2^n-1 to 0.
-/

def all_interps_e := listInterpsFromExpr e



/-!
TRUTH TABLES

You already know you can get the results of evaluating an
expression e for each interpretation in a given list of them.
-/

#eval! truthTableOutputs e

/-
We see that e (go back and see how we defined it) is actually
valid. And now of course you can see how we check validity for
any expression. We count the variables in it, we generate 2^n

-/

#eval! truthTableOutputs ¬e


/-!
PROPERTIES OF EXPRESSIONS

As you know, validity just means that a proposition is true
under every interpretation -- in all worlds -- making it into
a general-purpose reasoning principle. The is_valid function
takes an expression, computes its number of variable, gets a
list of all interpretations
-/

#eval! is_valid e
#eval! is_sat e
#eval! is_unsat ¬e


/-!
TRUTH TABLES (output vectors). The returned
list is the semantic meaning of the single
given expression under each ]interpretation,
starting with all true and descending to all
false. (We have a note to clean this up.)
-/

#eval! (truthTableOutputVector (P))
#eval! (truthTableOutputVector (P ∧ Q))


/-!
Examples: Checking satisfiability-related properties of a few expressions
-/

#reduce is_sat ⊤
#reduce is_sat ⊥

#reduce is_sat P
#reduce is_unsat P
#reduce is_valid P

#reduce is_sat ¬P
#reduce is_unsat ¬P
#reduce is_valid ¬P

#reduce is_sat (P ∨ ¬P)
#reduce is_unsat (P ∨ ¬P)
#reduce is_valid (P ∨ ¬P)

#reduce is_sat (P ∧ ¬P)
#reduce is_unsat (P ∧ ¬P)
#reduce is_valid (P ∧ ¬P)

#reduce is_sat (P ∧ Q)
#reduce is_unsat (P ∧ Q)
#reduce is_valid (P ∧ Q)

#reduce is_sat (P ∨ Q)
#reduce is_unsat (P ∨ Q)
#reduce is_valid (P ∨ Q)


/-!
Homework #1

1.Complete the sentence: If a proposition is not valid,
then there is at least one __________.

2. Read the following propositions in English and render
them into the formal language of propositional logic. We
will get you started by defining three new propositional
variables: isRaining, streetWet, and sprinklerOn. Now for
each of the following propositions expressed in English,
express it formally using these PL variable expressions.
Here then are our three new PL variable expressions. The
identifer's we're binding to these terms remind us what
we are going to want these terms to mean "in the world."
-/

def itsRaining : PLExpr := PLExpr.var_expr v₀
def sprinklerOn : PLExpr := PLExpr.var_expr v₁
def streetWet : PLExpr := PLExpr.var_expr v₂

/-
For each of the following English language expressions write
the corresponding expression using our concrete propositional
logic syntax. Give names to these propositions (PLExpr's) in
the pattern of p0, p1, p2, as seen below.
-/

/-!
It's raining and the sprinkler's on.
-/
def p0 : PLExpr := itsRaining ∧ sprinklerOn

/-!
The sprinler's on and it's raining.
-/
def p1  : PLExpr := sorry

/-!
If it's raining, then if the sprinkler's on, then it's
raining and the sprinkler is on. Conditional (if this
then that) expressions in natural language are written
formally in propositional and predicate logic using the
implication (implies) operator, imp (⇒ in our notation).
-/
def p2  : PLExpr := itsRaining ⇒ sprinklerOn ⇒ p0

/-!
If it's raining and the sprinkler's running, then it's raining.
-/
def p3  : PLExpr := (itsRaining ∧ sprinklerOn) ⇒ itsRaining

/-!
If it's raining ,then it's raining or the sprinkler's running.
-/
def p4  : PLExpr := sorry

/-!
If the sprinkler's running, it's raining or the sprinkler's running.
-/
def p5  : PLExpr := sorry

/-!
Whenever it's raining the streets are wet.
-/
def p6  : PLExpr := sorry

/-!
Whenever the sprinkler's running the streets are wet.
-/
def p7  : PLExpr := sorry

/-!
If (a) it's raining or the sprinkler's running, then (b) if
whenever it's raining then the streets are wet, then (c) if
whenever the sprinkler's running then the streets are wet, then
_________. What is the conclusion? Write the expression in PL.
-/

def p8  : PLExpr := (itsRaining ∨ sprinklerOn) ⇒ (itsRaining ⇒ streetWet) ⇒ (sprinklerOn ⇒ streetWet) ⇒ streetWet
#eval! is_valid p8
#eval! is_sat p8
#eval! is_unsat p8



/-!
If whenever it's raining, the streets are wet, then whenever the
streets are wet it's raining.
-/
def p9  : PLExpr := sorry


/-!
If whever it's raining then bottom, then it's not raining.
-/
def p10  : PLExpr := sorry

/-!
If it's raining or the sprinkler's running then if it's
not raining then the sprinkler's running.
-/
def p11 : PLExpr := sorry

/-!
If whenever it's raining the streets are wet, then whenever the
streets are not wet, it must not be raining.
-/
def p12 : PLExpr := sorry

/-!
QUIZ: challenges to come
-/
def p13 : PLExpr := sorry
def p14 : PLExpr := sorry
def p15 : PLExpr := sorry

end cs2120f24
