---
title: Semantics-based test case generation
author:
  - Nishant Rodrigues
  - Manasvi Saxena
---

Overview
--------

Goal: Create a fuzzing tool that is both **language-agnostic** and **semantics-aware**

Our approach can be thought of as an extension of both:

* Skelatal Program Enumeration, and
 
* Grammar based fuzzing

The K Framework
---------------

K is a framework for formally specifying languages using the semantics-first approach.


::: columns

:::: {.column width=33%}
Several languages are already defined:

1.  C
2.  Python
3.  LLVM
4.  Java
5.  JavaScript
6.  EVM
7.  Solidity
8.  ...
::::

:::: {.column width=33%}
Several tools can already be derived:

* Parser
* Interpreter
* Model Checker
* Deductive Verifier
* Equivalence checker

>  * <mark> Fuzzer? </mark>
::::

:::: {.column width=33%}
![](../../doc/k.png){width="100%"}
::::
:::

What does a K semantics look like?
----------------------------------

:::columns

:::: column


``` {.k .dense}
syntax AExp  ::= Int | Id
               | "-" Int
               | AExp "/" AExp      [left, strict]
               > AExp "+" AExp      [left, strict]
               | "(" AExp ")"       [bracket]
syntax BExp  ::= Bool
               | AExp "<=" AExp     [seqstrict]
               | "!" BExp           [strict]
               > BExp "&&" BExp     [left, strict(1)]
               | "(" BExp ")"       [bracket]
syntax Block ::= "{" "}"
               | "{" Stmt "}"
syntax Stmt  ::= Block
               | Id "=" AExp ";"    [strict(2)]
               | "if" "(" BExp ")"
                 Block "else" Block [strict(1)]
               | "while" "(" BExp ")" Block
               > Stmt Stmt          [left]
syntax Pgm ::= "int" Ids ";" Stmt
syntax Ids ::= List{Id,","}
```

``` {.k .dense}
configuration <T color="yellow">
                <k color="green"> $PGM:Pgm </k>
                <state color="red"> .Map </state>
              </T>
```

::::

:::: column
``` {.k .dense}
  rule <k> X:Id => I ... </k>
       <state>... X |-> I ...</state>

// Integer arithmetic
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I1 => 0 -Int I1

// Boolean arithmetic
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false

// Block
  rule {} => .
  rule {S} => S

// Stmt
  rule <k> X = I:Int; => . ...</k>
       <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S
    => if (B) {S while (B) S} else {}

// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S
```
::::

:::

Semantics-based test case generation
------------------------------------

1. Execute a symbolic program "skeleton"
2. Guide the execution process to avoid uninteresting programs
3. Replace remaining symbolic variables with arbitary concrete values


Executing symbolic programs
---------------------------


:::columns

:::: {.column }

Leverage K's symbolic execution engine, and narrowing.

* Execute a symbolic program "skeleton"
* When symbolic variables are encountered, K "narrows" on those variables 
* These choices are semantics-driven, so only semantically meaningful choices are made


Most symbolic engines support this:

```k
  int x, y;
  x = ?X:Int;
  y = ?X:Int
  while (x < y) { ... }
  if (x == 2) { ... } 
```

::::

:::: {.column }
![](../../doc/narrowing-on-statements.png){width="50%"}

K allows this:

```k
  int x, y;
  ?V:Id = ?I:Int;
  ?T1:Stmt
  ?T2:Stmt
```

::::
:::

---------------------

:::columns
:::: column

### Guidance needed

* State-space is HUGE!
* Suppose we generate a program that does not terminate?

...

* Limit the application of some rules

::::
:::: column
### Concretization

Since only branches that were executed are narrowed, there are still remaining symbolic variables

```k
  int x, y;
  x = 2;
  if ( false ) { ?S:Stmt }
  ...
```

We chose arbitary values for remaining variables:

```k
  int x, y;
  x = 2;
  if ( false ) { { } }
  ...
```

::::
:::

---

:::columns
:::: column

### Prototype Evaluation

* Generated 1988 programs in 10 minutes
* Programs cover 100% of the language semantics

### Caveats

* Some manual modifications needed for instrumentation; We should automate these
* Guidance heuristic is very simple, will probably not be good enough for more complex languages
 
::::
:::: column

### Next steps

* Port to other languages, and use as a source of tests for diffrential testing. Solidity? JavaScript?
* Performance: Currently, we run K every time we take a step, this is expensive
* Better integration with the K

::::
:::
