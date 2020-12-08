---
title: "Semantics-based test case generation"
author:
  - Nishant Rodrigues
  - Manasvi Saxena
theme: white
transition: none
center: false
---

Overview
--------

Goal: Create a fuzzing tool that is both **language-agnostic** and **semantics-aware**.

Our approach can be thought of as an extension of both:

* Skelatal Program Enumeration, and
* Grammar based fuzzing

The 𝕂 Framework
---------------

𝕂 is a framework for formally specifying languages using the semantics-first
approach.

::: columns

:::: {.column }

::::: {.r-stack}
:::::: {.fragment .fade-in-then-out}
Several languages are already defined:

*  C
*  Python
*  LLVM
*  Java
*  JavaScript
*  EVM
*  Solidity
*  ...

::::::

:::::: {.fragment .fade-in-then-out}
Several tools can already be derived:

* Parser
* Interpreter
* Model Checker
* Deductive Verifier
* Equivalence checker
* 
::::::

:::::: {.fragment .fade-in-then-out}
Several tools can already be derived:

* Parser
* Interpreter
* Model Checker
* Deductive Verifier
* Equivalence checker
* <mark> Fuzzer? </mark> 
::::::

:::::
::::

:::: {.column}
![](../../doc/k.png){width="100%"}
::::
:::

What does a 𝕂 semantics look like?
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

Our insight
-----------

𝕂 makes no distinction between program constructs and language constructs such as statements.

:::columns

::::column
:::::{.fragment .fade-in}

Most symbolic engines support this:

```k
  int x, y;
  x = ☐:Int;
  y = ☐:Int;
  while (x < y) { ... }
  if (x == 2) { ... } 
```
:::::
::::

::::column
:::::{.fragment .fade-in}
𝕂 also allows this:

```k
  int x, y;
  ☐:Id = ☐:Int;
  ☐:Stmt
  ☐:Stmt

```
:::::
::::
:::

Semantics-based test case generation
------------------------------------

1.  Begin with a symbolic "skeleton"
2.  Use symbolic execution (aka "narrowing") over this skeleton
3.  Avoid uninteresting programs
4.  Concretize any remaining variables

## 1. Symbolic Skeleton

:::columns
::::column

* The user selects a symbolic skeleton.

* This skeleton allows us to guide the tool to target particular features 

* e.g. It is unlikely that 4 variables would be able to trigger many more bugs than 3

* The user may select multiple skeletons to target distinct areas of the language
 
::::

:::: {.column }
```
int x, y;
☐ = ☐:Exp;
☐:Stmt
☐:Stmt
```
::::
:::


## 2. Narrowing


:::columns
:::: {.column}

**Program State**

```
<k> ☐:Stmt ... </k>
<state> (x |-> 3) (y |-> 0) </state>
```

**Rules**

```
// Assignment
rule
  <k> X = I:Int; => . ... </k>
  <state> 
    ... X |-> (_ => I) ...
  </state>

// While
rule
  <k> while (B) S
   => if (B) {S while (B) S}
      else   {}
      ...
  </k>
```
::::

:::: {.column}
:::::{.fragment .fade-in}
**Results in**

```
<k> x = ☐:Stmt ... </k>
<state> (x |-> 3) (y |-> 0) </state>
```

```
<k> y = ☐:Stmt ... </k>
<state> (x |-> 3) (y |-> 0) </state>
```

```
<k> while (☐:Exp) ☐:Stmt
  ...
</k>
<state> (x |-> 3) (y |-> 0) </state>
```
:::::
::::
:::

## ⚠️️️  state-space explosion ⚠️

::: {.columns}
:::: {.column}
![](../../doc/narrowing-on-statements.png){  width=80% }
::::

:::: {.column}
:::::{.fragment .fade-in}

What about infinite loops?

```
<k> while (true) { ... }
  ...
</k>
```
:::::
::::
:::

## 3. Avoid uninteresting programs

* Limit the application of some rules
* Use instrumentation, so that we prune narrowing once a rule has been executed $n$ times on a path.

## 4. Concretization

Since only branches that were executed are narrowed, there are still remaining symbolic variables:

```k
  int x, y;
  x = 2;
  if ( false ) { ?S:Stmt }
  ...
```

We choose arbitary values for remaining variables:

```k
  int x, y;
  x = 2;
  if ( false ) { { } }
  ...
```

## Prototype Evaluation

* Generated 1988 programs in 10 minutes
* Programs cover 100% of the language semantics

### Caveats

* Some manual modifications needed for instrumentation; We should automate these
* Guidance heuristic is very simple, will probably not be good enough for more complex languages

### Next steps

* Port to other languages, and use as a source of tests for diffrential testing. Solidity? JavaScript?
* Performance: Currently, we run 𝕂 every time we take a step, this is expensive
* Better integration with the 𝕂

