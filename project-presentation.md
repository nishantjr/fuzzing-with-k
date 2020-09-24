---
title: Building language-agnostic semantics-aware Fuzzing tools
---



Building language-agnostic semantics-aware Fuzzing tools
========================================================

Motivation
----------

- Broad classifications of *Fuzzing Techniques*:
  * **Language Specific** - *Implicitly* leverage semantics to boost
    performance at the expense of modularity. Example *JSFunFuzz* (JavaScript)

  * **Language Agnostic** - Offer modularity at the expense of performance.
    Example *LangFuzz* (JavaScript, PHP)

- Leads to *duplication of work*. Core idea constant across multiple
  langauges.


> - Develop a **Language Agnostic Tool** that *leverages semantics* to offer both **performance** and **modularity**
  - Extend existing work on **Semantics First Approach**


Semantics First Approach
------------------------

::: columns

:::: column

1. Define a formal semantics for your language
2. Derive each tool you care about from this semantics
3. Profit. *Core* ideas instantiated with the semantics reduce duplication


::::

:::: column

DIAGRAM OF SEMANTICS FIRST

::::

:::

The K Framework
---------------

K is a framework for formally specifying languages using the semantics-first approach.


::: columns

:::: column

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

:::: column

Several tools can already be derived:

* Parser
* Interpreter
* Model Checker
* Deductive Verifier
* Equivalence checker

::::: incremental
* <mark> Fuzzer? </mark>
:::::

::::

:::

What do K semantics look like?
------------------------------

:::columns

:::: column


```k
syntax AExp  ::= Int | Id
               | "-" Int
               | AExp "/" AExp              [left, strict]
               > AExp "+" AExp              [left, strict]
               | "(" AExp ")"               [bracket]
syntax BExp  ::= Bool
               | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
               | "!" BExp                   [strict]
               > BExp "&&" BExp             [left, strict(1)]
               | "(" BExp ")"               [bracket]
syntax Block ::= "{" "}"
               | "{" Stmt "}"
syntax Stmt  ::= Block
               | Id "=" AExp ";"            [strict(2)]
               | "if" "(" BExp ")"
                 Block "else" Block         [strict(1)]
               | "while" "(" BExp ")" Block
               > Stmt Stmt                  [left]
syntax Pgm ::= "int" Ids ";" Stmt
syntax Ids ::= List{Id,","}
```

```k
configuration <T color="yellow">
                <k color="green"> $PGM:Pgm </k>
                <state color="red"> .Map </state>
              </T>
```

::::

:::: column


```k
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


Milestones
----------

Goals:

1. [Engineering] Grammar based generation
2. [Engineering] Use coverage information for feedback
3. [Research]    Use typing semantics (for typed languages) to synthesize
                 input with interesting use of types
4. [Research]    Combine symbolic execution with instrumentation to generate tests?



Evaluation
----------

1. Start with a simple language with existing K semantics
2. Currently considering EVM, JavaScript
3. Evaluate against existing tools for language




