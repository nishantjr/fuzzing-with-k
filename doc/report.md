---
title: Building a language-agnostic semantics-aware fuzzer
documentclass: acmart
classoption: sigconf
author:
  - name: Nishant Rodrigues
    email: nishant2@illinois.edu
  - name: Manasvi Saxena
    email: msaxena2@illinois.edu
frontmatter:
    \newcommand {\K} {$\mathbb{K}$}
    \newcommand{\cmark}{\ding{51}}
    \newcommand{\xmark}{\ding{55}}
abstract:
    Current state of the art fuzzers are either semantics-aware or language-specific.
    In this project, we prototype a fuzzer that is both semantics-aware and language-agnostic.
    This is done using the semantics-first approach, by taking advantage of K semantics for the languages.
---

Motivation
----------

Test case generation tools need to be aware of the semantics of the tools they
are targeting in order to generate programs the exercise "deep" paths. However,
their development is expensive and are only available for a few languages in
widespread usage. Language agnostic fuzzers alllowing testing many more
languages in the same tool reducing devlopment costs. Thus, most test case
generation tools are either language-agnostic or semantics-aware, but not both.

Most test case generation tools are either been: semantics-aware,
language specific, but can find semantically interesting bugs (e.g. jsfunfuzz, KLEE, Korat) or,
language agnostic, but semantics-unaware and only able to find "shallow" bugs (e.g. AFL, LangFuzz).

This is because of the way programming languages are traditionally developed.
A rough natural-language design or specification is written first.
This is used to guide the writing of a compiler or interpreter.
When other language tools are needed, the same process is repeated, treating the natural language document as the source of truth.
This kind of development goes against the traditionally software engineering principals such as DRY (don't repeat yourself).

The semantics-first approach to language development gives us insight into how this problem can be solved.
As prescribed by this approach, we will build a test
case generator that is parametric over the formal semantics of the language. We
intend to use the \K{} Framework as the basis of our work. This
framework allows defining programming languages semantics and deriving various
language tools (e.g. parsers, interpreters, deductive verifiers, symbolic
execution engines...) from them. Currently, \K{} does not support test
case generation. Our work will focus on adding a test case generator to
\K{} and evaluating it with existing \K{} definitions of
languages like the EVM and JavaScript.

\begin{figure}[h]
\includegraphics[width=0.45\textwidth]{k.png}
\caption{The ideal language framework}
\label{fig:ideal}
\end{figure}

The \K{} Framework is a language framework that takes such an approach. Several
large, real-world languages are already have semantics defined in \K{}, such as C,
Python, LLVM, Java, JavaScript, EVM and Solidity. The \K{} Framework is also
already able to derive a parser, interpreter, symbolic execution engine, model
checker and a deductive verifier from these semantics.

The \K{} Framework, however, does not yet derive a test case generator. This
project aims to remedy that situation by developing a test case generator parametric over the
input language that is both language-agnostic, and semantics-aware.

Background
----------

\K{} semantics consists of three parts:

1. the grammar of the language, described using `syntax` statements, in Figure \ref{fig:syntax}
2. the "`configuration`", a nested record like structure representing the state of the program,
   in Figure \ref{fig:configuration} and
3. the semantics of the language, described using a set of `rule`s as transitions from on state to the next,
   in Figure \ref{fig:semantics}.

\begin{figure}[h]
\footnotesize
\begin{minipage}{0.38\textwidth}
\begin{lstlisting}
syntax AExp
   ::= Int | Id
     | "-" Int
     | AExp "/" AExp  [strict]
     > AExp "+" AExp  [strict]
     | "(" AExp ")"   [bracket]
syntax BExp
   ::= Bool
     | AExp "<=" AExp [seqstrict]
     | "!" BExp       [strict]
     > BExp "&&" BExp [left, strict(1)]
     | "(" BExp ")"   [bracket]
\end{lstlisting}
\end{minipage}
\begin{minipage}{0.33\textwidth}
\begin{lstlisting}
syntax Block
   ::= "{" "}"
     | "{" Stmt "}"
syntax Stmt
   ::= Block
     | Id "=" AExp ";"
     | "if" "(" BExp ")"
       Block "else" Block
     | "while" "(" BExp ")" Block
     > Stmt Stmt

syntax Pgm ::= "int" Ids ";" Stmt
syntax Ids ::= List{Id,","}
\end{lstlisting}
\end{minipage}
\begin{minipage}{0.18\textwidth}
\begin{lstlisting}configuration
configuration
  <imp>
    <k> $PGM:Pgm </k>
    <state> .Map </state>
  </imp>
\end{lstlisting}
\end{minipage}\caption{The syntax and configuration of the IMP programming language}
\label{fig:syntax}
\label{fig:configuration}
\end{figure}

\begin{figure}[h]
\footnotesize
\begin{minipage}{0.33\textwidth}
\begin{lstlisting}
syntax KResult ::= Int | Bool

// Blocks and Statements
rule S1:Stmt S2:Stmt => S1 ~> S2
rule {} => .
rule {S} => S

// Control Structure
rule if (true)  S else _ => S
rule if (false) _ else S => S

rule while (B) S
  => if (B) {S while (B) S} else {}
\end{lstlisting}
\end{minipage}
\begin{minipage}{0.26\textwidth}
\begin{lstlisting}
// Arithmetic
rule I1 / I2 => I1 /Int I2
  requires I2 =/=Int 0
rule I1 + I2 => I1 +Int I2
rule - I1 => 0 -Int I1

rule I1 <= I2 => I1 <=Int I2
rule ! T => notBool T
rule true && B => B
rule false && _ => false
\end{lstlisting}
\end{minipage}
\begin{minipage}{0.31\textwidth}
\begin{lstlisting}
rule <k> int (X,Xs => Xs);_ </k>
     <state> Rho:Map (.Map => X|->0) </state>
  requires notBool (X in keys(Rho))
rule int .Ids; S => S
// variable lookup
rule <k> X:Id => I ...</k>
     <state>... X |-> I ...</state>
// Assignment
rule <k> X = I:Int; => . ...</k>
     <state>... X |-> (_ => I) ...</state>
\end{lstlisting}
\end{minipage}
\caption{The semantics and configuration of the IMP programming language}
\label{fig:semantics}
\end{figure}

Our solution
------------

In this project (<https://github.com/nishantjr/fuzzing-with-k/>), we leverage \K{} to perform semantics-based fuzzing.
Our method of fuzzing can be viewed as an extension simultanuously of grammar-based fuzzing and
of skeleton-based fuzzing.
Our tool will take advantage of \K{}'s symbolic execution engine.
This symbolic engine is much more general than traditional language specific engines.
Most symbolic exection engines are restricted to executing programs where particular variables are assigned symbolic values.
\K{}, however, being a language framework, has no distinction
between program values, such as integers, strings, objects, etc
and program constructs such as statements, conditionals, and while loops.
This means that we may execute a **symbolic program**, i.e. one where parts of the program themselves are symbolic.

We feed as input to our tool, a program skeleton with certain positions in the AST holding symbolic variables.
These symbolic variables may be instantiated not just by values, but also by statements, class and function declarations
etc. For example, when prototyping our technique against the IMP programming language above, we used the following symbolic program
as input:

```
  int x, y;
  ?V:Id = ?I:Int;
  ?T1:Stmt
  ?T2:Stmt
```

In this skeleton, we have a program with two variables `x` and `y`, an
assignment statement, followed by two arbitary statements.
The \K{} symbolic engine first adds the `x` and `y` variables to the environment.

\begin{figure}[h]
\includegraphics[width=0.45\textwidth]{narrowing-on-statements.png}
\caption{Narrowing on a symbolic program}
\label{fig:ideal}
\end{figure}

It then encounters a symbolic statement. \K{} *narrows* (rewrites over symbolic terms) on that statement,
chosing each possible case instantiation of the symbolic variable. For example, \K{} a symbolic statement
may narrow into each of an assignment, an if statement, a while loop and so on.
Each of the parameters that these constucts take may then be further narrowed on.
For example, the left hand side of an assignment may narrow into various identifiers,
and the right hand side into various expressions.
Importantly, since the narrowing is driven by the semantic rules for the language,
only semantically interesting programs are generated.
For example, only declared variables are chosen for both the right and the left hand side of the
assignemnt statement. Magic numbers used in the semantics (e.g. if division by zero is a special case in the semantics)
are also found and exploited.

Simply enumerating as many programs as possible with this method is not viable however, since the search space
is unbounded. Further, we may spend a lot of time repeatedly exercising the same areas
of the semantics, for example, by generating deeply nested but uninteresting expressions on the right hand side
of the assignement in the first statement, without proceeding to the next one.
It is also easy to generate programs that loop forever. We must guide this search for it to be useful.
We do so using a simple coverage metric -- we stop symbolic execution once a program has executed any
rule from a particular set a certain number of times. Besides guiding the semantics, this also
deals with non-terminating programs by dissallowing the rule for while loops executing too many times.

At this point, we are left with a program that, while more fleshed out than the original skeleton, still has some symbolic "holes" in it.
For example, since only branches that were executed are narrowed, there are still remaining symbolic variables.

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

resulting in a concrete program that may be executed by any interpreter for that language.

Evaluation
----------

We evaluated our prototype by generating programs for the IMP programing language.
Using the skeleton above, we generated 1988 programs in under 10 minutes.
These programs have 100% coverage: they execute every semantic rule in the definition.

Next Steps & Future Work
------------------------

Turing our current prototype into a full fledged tool requires additional work, enumerated in this section.

### Efficiency

This prototype was developed to provide a demonstration of semantics based fuzzing.
However, for fuzzing the effectiveness of a tool directly relates to is efficiency
-- the more quickly one can generate programs, the more quickly one may find bugs.
We currently call into \K{}'s symbolic backend each time it needs to take a single execution step using the backend.
This means that each time we take a step, the backend needs to parse and load the semantics, take a step and unparse the configuration
and the fuzzer needs to parse the output produced. 
This is very inefficient.
In the future, we may implement the fuzzer as an "execution strategy" within the symbolic backend, to save on these round trip costs.

Another option is to avoid \K{}'s symbolic backend as much as possible.
\K{}'s symbolic backend is intended for formal reasoning about programs.
In particular, it is intended to eventually produce formal proofs about a programs possible executions.
This is quite an overkill for fuzzing.
Fortunately, \K{} provides a second backend -- one aimed a fast execution of concrete programs (i.e. programs without symbolic variables).
This backend translates \K{} definitions into native code using the LLVM compiler infrastructure.
However, our tool depends on symbolic variables to represent parts of the program state that may to be fuzzed.
This may be worked around by "skolemnizing" them -- we may generate new language syntax that allows symbolic variables to be treated as "uninterpreted" language constructs.
By "uninterpreted" we mean that there are no semantic rules defined over them,
and when program execution needs to "inspect" their values to continue execution, it gets stuck.
We may then convert these constants back into symbolic variables, execute the rule that needs to inspect the symbolic variable, and then pass the output
configuration back to the concerte backend.

### User interface & tooling

For this fuzzer to be useful, it must be convenient to use.
There are a number of improvements that need to be made for this.

Currently, the initial program state must be written in "Kore" -- an internal language used by various \K{} tools to communicate.
Ideally, we would be able to write this intial state directly using the
programming language's syntax, or \K{}'s syntax for writing semantic rules.

In its current incarnation, the prototype also requires manaul changes to the language semantics to provide instrumentation.
This step can be automated, so that we can use any existing language definition unchanged.

While conceptually simple, these are important changes that need to be made to the tooling for this fuzzer to be useful to a general audience.

### Imporve concretization procedure

Currently, during the concretization process, we simple chose a value hard coded value for each sort.
For example, we always chose "2" for any symbolic integer remaining in the program.
We completely ignore the constraints that \K{} has generated.
We should instead use an SMT solver to generate a number of values that satisfy the path condition for that state.

### Improve coverage metric

Our current coverage guidance is quite simple -- we stop executing on branches where a rule has been executed a certain number of times.
This may suffice in a simple language like K, however, this may still be a massive search space for more complex langauges.
A more interesting heuristic may prefer programs that exercise rules that haven't been seen before, or even orderings of rules that haven't been seen.

