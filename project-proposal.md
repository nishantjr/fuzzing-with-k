---
title: Building language-agnostic semantics-aware test case generation
author:
  - Nishant Rodrigues
  - Manasvi Saxena
---

Abstract
--------

Test case generation tools need to be aware of the semantics of the tools they
are targeting in order to generate programs the exercise "deep" paths. However,
their development is expensive. Thus, most test case generation tools are either
language-agnostic or semantics-aware but not both. The semantics-first approach
to language development gives us hope for solving this problem.

Motivation
----------

The Fuzzing tools we have seen so far, have either been:

1.  Semantics-aware, language specific, but can find "deep" bugs

    e.g. jsfunfuzz, KLEE, Korat

2.  Language Agnostic, but semantics-unaware and can only find "shallow" bugs

    e.g. AFL, LangFuzz

This is because of the way programming languages are traditionally developed --
A rough natural language design or specification is written This is used to
guide the writing of a compiler or interpreter. When other language tools are
needed, the same process is repeated, treating the natural language document as
the source of truth. This kind of development goes against the traditionally
software engineering goals we strive for such as DRY (don't repeat yourself).

Fortunately, there is an alternative. The semantics-first school of thought
prescribes first writing a *formal specification* of the language's semantics,
and then using this specification as the source of truth. First, we define a
formal semantics for your language. Then, from that formal semantics, we derive
the various tool we need, such as parsers, compilers, interpreters, deduction
engines and fuzzers.

![](../k.png){width="100%"}

The K Framework is a language framework that takes such an approach. Several
large, real-world languages are already have semantics defined in K, such as C,
Python, LLVM, Java, JavaScript, EVM and Solidity. The K Framework is also
already able to derive a parser, interpreter, symbolic execution engine, model
checker and a deductive verifier from these semantics.

The K Framework, however, does not yet derive a test case generator. This
project aims to remedy that situation by developing a fuzzer parametric over the
input language that is both language-agnostic, and semantics-aware.

Proposal & Milestones
---------------------

1. [Engineering] Grammar based generation
2. [Engineering] Use coverage information for feedback
3. [Research]    Can we generate instrumentation in a language agnostic fashion?
3. [Research]    Can we use the typing semantics of language to generate more interesting tests?
4. [Research]    Can we combine symbolic execution with instrumentation in interesting ways?

Evaluation
----------

1. Compare code coverage found using our tool with languages that already have fuzzers
2. Try our fuzzer on a variety of languages: imperative, stack-based, functional

