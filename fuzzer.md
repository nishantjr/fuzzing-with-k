```k
requires "substitution.md"
```

```k
module KORE
    imports STRING-SYNTAX
    imports KVAR-SYNTAX

    syntax KVar ::= r"[A-Za-z'-][A-Za-z'0-9-]*" [token]
    syntax Sort ::= KVar "{" "}"
    syntax Symbol ::= KVar "{" Sorts "}"
    syntax Pattern ::= "\\dv" "{" Sort "}" "(" String ")"                           [klabel(\dv)]
                     | KVar ":" Sort                                                [klabel(variable)]
                     | Symbol "(" Patterns ")"                                      [klabel(application)]
                     | "\\not" "{" Sort "}" "(" Pattern ")"                         [klabel(\not)]
                     | "inj" "{" Sort "," Sort "}" "(" Pattern ")"                  [klabel(inj)]
                     | "\\equals" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")" [klabel(\equals)]
                     | "\\and" "{" Sort "}" "(" Pattern "," Pattern ")"             [klabel(\and)]
                     | "\\or" "{" Sort "}" "(" Pattern "," Pattern ")"              [klabel(\or)]
                     | "\\top" "{" Sort "}" "(" ")"                                 [klabel(\top)]
                     | "\\bottom" "{" Sort "}" "(" ")"                              [klabel(\bottom)]
                     | "\\forall" "{" Sort "}" "(" Pattern "," Pattern ")"          [klabel(\forall)]
                     | "\\exists" "{" Sort "}" "(" Pattern "," Pattern ")"          [klabel(\exists)]

    syntax Patterns ::= List{Pattern, ","} [klabel(Patterns)]
    syntax Sorts ::= List{Sort, ","}       [klabel(Sorts)]
endmodule
```

```k
module KORE-UNPARSE
    imports KORE
    imports STRING

    syntax String ::= unparsePattern(Pattern) [function, functional]
    rule unparsePattern(\equals { S1 , S2 } (P1, P2)) => "\\equals{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"
    rule unparsePattern(KVar : Sort)                  => NameToString(KVar) +String ":" +String unparseSort(Sort)
    rule unparsePattern(\dv { S } (Value))            => "\\dv{" +String unparseSort(S)  +String "} (\"" +String Value +String "\")"
    rule unparsePattern(\top { S } ())                => "\\top{" +String unparseSort(S)  +String "} ()"
    rule unparsePattern(\bottom { S } ())                => "\\bottom{" +String unparseSort(S)  +String "} ()"
    rule unparsePattern(inj { S1 , S2 } (P1))         => "inj{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(\not { S1 } (P1))         => "\\not{" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(S(Args:Patterns))             => unparseSymbol(S) +String "(" +String unparsePatterns(Args) +String ")"
    rule unparsePattern(\and { S1 } (P1, P2))
      => "\\and{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"
    rule unparsePattern(\or { S1 } (P1, P2))
      => "\\or{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"
    rule unparsePattern(\forall  { S1 } (P1, P2)) => "\\forall {" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"
    rule unparsePattern(\exists  { S1 } (P1, P2)) => "\\exists {" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"

    syntax String ::= NameToString(KVar) [function, functional, hook(STRING.token2string)]

    syntax String ::= unparseSort(Sort) [function, functional]
    rule unparseSort(KVar {}) => NameToString(KVar) +String "{}"

    syntax String ::= unparseSymbol(Symbol) [function, functional]
    rule unparseSymbol(KVar {Sorts}) => NameToString(KVar) +String "{" +String unparseSorts(Sorts) +String "}"

    syntax String ::= unparsePatterns(Patterns) [function, functional]
    rule unparsePatterns(P, Ps) => unparsePattern(P) +String "," +String unparsePatterns(Ps) requires notBool Ps ==K .Patterns
    rule unparsePatterns(P, .Patterns) => unparsePattern(P)
    rule unparsePatterns(.Patterns) => ""

    syntax String ::= unparseSorts(Sorts) [function, functional]
    rule unparseSorts(S, Ss) => unparseSort(S) +String "," +String unparseSorts(Ss) requires notBool Ss ==K .Sorts
    rule unparseSorts(S, .Sorts) => unparseSort(S)
    rule unparseSorts(.Sorts) => ""
endmodule
```

```k
module FUZZER
    imports INT
    imports KORE
    imports KORE-UNPARSE
    imports K-IO
    imports K-REFLECTION
    imports MAP

    configuration <k> fuzz($MaxDepth, $PGM:Pattern) </k>
                  <ruleLimit> $RuleLimit </ruleLimit>

    syntax PrePattern ::= Pattern
    syntax KResult ::= Pattern

    syntax PreString ::= String
    syntax KResult ::= String

    syntax KItem ::= fuzz(Int, PrePattern) [seqstrict(2)]
    rule <k> fuzz(N, P) => choose(N -Int 1, exec(P)) ... </k> requires N >Int 0 andBool \or{_}(_, _) :/=K P
    rule <k> fuzz(0, P) => finalize(P) ... </k>

    syntax PrePattern ::= exec(Pattern)
    rule <k> exec(Pattern)
          => write("tmp/step.kore", unparsePattern(Pattern)) ~> kore-exec("tmp/step.kore")
             ...
         </k>

    syntax KItem ::= write(filename: String, content: String)
                   | write(fd: IOInt, content: String)
                   | close(Int)
    rule <k> write(Filename, Content) => write(#open(Filename, "w"), Content)  ... </k>
    rule <k> write(Fd, Content)       => #write(Fd, Content) ~> close(Fd) ... </k>
    rule <k> close(Fd) => #close(Fd) ... </k>

    syntax KItem ::= "kore-exec" "(" path: String ")"
    rule <k> kore-exec(Path)
          => parse(system("./meta-kore-exec .build/defn/imp-haskell/imp-kompiled/definition.kore --search search-pattern.kore --searchType FINAL --depth 1 --module IMP --pattern " +String Path))
             ...
         </k>

    syntax KItem ::= finalize(Pattern) [seqstrict]
    rule <k> finalize(\or{_}(P1, P2)) => finalize(P1) ~> finalize(P2) ... </k>
    rule <k> finalize(P) => print(unparse(getProgram(concretize(P)))) ... </k> requires \or{_}(_, _) :/=K P

    syntax PrePattern ::= choose(depth: Int, PrePattern) [seqstrict(2)]
    rule <k> choose(N, \or{_}(P1, P2)) => choose(N, P1) ~> choose(N, P2) ... </k>
    rule <k> choose(N,  P) => fuzz(N, P)  ... </k> requires \or{_}(_, _) :/=K P andBool withinRuleLimits(P)
    rule <k> choose(_N, P) => finalize(P) ... </k> requires \or{_}(_, _) :/=K P andBool notBool withinRuleLimits(P)

    syntax PreString ::= unparse(PrePattern) [seqstrict]
    rule <k> unparse(P) => unparsePattern(P) ... </k>

    syntax PrePattern ::= parse(PreString) [seqstrict]
    rule <k> parse(MetaKore) => #parseKORE(MetaKore):Pattern ... </k>

    syntax PreString ::= system(command: String)
    rule <k> system(Command) => #system(Command) ... </k>
    rule <k> #systemResult(0, StdOut, _) => StdOut ... </k>

    syntax KItem ::= print(PreString) [seqstrict]
    rule <k> print(S:String)
          => write("tmp/out/" +String Int2String(!I) +String ".kore", S)
             ...
         </k>
```

Given a Pre Pattern with variables, convert to
a pattern where variables are replaced by concrete values

```k
    syntax PrePattern ::= concretize(Pattern)
    rule <k> concretize(P) => first(concretizePattern(P)) ... </k>

    syntax Patterns ::= concretizePatterns(Patterns) [function]
    rule concretizePatterns(P, Ps) => concretizePattern(P) +Patterns concretizePatterns(Ps)
    rule concretizePatterns(.Patterns) => .Patterns

    syntax KVar ::= "Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids" [token]
                  | "Lbl'Stop'List'LBraQuotUndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids'QuotRBraUnds'Ids" [token]
                  | "SortId" [token]
                  | "SortInt" [token]
                  | "SortBool" [token]
                  | "SortBlock" [token]
                  | "SortStmt" [token]
                  | "SortAExp" [token]
                  | "SortBExp" [token]
                  | "Lblnoop" [token]

    syntax Pattern ::= first(Patterns) [function]
    rule first(P, Ps) => P

    syntax Patterns ::= concretizePattern(Pattern)   [function]
    rule concretizePattern(Symbol{Sorts}(Patterns)) => Symbol{Sorts}(concretizePatterns(Patterns))
    rule concretizePattern(\and{S}(P1, P2)) => concretizePattern(P1) +Patterns concretizePattern(P2)
    rule concretizePattern(\equals{S1, S2}(P1, P2)) => .Patterns
    rule concretizePattern(\not{S}(P)) => .Patterns
    rule concretizePattern((\dv{_}(_)) #as Dv::Pattern) => Dv
    rule concretizePattern((\top{_}()) #as Top::Pattern) => .Patterns
    rule concretizePattern((\bottom{_}()) #as Bot::Pattern) => .Patterns
    rule concretizePattern(inj{S1, S2}(P)) => inj{S1, S2}(first(concretizePattern(P)))
    rule concretizePattern(_ : SortId{}) => \dv{SortId{}}("x")
    rule concretizePattern(_ : SortInt{}) => \dv{SortInt{}}("2")
    rule concretizePattern(V : SortAExp{}) => inj{SortInt{}, SortAExp{}}(first(concretizePattern(V : SortInt{})))
    rule concretizePattern(_ : SortBool{}) => \dv{SortBool{}}("false")
    rule concretizePattern(V : SortBExp{}) => inj{SortBool{}, SortBExp{}}(first(concretizePattern(V : SortBool{})))
    rule concretizePattern(_ : SortBlock{}) => Lblnoop{.Sorts}(.Patterns) 
    rule concretizePattern(V : SortStmt{}) => inj{SortBlock{}, SortStmt{}}(first(concretizePattern(V : SortBlock{})))
```

Extract the program cell from the configuration pattern

```k
    syntax PrePattern ::= getProgram(PrePattern) [seqstrict]
    rule <k> getProgram(Lbl'-LT-'generatedTop'-GT-'{.Sorts}(_,_ {.Sorts }(P, .Patterns),_:Patterns)) => first(kseqToPatterns(P)) ... </k>
```

Checks if a rule has been exercised more than `<ruleLimit>` times.

```k
    syntax Bool ::= withinRuleLimits(Pattern) [function]
    rule withinRuleLimits(P) => withinRuleLimits(getRuleInstrumentation(P), .Map)

    syntax Bool ::= withinRuleLimits(Patterns, Map) [function]
    rule withinRuleLimits((R, Rs),                  M)
      => withinRuleLimits((R, Rs), (R |-> 0)        M) requires notBool R in_keys(M)
    rule [[ withinRuleLimits((R, Rs), (R |-> N)        M)
         => withinRuleLimits(    Rs , (R |-> N +Int 1) M)
         ]] 
         <ruleLimit> RuleLimit </ruleLimit>
      requires N <Int RuleLimit
    rule [[ withinRuleLimits((R,_Rs), (R |-> RuleLimit) _M) => false ]]
         <ruleLimit> RuleLimit </ruleLimit>
    rule withinRuleLimits(.Patterns, _) => true

    syntax KVar ::= "Lbl'-LT-'generatedTop'-GT-'" [token]
    syntax KVar ::= "Lbl'-LT-'ruleInstrumentation'-GT-'" [token]
    syntax Patterns ::= getRuleInstrumentation(Pattern) [function]
    rule getRuleInstrumentation(\and{_}(P1, P2)) => getRuleInstrumentation(P1) +Patterns getRuleInstrumentation(P2)
    rule getRuleInstrumentation(Lbl'-LT-'generatedTop'-GT-'{.Sorts}(_, _, _, Lbl'-LT-'ruleInstrumentation'-GT-'{.Sorts}(KSeq)))
      => kseqToPatterns(KSeq)
    rule getRuleInstrumentation(\equals{_, _}(_, _)) => .Patterns
    rule getRuleInstrumentation(\not{_}(_))          => .Patterns

    syntax Patterns ::= kseqToPatterns(Pattern) [function]
    rule kseqToPatterns(dotk{.Sorts}(.Patterns)) => .Patterns
    rule kseqToPatterns(kseq{.Sorts}(P, Ps)) => P, kseqToPatterns(Ps)

    syntax Patterns ::= Patterns "+Patterns" Patterns [function]
    rule (P1, P1s) +Patterns P2s => P1, (P1s +Patterns P2s)
    rule .Patterns +Patterns P2s => P2s
```

TODO: remove once `--strategy all` is available

```k
    syntax KVar ::= "VarResult" [token]
                  | "SortGeneratedTopCell" [token]
                  | "dotk" [token]
                  | "kseq" [token]
    rule \equals { _, _ } ( VarResult : SortGeneratedTopCell {} , Result ) => Result [anywhere]
```

```k
endmodule
```
