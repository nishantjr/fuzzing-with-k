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

    configuration <k> fuzz(8, $PGM:Pattern) </k>
                  <out stream="stdout"> .List </out>
    
    syntax PrePattern ::= Pattern
    syntax KResult ::= Pattern 
    
    syntax PreString ::= String
    syntax KResult ::= String

    syntax KItem ::= fuzz(Int, PrePattern) [seqstrict(2)]
    rule <k> fuzz(N, \or{S}(P, Ps)) => fuzz(N, P) ~> fuzz(N, Ps) ... </k>
    rule <k> fuzz(N, P) => fuzz(N -Int 1, exec(P))           ... </k> requires N >Int 0 andBool \or{_}(_, _) :/=K P
    rule <k> fuzz(0, P) => print(pretty(P))         ... </k>

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
          => unparse(system("./meta-kore-exec .build/defn/imp-haskell/imp-kompiled/definition.kore --search search-pattern.kore --searchType FINAL --depth 1 --module IMP --pattern " +String Path))
             ...
         </k>

    syntax PrePattern ::= unparse(PreString) [seqstrict]
    rule <k> unparse(MetaKore) => #parseKORE(MetaKore):Pattern ... </k>

    syntax PreString ::= system(command: String)
    rule <k> system(Command) => #system(Command) ... </k>
    rule <k> #systemResult(0, StdOut, _) => StdOut ... </k>

    syntax PreString ::= pretty(Pattern)
    rule <k> pretty(Pattern)
          => write("tmp/pretty", unparsePattern(Pattern))
          ~> system("kprint .build/defn/imp-haskell/imp-kompiled/ tmp/pretty true true")
             ...
         </k>

    syntax KItem ::= print(PreString) [seqstrict]
    rule <k> print(S:String) => .K ... </k>
         <out> ... .List => ListItem(S) </out>
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
