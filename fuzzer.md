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
                     | "\\ceil" "{" Sort "," Sort "}" "(" Pattern ")"               [klabel(\ceil)]

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
    rule unparsePattern(\ceil { S1 , S2 } (P1)) => "\\ceil{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String ")"
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

`KORE-UTILITIES`
==============

Various generic library functions over kore.

```k
module KORE-UTILITIES
    imports KORE
    imports K-EQUAL

    syntax Pattern ::= first(Patterns) [function]
 // ---------------------------------------------
    rule first(P, _) => P

    syntax Patterns ::= getArgs(Pattern) [function]
 // -----------------------------------------------
    rule getArgs(Ctor { .Sorts } ( Args )) => Args

    syntax Patterns ::= Patterns "+Patterns" Patterns [function, functional, left]
 // ------------------------------------------------------------------------------
    rule (P1, P1s) +Patterns P2s => P1, (P1s +Patterns P2s)
    rule .Patterns +Patterns P2s =>                    P2s

    syntax Patterns ::= kseqToPatterns(Pattern) [function]
 // ------------------------------------------------------
    rule kseqToPatterns(dotk{.Sorts}(.Patterns)) => .Patterns
    rule kseqToPatterns(kseq{.Sorts}(P, Ps)) => P, kseqToPatterns(Ps)
    syntax KVar ::= "dotk" [token] | "kseq" [token]

    syntax Patterns ::= findSubTermsByConstructor(KVar, Pattern) [function, functional]
 // -----------------------------------------------------------------------------------
    rule findSubTermsByConstructor(Ctor, Ctor { .Sorts } ( _ ) #as P  ) => P, .Patterns

    rule findSubTermsByConstructor(Ctor, S { _ } ( Args ) )     => findSubTermsByConstructorPs(Ctor, Args) requires S =/=K Ctor
    rule findSubTermsByConstructor(Ctor, inj{ _, _ } (P) )      => findSubTermsByConstructor(Ctor, P)
    rule findSubTermsByConstructor(Ctor, \not{ _ } (P) )        => findSubTermsByConstructor(Ctor, P)
    rule findSubTermsByConstructor(Ctor, \and{ _ } (P1, P2) )   => findSubTermsByConstructor(Ctor, P1) +Patterns findSubTermsByConstructor(Ctor, P2)
    rule findSubTermsByConstructor(Ctor, \or{ _ } (P1, P2) )    => findSubTermsByConstructor(Ctor, P1) +Patterns findSubTermsByConstructor(Ctor, P2)

    rule findSubTermsByConstructor(_ , \bottom{ _ } () )        => .Patterns
    rule findSubTermsByConstructor(_ , \top{ _ } () )           => .Patterns
    rule findSubTermsByConstructor(_ , \dv{ _ } (_) )           => .Patterns
    rule findSubTermsByConstructor(_ , \forall{ _} (_, _) )     => .Patterns
    rule findSubTermsByConstructor(_ , \exists{ _} (_, _) )     => .Patterns
    rule findSubTermsByConstructor(_ , \ceil{ _, _ } (_) )      => .Patterns
    rule findSubTermsByConstructor(_ , \equals{ _, _ } (_, _) ) => .Patterns
    rule findSubTermsByConstructor(_ , _ : _)                   => .Patterns

    syntax Patterns ::= findSubTermsByConstructorPs(KVar, Patterns) [function, functional]
 // --------------------------------------------------------------------------------------
    rule findSubTermsByConstructorPs(Ctor, P, Ps) => findSubTermsByConstructor(Ctor, P) +Patterns findSubTermsByConstructorPs(Ctor, Ps)
    rule findSubTermsByConstructorPs(   _, .Patterns) => .Patterns
endmodule
```

`FUZZER`
========

```k
module FUZZER
    imports INT
    imports KORE
    imports KORE-UNPARSE
    imports K-IO
    imports K-REFLECTION
    imports MAP
    imports KORE-UTILITIES

    configuration <k> fuzz($MaxDepth, $PGM:Pattern) </k>
                  <ruleLimit> $RuleLimit </ruleLimit>
                  <mainModule> $MainModule:String </mainModule>
                  <kompiledDir> $KompiledDirectory:String </kompiledDir>
                  <outputDir>   $OutputDirectory:String </outputDir>

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
          => parse(system("./meta-kore-exec " +String KompiledDirectory +String "/definition.kore --strategy all --depth 1 --module " +String MainModule +String " --pattern " +String Path))
             ...
         </k>
         <kompiledDir> KompiledDirectory </kompiledDir>
         <mainModule> MainModule </mainModule>

    syntax KItem ::= finalize(Pattern) [seqstrict]
    rule <k> finalize(\or{_}(P1, P2)) => finalize(P1) ~> finalize(P2) ... </k>
    rule <k> finalize(P) => print(unparse(concretize(getProgramPrePattern(P)))) ... </k> requires \or{_}(_, _) :/=K P

    syntax PrePattern ::= choose(depth: Int, PrePattern) [seqstrict(2)]
    rule <k> choose( N, \or{_}(P1, P2)) => choose(N, P1) ~> choose(N, P2) ... </k>
    rule <k> choose(_N, P) => .K          ... </k> requires \or{_}(_, _) :/=K P andBool usesForbiddedConstructors(first(getProgram(P)))
    rule <k> choose( N, P) => fuzz(N, P)  ... </k> requires \or{_}(_, _) :/=K P andBool (notBool usesForbiddedConstructors(first(getProgram(P)))) andBool withinRuleLimits(P)
    rule <k> choose(_N, P) => finalize(P) ... </k> requires \or{_}(_, _) :/=K P andBool (notBool usesForbiddedConstructors(first(getProgram(P)))) andBool (notBool withinRuleLimits(P))

    syntax PreString ::= unparse(PrePattern) [seqstrict]
    rule <k> unparse(P) => unparsePattern(P) ... </k>

    syntax PrePattern ::= parse(PreString) [seqstrict]
    rule <k> parse(MetaKore) => #parseKORE(MetaKore):Pattern ... </k>

    syntax PreString ::= system(command: String)
    rule <k> system(Command) => #system(Command) ... </k>
    rule <k> #systemResult(0, StdOut, _) => StdOut ... </k>

    syntax KItem ::= print(PreString) [seqstrict]
    rule <k> print(S:String)
          => write(OutputDirectory +String "/" +String Int2String(!_I) +String ".kore", S)
             ...
         </k>
         <outputDir> OutputDirectory </outputDir>
```

Given a Pre Pattern with variables, convert to
a pattern where variables are replaced by concrete values

```k
    syntax PrePattern ::= concretize(PrePattern) [strict]
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
                  | "SortData" [token]
                  | "SortSimpleData" [token]
                  | "SortInstruction" [token]
                  | "SortDataList" [token]
                  | "SortTypeName" [token]
                  | "SortMaybeTypeName" [token]
                  | "SortNullaryTypeName" [token]
                  | "SortEmptyBlock" [token]
                  | "SortInternalList" [token]
                  | "Lblnoop" [token]
                  | "LblemptyBlock" [token]
                  | "LbltypeNameUnit" [token]
                  | "Lbl'Stop'List'LBraQuot'InternalList'QuotRBraUnds'InternalList" [token]
                  | "LblUnit" [token]
                  | "Lbl'Stop'Map" [token]
                  | "SortMap" [token]
                  | "SortStack" [token]
                  | "SortInternalStack" [token]
                  | "SortAnnotationList" [token]
                  | "Lbl'Stop'List'LBraQuotUndsSClnUndsUnds'MICHELSON-COMMON'Unds'Stack'Unds'StackElement'Unds'Stack'QuotRBraUnds'Stack" [token]
                  | "Lbl'Stop'List'LBraQuotUndsUndsUnds'MICHELSON-COMMON-SYNTAX'Unds'AnnotationList'Unds'Annotation'Unds'AnnotationList'QuotRBraUnds'AnnotationList" [token]
                  | "SortBlockList" [token]
                  | "Lbl'Stop'List'LBraQuotUndsSClnUndsUnds'MICHELSON-INTERNAL-SYNTAX'Unds'BlockList'Unds'Block'Unds'BlockList'QuotRBraUnds'BlockList" [token]
                  | "SortOutputStack" [token]

    syntax Patterns ::= concretizePattern(Pattern)   [function]
    rule concretizePattern(Symbol{Sorts}(Patterns)) => Symbol{Sorts}(concretizePatterns(Patterns))
    rule concretizePattern(\and{_S}(P1, P2)) => concretizePattern(P1) +Patterns concretizePattern(P2)
    rule concretizePattern(\equals{_S1, _S2}(_P1, _P2)) => .Patterns
    rule concretizePattern(\ceil{_S1, _S2}(_P1)) => .Patterns
    rule concretizePattern(\not{_S}(_P)) => .Patterns
    rule concretizePattern((\dv{_}(_)) #as Dv::Pattern) => Dv
    rule concretizePattern((\top{_}()) #as _::Pattern) => .Patterns
    rule concretizePattern((\bottom{_}()) #as _::Pattern) => .Patterns
    rule concretizePattern(inj{S1, S2}(P)) => inj{S1, S2}(first(concretizePattern(P)))

    // General
    rule concretizePattern(_ : SortId{}) => \dv{SortId{}}("x")
    rule concretizePattern(_ : SortInt{}) => \dv{SortInt{}}("2")
    rule concretizePattern(_ : SortBool{}) => \dv{SortBool{}}("false")

    // Imp
    rule concretizePattern(V : SortAExp{}) => inj{SortInt{}, SortAExp{}}(first(concretizePattern(V : SortInt{})))
    rule concretizePattern(V : SortBExp{}) => inj{SortBool{}, SortBExp{}}(first(concretizePattern(V : SortBool{})))
    rule concretizePattern(_ : SortBlock{}) => Lblnoop{.Sorts}(.Patterns)
    rule concretizePattern(V : SortStmt{}) => inj{SortBlock{}, SortStmt{}}(first(concretizePattern(V : SortBlock{})))

    // Michelson
    rule concretizePattern(_ : SortInstruction{})   => inj{SortEmptyBlock{}, SortInstruction{}}(LblemptyBlock{.Sorts}(.Patterns))
    rule concretizePattern(_ : SortDataList{})      => inj{SortEmptyBlock{}, SortDataList{}   }(LblemptyBlock{.Sorts}(.Patterns))

    rule concretizePattern(_ : SortInternalList{})  => Lbl'Stop'List'LBraQuot'InternalList'QuotRBraUnds'InternalList{.Sorts}(.Patterns)
    rule concretizePattern(_ : SortAnnotationList{})=> Lbl'Stop'List'LBraQuotUndsUndsUnds'MICHELSON-COMMON-SYNTAX'Unds'AnnotationList'Unds'Annotation'Unds'AnnotationList'QuotRBraUnds'AnnotationList{.Sorts}(.Patterns)
    rule concretizePattern(_ : SortBlockList{}) => Lbl'Stop'List'LBraQuotUndsSClnUndsUnds'MICHELSON-INTERNAL-SYNTAX'Unds'BlockList'Unds'Block'Unds'BlockList'QuotRBraUnds'BlockList{.Sorts}(.Patterns)

    rule concretizePattern(_ : SortInternalStack{}) => inj{SortStack{}, SortInternalStack{}}(Lbl'Stop'List'LBraQuotUndsSClnUndsUnds'MICHELSON-COMMON'Unds'Stack'Unds'StackElement'Unds'Stack'QuotRBraUnds'Stack{.Sorts}(.Patterns))

    rule concretizePattern(_ : SortData{})          => inj{SortSimpleData{}, SortData{}}(LblUnit{.Sorts}(.Patterns))
    rule concretizePattern(_ : SortTypeName{})      => inj{SortNullaryTypeName{}, SortTypeName{}}(LbltypeNameUnit{.Sorts}(.Patterns))
    rule concretizePattern(_ : SortMaybeTypeName{}) => inj{SortNullaryTypeName{}, SortMaybeTypeName{}}(LbltypeNameUnit{.Sorts}(.Patterns))

    rule concretizePattern(_ : SortMap{}) => Lbl'Stop'Map{.Sorts}(.Patterns)

    rule concretizePattern(_ : SortOutputStack{}) => Lbl'Stop'Map{.Sorts}(.Patterns)
```

Extract the program cell from the configuration pattern

```k
    syntax PrePattern ::= getProgramPrePattern(PrePattern) [seqstrict]
    rule <k> getProgramPrePattern(P) => getProgram(P) ... </k>

    syntax Pattern ::= getProgram(Pattern) [function]
    rule getProgram(P) => first(getArgs(first(findSubTermsByConstructor(Lbl'-LT-'pgm'-GT-', P))))
    syntax KVar ::= "Lbl'-LT-'pgm'-GT-'" [token]
```

Checks if the program uses forbidden constructors:

TODO: Ideally, we want this to dissallow anything outside the SYNTAX module

```k
    syntax Bool ::= usesForbiddedConstructors(Pattern) [function]
    rule usesForbiddedConstructors(Ctor { .Sorts } (_Args ))  => true                              requires isForbiddenConstructor(Ctor)
    rule usesForbiddedConstructors(Ctor { .Sorts } ( Args ))  => usesForbiddedConstructorsPs(Args) requires notBool isForbiddenConstructor(Ctor)
    rule usesForbiddedConstructors(inj{ _, _ } (P) )          => usesForbiddedConstructors(P)
    rule usesForbiddedConstructors(\not{ _ } (P) )            => usesForbiddedConstructors(P)
    rule usesForbiddedConstructors(\and{ _ } (P1, P2) )       => usesForbiddedConstructors(P1) orBool usesForbiddedConstructors(P2)
    rule usesForbiddedConstructors(\or { _ } (P1, P2) )       => usesForbiddedConstructors(P1) orBool usesForbiddedConstructors(P2)
    rule usesForbiddedConstructors(\equals{ _, _ } (P1, P2) ) => usesForbiddedConstructors(P1) orBool usesForbiddedConstructors(P2)
    rule usesForbiddedConstructors(\forall{_} (_, P) )        => usesForbiddedConstructors(P)
    rule usesForbiddedConstructors(\exists{_} (_, P) )        => usesForbiddedConstructors(P)
    rule usesForbiddedConstructors(\ceil{ _, _ } (P) )        => usesForbiddedConstructors(P)
    rule usesForbiddedConstructors(\bottom{ _ } () )          => false
    rule usesForbiddedConstructors(\top{ _ } () )             => false
    rule usesForbiddedConstructors(\dv{ _ } (_) )             => false
    rule usesForbiddedConstructors(_ : _)                     => false
    
    syntax Bool ::= usesForbiddedConstructorsPs(Patterns) [function]
    rule usesForbiddedConstructorsPs(P, Ps) => usesForbiddedConstructors(P) orBool usesForbiddedConstructorsPs(Ps) 
    rule usesForbiddedConstructorsPs(.Patterns) => false
    
    syntax Bool ::= isForbiddenConstructor(KVar) [function]
    rule isForbiddenConstructor( KVar) => true requires findString(NameToString(KVar), "Hash", 0) =/=Int -1
    rule isForbiddenConstructor(LblemptyBlock) => true
    rule isForbiddenConstructor(_KVar) => false [owise]
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

    syntax Patterns ::= getRuleInstrumentation(Pattern) [function]
    rule getRuleInstrumentation(P) => first(findSubTermsByConstructor(Lbl'-LT-'ruleInstrumentation'-GT-', P))
```

```k
endmodule
```
