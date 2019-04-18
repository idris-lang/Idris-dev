*****************
Syntax Reference
*****************

Here we present a rough description of Idris' surface syntax as an eBNF grammar.
This presentend grammar may differ from syntax that Idris' parser can handle due to the parser and grammar description not being in sync.

=========
Notation
=========

Grammar shortcut notation::

  ~CHARSEQ = complement of char sequence (i.e. any character except CHARSEQ)
  RULE? = optional rule (i.e. RULE or nothing)
  RULE* = repeated rule (i.e. RULE zero or more times)
  RULE+ = repeated rule with at least one match (i.e. RULE one or more times)
  RULE! = invalid rule (i.e. rule that is not valid in context, report meaningful error in case)
  RULE{n} = rule repeated n times


=============
Main Grammar
=============

.. productionlist::
   ModuleHeader : `DocComment_t`? "module" `Identifier_t` ";"? ;
   Import       : "import" `Identifier_t` ";"? ;
   Prog         : `Decl`* `EOF`;
   Decl         : `DeclP`
                : | `Using`
                : | `Params`
                : | `Mutual`
                : | `Namespace`
                : | `Interface`
                : | `Implementation`
                : | `DSL`
                : | `Directive`
                : | `Provider`
                : | `Transform`
                : | `Import`!
                : | `RunElabDecl` ;
   DeclP : `Fixity`
         : | `FunDecl`
         : | `Data`
         : | `Record`
         : | `SyntaxDecl` ;


--------------------
Syntax Declarations
--------------------

.. productionlist::
   SyntaxDecl : `SyntaxRule` ;
   SyntaxRuleOpts : "term" | "pattern" ;
   SyntaxRule : `SyntaxRuleOpts`? "syntax" `SyntaxSym`+ "=" `TypeExpr` `Terminator`;
   SyntaxSym :   '[' `Name_t` ']'
             : |  '{' `Name_t` '}'
             : |  `Name_t`
             : |  `StringLiteral_t`;
   SyntaxSym :    '[' `Name_t` ']'
             : |  '{' `Name_t` '}'
             : |  `Name_t`
             : |  `StringLiteral_t`;

----------
Functions
----------

.. productionlist::
   FunDecl : `FunDeclP`;
   FunDeclP : `DocComment_t`? `FnOpts`* `Accessibility`? `FnOpts`* `FnName` `TypeSig` `Terminator`
            : | `Postulate`
            : | `Pattern`
            : | `CAF` ;
   FnOpts : `FnOpt`* `Accessibility` `FnOpt`* ;
   FnOpt :   'total'
         : | 'partial'
         : | 'covering'
         : | 'implicit'
         : | '%' 'no_implicit'
         : | '%' 'assert_total'
         : | '%' 'error_handler'
         : | '%' 'reflection'
         : | '%' 'specialise' '[' `NameTimesList`? ']' ;
   NameTimes : `FnName` `Natural`?;
   NameTimesList : `NameTimes` | `NameTimes` ',' `NameTimesList` ;
   Postulate : `DocComment_t`? 'postulate' `FnOpts`* `Accesibility`? `FnOpts`* `FnName` `TypeSig` `Terminator` ;

--------------------
Blocks & Namespaces
--------------------

.. productionlist::
  Using : 'using' '(' `UsingDeclList` ')' `OpenBlock` `Decl`* `CloseBlock` ;
  UsingDeclList : `UsingDeclListP` | `NameList TypeSig`;
  UsingDeclListP : `UsingDecl` | `UsingDecl` ',' `UsingDeclListP` ;
  NameList : `Name` | `Name` ',' `NameList` ;
  UsingDecl : `FnName` `TypeSig` | `FnName` `FnName`+ ;
  Params : 'parameters' '(' `TypeDeclList` ')' `OpenBlock` `Decl`* `CloseBlock`;
  Mutual : 'mutual' `OpenBlock` `Decl`* `CloseBlock` ;
  Namespace : 'namespace' `identifier` `OpenBlock` `Decl`+ `CloseBlock` ;

----------------------------
Interfaces & Implementation
----------------------------

.. productionlist::
  ImplementationBlock : 'where' `OpenBlock` `FnDecl`* `CloseBlock` ;
  MethodOrImplementation : `FnDecl` | `Implementation`;
  InterfaceBlock : 'where' `OpenBlock` `Constructor`? `MethodOrImplementation`* `CloseBlock` ;
  InterfaceArgument : `Name` | '(' `Name` ':' `Expr` ')';
  Interface ::= `DocComment_t`? `Accessibility`? 'interface' `ConstraintList`? `Name` `InterfaceArgument`* `InterfaceBlock`?;
  Implementation : `DocComment_t`? 'implementation' `ImplementationName`? `ConstraintList`? `Name` `SimpleExpr`* `ImplementationBlock`? ;
  ImplementationName : '[' `Name` ']';


-------
Bodies
-------

.. productionlist::
  Pattern : `Clause`;
  CAF : 'let' `FnName` '=' `Expr` `Terminator`;
  ArgExpr : `HSimpleExpr` | "In Pattern External (User-defined) Expression";
  RHS :    '='             `Expr`
      : | '?='  `RHSName`? `Expr`
      : |  `Impossible` ;
  RHSName : '{' `FnName` '}' ;
  RHSOrWithBlock : `RHS` `WhereOrTerminator`
                 : | 'with' `SimpleExpr` `OpenBlock` `FnDecl`+ `CloseBlock`;
  Clause :   `WExpr`+ `RHSOrWithBlock`
         : | `SimpleExpr` '<=='  `FnName` `RHS` `WhereOrTerminator`
         : | `ArgExpr` `Operator` `ArgExpr` `WExpr`* `RHSOrWithBlock` {- Except "=" and "?=" operators to avoid ambiguity -}
         : | `FnName` `ConstraintArg`* `ImplicitOrArgExpr`*    `WExpr`* `RHSOrWithBlock`;
  ImplicitOrArgExpr ::= `ImplicitArg` | `ArgExpr`;
  WhereOrTerminator ::= `WhereBlock` | `Terminator`;
  WExpr ::= '|' `Expr`';
  WhereBlock : 'where' `OpenBlock` `Decl`+ `CloseBlock`;

----------
Directives
----------

.. productionlist::
  Codegen: 'C'
         : | 'Java'
         : | 'JavaScript'
         : | 'Node'
         : | 'LLVM'
         : | 'Bytecode' ;
  StringList : `String` | `String` ',' `StringList` ;
  Directive : '%' `DirectiveP`;
  DirectiveP :   'lib'            `CodeGen` `String_t`
             : | 'link'           `CodeGen` `String_t`
             : | 'flag'           `CodeGen` `String_t`
             : | 'include'        `CodeGen` `String_t`
             : | 'hide'           `Name`
             : | 'freeze'         `Name`
             : | 'thaw'           `Name`
             : | 'access'         `Accessibility`
             : | 'default'        `Totality`
             : | 'logging'        `Natural`
             : | 'dynamic'        `StringList`
             : | 'name'           `Name` `NameList`
             : | 'error_handlers' `Name` `NameList`
             : | 'language'       'TypeProviders'
             : | 'language'       'ErrorReflection'
             : | 'deprecated' `Name` `String`
             : | 'fragile'    `Name` `Reason` ;
  LangExt :   "TypeProviders"
          : | "ErrorReflection"
          : | "UniquenessTypes"
          : | "LinearTypes"
          : | "DSLNotation"
          : | "ElabReflection"
          : | "FirstClassReflection" ;
  Totality : 'partial' | 'total' | 'covering'
  Provider : `DocComment_t`? '%' 'provide' `Provider_What`? '(' `FnName` `TypeSig` ')' 'with' `Expr`;
  ProviderWhat : 'proof' | 'term' | 'type' | 'postulate'
  Transform : '%' 'transform' `Expr` '==>' `Expr`;
  RunElabDecl : '%' 'runElab' `Expr`;


===========
Expressions
===========

.. productionlist::
  FullExpr : `Expr` `EOF_t` ;
  Expr     : `Pi` ;
  OpExpr   : "Expression Parser with Operators based on ExprP" ;
  ExprP    : "External (User-defined) Syntax" |  `InternalExpr` ;
  InternalExpr : `UnifyLog`
               : | `RecordType`
               : | `SimpleExpr`
               : | `Lambda`
               : | `QuoteGoal`
               : | `Let`
               : | `If`
               : | `RewriteTerm`
               : | `CaseExpr`
               : | `DoBlock`
               : | `App` ;

-------
Bodies
-------

.. productionlist::
  Impossible : `impossible` ;
  CaseExpr : "case" `Expr` "of" `OpenBlock` `CaseOption`+ `CloseBlock` ;
  CaseOption : `Expr` (`Impossible` | "=>" `Expr`) `Terminator` ;
  ProofExpr : "proof" `OpenBlock` `Tactic'`* `CloseBlock` ;
  TacticsExpr : "tactics" `OpenBlock` `Tactic'`* `CloseBlock` ;
  SimpleExpr : "External (User-defined) Simple Expression"
             : | "?" `Name`
             : | "%" "implementation"
             : | "Refl" ("{" `Expr` "}")?
             : | `ProofExpr`
             : | `TacticsExpr`
             : | `FnName`
             : | `Idiom`
             : | `List`
             : | `Alt`
             : | `Bracketed`
             : | `Constant`
             : | `Type`
             : | "Void"
             : | `Quasiquote`
             : | `NameQuote`
             : | `Unquote`
             : | "_" ;
  Bracketed : "(" `BracketedP` ;
  BracketedP : ")"
             : | `Expr` ")"
             : | `ExprList` ")"
             : | `DependentPair` ")"
             : | `Operator` `Expr` ")"
             : | `Expr` `Operator` ")" ;
  Alt : "(|" `Expr_List` "|)" ;
  Expr_List : `Expr'` | `Expr'` "," `Expr_List` ;
  HSimpleExpr : "." `SimpleExpr` | `SimpleExpr` ;
  UnifyLog : "%" "unifyLog" `SimpleExpr` ;
  RunTactics : "%" "runElab" `SimpleExpr` ;
  Disamb : "with" `NameList` `Expr` ;
  NoImplicits : "%" "noImplicits" `SimpleExpr` ;
  App : "mkForeign" `Arg` `Arg`*
      : | `MatchApp`
      : | `SimpleExpr` `Arg`* ;
  MatchApp : `SimpleExpr` "<==" `FnName` ;
  Arg :` ImplicitArg` | `ConstraintArg` | `SimpleExpr` ;
  ImplicitArg : "{" `Name` ("=" `Expr`)? "}" ;
  ConstraintArg : "@{" `Expr` "}" ;
  Quasiquote : "`(" `Expr` ")" ;
  Unquote : "," `Expr` ;
  RecordType : "record" "{" `FieldTypeList` "}" ;
  FieldTypeList : `FieldType` | `FieldType` "," `FieldTypeList` ;
  FieldType : `FnName` "=" `Expr` ;
  TypeSig : ":" `Expr` ;
  TypeExpr : `ConstraintList`? `Expr` ;
  Lambda : "\\" `TypeOptDeclList` `LambdaTail`
         : | "\\" `SimpleExprList`  `LambdaTail` ;
  SimpleExprList : `SimpleExpr` | `SimpleExpr` "," `SimpleExprList` ;
  LambdaTail : `Impossible` | "=>" `Expr` ;
  RewriteTerm : "rewrite" `Expr` ("==>" `Expr`)? "in" `Expr` ;
  RigCount: "1" : "0" ;
  Let : "let" `Name` `TypeSig`"? "=" `Expr`  "in" `Expr`
      : | "let" `Expr'`            "=" `Expr'` "in" `Expr` ;
  TypeSig' : ":" `Expr'` ;
  If : "if" `Expr` "then" `Expr` "else" `Expr` ;
  QuoteGoal : "quoteGoal" `Name` "by" `Expr` "in" `Expr` ;

----
Pies
----

.. productionlist::
  Pi : `PiOpts` `Static`? `PiP` ;
  PiP : `OpExpr` ("->" `Pi`)?
      : | "(" `TypeDeclList`           ")"            "->" `Pi`
      : | "{" `TypeDeclList`           "}"            "->" `Pi`
      : | "{" "auto"    `TypeDeclList` "}"            "->" `Pi`
      : | "{" "default" `SimpleExpr` `TypeDeclList` "}" "->" `Pi` ;
  PiOpts : "."? ;
  ConstraintList : "(" `Expr_List` ")" "=>"
                 : | `Expr`              "=>" ;
  TypeDeclList : `FunctionSignatureList`
               : | `NameList` `TypeSig` ;
  FunctionSignatureList : `Name` `TypeSig`
                        : | `Name` `TypeSig` "," `FunctionSignatureList` ;
  TypeOptDeclList : `NameOrPlaceholder` `TypeSig`?
                  : | `NameOrPlaceholder` `TypeSig`? "," `TypeOptDeclList` ;
  NameOrPlaceHolder : `Name` : "_" ;
  ListExpr : "[" "]" | "[" `Expr` "|" `DoList` "]" | "[" `ExprList` "]" ;
  ExprList : `Expr` | `Expr` "," `ExprList` ;


-------------------
Do Blocks & Idioms
-------------------

.. productionlist::
  DoList : `Do` : `Do` "," `DoList` ;
  Do' : `Do` `KeepTerminator` ;
  DoBlock : "do" `OpenBlock` `Do'`+ `CloseBlock` ;
  Do : "let" `Name`  `TypeSig`"?      "=" `Expr`
     : | "let" `Expr'`                  "=" `Expr`
     : | "rewrite" `Expr`
     : | `Name`  "<-" `Expr`
     : | `Expr'` "<-" `Expr`
     : | `Expr` ;
  Idiom : "[|" `Expr` "|]" ;


----------
Constants
----------

.. productionlist::
  Constant : | "Integer"
           : | "Int"
           : | "Char"
           : | "Double"
           : | "String"
           : | "Bits8"
           : | "Bits16"
           : | "Bits32"
           : | "Bits64"
           : | `Float_t`
           : | `Natural_t`
           : | `VerbatimString_t`
           : | `String_t`
           : | `Char_t` ;
  VerbatimString_t : "\"\"\"" ~"\"\"\"" "\""* "\"\"\"" ;

-------
Tactics
-------

.. productionlist::
  Tactic : "intro" `NameList`?
         : |  "intros"
         : |  "refine"      `Name` `Imp`+
         : |  "mrefine"     `Name`
         : |  "rewrite"     `Expr`
         : |  "induction"   `Expr`
         : |  "equiv"       `Expr`
         : |  "let"         `Name` ":" `Expr'` "=" `Expr`
         : |  "let"         `Name`            "=" `Expr`
         : |  "focus"       `Name`
         : |  "exact"       `Expr`
         : |  "applyTactic" `Expr`
         : |  "reflect"     `Expr`
         : |  "fill"        `Expr`
         : |  "try"         `Tactic` "|" `Tactic`
         : |  "{" `TacticSeq` "}"
         : |  "compute"
         : |  "trivial"
         : |  "solve"
         : |  "attack"
         : |  "state"
         : |  "term"
         : |  "undo"
         : |  "qed"
         : |  "abandon"
         : |  ":" "q" ;
  TacticSeq : `Tactic` ";" `Tactic` | `Tactic` ";" `TacticSeq` ;

----
Misc
----

.. productionlist::
  Imp : "?" | "_" ;
  Static : "%static" ;

=====
Data
=====

.. productionlist::
  Record : `DocComment` `Accessibility`? "record" `FnName` `TypeSig` "where" `OpenBlock` `Constructor` `KeepTerminator` `CloseBlock`;
  DataI : "data" | "codata";
  Data : `DocComment`? `Accessibility`? `DataI` `FnName` `TypeSig` `ExplicitTypeDataRest`?
       : `DocComment`? `Accessibility`? `DataI` `FnName` `Name`* `DataRest`? ;
  Constructor': `Constructor` `KeepTerminator` ;
  ExplicitTypeDataRest : "where" `OpenBlock` `Constructor'`* `CloseBlock`;
  DataRest : "=" `SimpleConstructorList` `Terminator` | "where"!;
  SimpleConstructorList : `SimpleConstructor` | `SimpleConstructor` "|" `SimpleConstructorList`;
  Constructor : `DocComment`? `FnName` `TypeSig`;
  SimpleConstructor : `FnName` `SimpleExpr`* `DocComment`?;
  DSL : "dsl" `FnName` `OpenBlock` `Overload'`+ `CloseBlock`;
  OverloadIdentifier : "let" | `Identifier`;
  Overload : `OverloadIdentifier` "=" `Expr`;


=========
Operators
=========

.. productionlist::
  BacktickOperator: `Name` ;
  OperatorName: `SymbolicOperator` : `BacktickOperator` ;
  OperatorFront: "(" "=" ")" | (`Identifier_t` ".")? "(" `Operator_t` ")" ;
  FnName: `Name` | `OperatorFront`;
  Fixity: `FixityType` `Natural_t` `OperatorList` `Terminator`;
  FixityType: "infixl" | "infixr" | "infix" | "prefix";


==============
Documentation
==============

.. productionlist::
  SingleLineComment_t: "--" ~`EOL_t`* `EOL_t` ;
  MultiLineComment_t: "{" ..  "}" | "{ -" `InCommentChars_t` ;
  InCommentChars_t : "- }" | `MultiLineComment_t` `InCommentChars_t` | ~"- }"+ `InCommentChars_t`;
  DocComment_t : `DocCommentLine` (`ArgCommentLine` `DocCommentLine`*)* ;
  DocCommentLine : "|||" ~`EOL_t`* `EOL_t` ;
  ArgCommentLine : "|||" "@" ~`EOL_t`* `EOL_t` ;
