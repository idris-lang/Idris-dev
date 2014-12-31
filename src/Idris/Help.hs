module Idris.Help (CmdArg(..), help, extraHelp) where

data CmdArg = ExprArg -- ^ The command takes an expression
            | NameArg -- ^ The command takes a name
            | FileArg -- ^ The command takes a file
            | ModuleArg -- ^ The command takes a module name
            | PkgArgs -- ^ The command takes a list of package names
            | NumberArg -- ^ The command takes a number
            | NamespaceArg -- ^ The command takes a namespace name
            | OptionArg -- ^ The command takes an option
            | MetaVarArg -- ^ The command takes a metavariable
            | ColourArg  -- ^ The command is the colour-setting command
            | NoArg -- ^ No completion (yet!?)
            | SpecialHeaderArg -- ^ do not use
            | ConsoleWidthArg -- ^ The width of the console
            | DeclArg -- ^ An Idris declaration, as might be contained in a file
            | ManyArgs CmdArg -- ^ Zero or more of one kind of argument
            | OptionalArg CmdArg -- ^ Zero or one of one kind of argument
            | SeqArgs CmdArg CmdArg -- ^ One kind of argument followed by another

instance Show CmdArg where
    show ExprArg          = "<expr>"
    show NameArg          = "<name>"
    show FileArg          = "<filename>"
    show ModuleArg        = "<module>"
    show PkgArgs          = "<package list>"
    show NumberArg        = "<number>"
    show NamespaceArg     = "<namespace>"
    show OptionArg        = "<option>"
    show MetaVarArg       = "<metavar>"
    show ColourArg        = "<option>"
    show NoArg            = ""
    show SpecialHeaderArg = "Arguments"
    show ConsoleWidthArg  = "auto|infinite|<number>"
    show DeclArg = "<top-level declaration>"
    show (ManyArgs a) = "(" ++ show a ++ ")..."
    show (OptionalArg a) = "[" ++ show a ++ "]"
    show (SeqArgs a b) = show a ++ " " ++ show b

help :: [([String], CmdArg, String)]
help =
  [ (["<expr>"], NoArg, "Evaluate an expression"),
    ([":t"], ExprArg, "Check the type of an expression"),
    ([":miss", ":missing"], NameArg, "Show missing clauses"),
    ([":doc"], NameArg, "Show internal documentation"),
    ([":mkdoc"], NamespaceArg, "Generate IdrisDoc for namespace(s) and dependencies"),
    ([":apropos"], SeqArgs (OptionalArg PkgArgs) NameArg, " Search names, types, and documentation"),
    ([":search", ":s"], SeqArgs (OptionalArg PkgArgs) ExprArg, " Search for values by type"),
    ([":whocalls", ":wc"], NameArg, "List the callers of some name"),
    ([":callswho", ":cw"], NameArg, "List the callees of some name"),
    ([":total"], NameArg, "Check the totality of a name"),
    ([":r",":reload"], NoArg, "Reload current file"),
    ([":l",":load"], FileArg, "Load a new file"),
    ([":cd"], FileArg, "Change working directory"),
    ([":module"], ModuleArg, "Import an extra module"), -- NOTE: dragons
    ([":e",":edit"], NoArg, "Edit current file using $EDITOR or $VISUAL"),
    ([":m",":metavars"], NoArg, "Show remaining proof obligations (metavariables)"),
    ([":p",":prove"], MetaVarArg, "Prove a metavariable"),
    ([":a",":addproof"], NameArg, "Add proof to source file"),
    ([":rmproof"], NameArg, "Remove proof from proof stack"),
    ([":showproof"], NameArg, "Show proof"),
    ([":proofs"], NoArg, "Show available proofs"),
    ([":x"], ExprArg, "Execute IO actions resulting from an expression using the interpreter"),
    ([":c",":compile"], FileArg, "Compile to an executable [codegen] <filename>"),
    ([":exec",":execute"], NoArg, "Compile to an executable and run"),
    ([":dynamic"], FileArg, "Dynamically load a C library (similar to %dynamic)"),
    ([":dynamic"], NoArg, "List dynamically loaded C libraries"),
    ([":?",":h",":help"], NoArg, "Display this help text"),
    ([":set"], OptionArg, "Set an option (errorcontext, showimplicits)"),
    ([":unset"], OptionArg, "Unset an option"),
    ([":colour", ":color"], ColourArg, "Turn REPL colours on or off; set a specific colour"),
    ([":consolewidth"], ConsoleWidthArg, "Set the width of the console"),
    ([":q",":quit"], NoArg, "Exit the Idris system"),
    ([":w", ":warranty"], NoArg, "Displays warranty information"),
    ([":let"], ManyArgs DeclArg, "Evaluate a declaration, such as a function definition, instance implementation, or fixity declaration"),
    ([":undefine",":unlet"], ManyArgs NameArg, "Remove the listed repl definitions, or all repl definitions if no names given"),
    ([":printdef"], NameArg, "Show the definition of a function"),
    ([":pp", ":pprint"], (SeqArgs OptionArg (SeqArgs NumberArg NameArg)), "Pretty prints an Idris function in either LaTeX or HTML and for a specified width.")
  ]

-- | Use these for completion, but don't show them in :help
extraHelp ::[([String], CmdArg, String)]
extraHelp =
    [ ([":casesplit", ":cs"], NoArg, ":cs <line> <name> splits the pattern variable on the line")
    , ([":casesplit!", ":cs!"], NoArg, ":cs! <line> <name> destructively splits the pattern variable on the line")
    , ([":addclause", ":ac"], NoArg, ":ac <line> <name> adds a clause for the definition of the name on the line")
    , ([":addclause!", ":ac!"], NoArg, ":ac! <line> <name> destructively adds a clause for the definition of the name on the line")
    , ([":addmissing", ":am"], NoArg, ":am <line> <name> adds all missing pattern matches for the name on the line")
    , ([":addmissing!", ":am!"], NoArg, ":am! <line> <name> destructively adds all missing pattern matches for the name on the line")
    , ([":makewith", ":mw"], NoArg, ":mw <line> <name> adds a with clause for the definition of the name on the line")
    , ([":makewith!", ":mw!"], NoArg, ":mw! <line> <name> destructively adds a with clause for the definition of the name on the line")
    , ([":proofsearch", ":ps"], NoArg, ":ps <line> <name> <names> does proof search for name on line, with names as hints")
    , ([":proofsearch!", ":ps!"], NoArg, ":ps! <line> <name> <names> destructively does proof search for name on line, with names as hints")
    , ([":addproofclause", ":apc"], NoArg, ":apc <line> <name> adds a pattern-matching proof clause to name on line")
    , ([":addproofclause!", ":apc!"], NoArg, ":apc! <line> <name> destructively adds a pattern-matching proof clause to name on line")
    , ([":refine", ":ref"], NoArg, ":ref <line> <name> <name'> attempts to partially solve name on line, with name' as hint, introducing metavariables for arguments that aren't inferrable")
    , ([":refine!", ":ref!"], NoArg, ":ref! <line> <name> <name'> destructively attempts to partially solve name on line, with name' as hint, introducing metavariables for arguments that aren't inferrable")
    ]
