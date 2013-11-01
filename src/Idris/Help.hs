module Idris.Help (CmdArg(..), help, extraHelp) where

data CmdArg = ExprArg -- ^ The command takes an expression
            | NameArg -- ^ The command takes a name
            | FileArg -- ^ The command takes a file
            | ModuleArg -- ^ The command takes a module name
            | OptionArg -- ^ The command takes an option
            | MetaVarArg -- ^ The command takes a metavariable
            | ColourArg  -- ^ The command is the colour-setting command
            | NoArg -- ^ No completion (yet!?)
            | SpecialHeaderArg -- ^ do not use

instance Show CmdArg where
    show ExprArg          = "<expr>"
    show NameArg          = "<name>"
    show FileArg          = "<filename>"
    show ModuleArg        = "<module>"
    show OptionArg        = "<option>"
    show MetaVarArg       = "<metavar>"
    show ColourArg        = "<option>"
    show NoArg            = ""
    show SpecialHeaderArg = "Arguments"

help :: [([String], CmdArg, String)]
help =
  [ (["<expr>"], NoArg, "Evaluate an expression"),
    ([":t"], ExprArg, "Check the type of an expression"),
    ([":miss", ":missing"], NameArg, "Show missing clauses"),
    ([":i", ":info"], NameArg, "Display information about a type class"),
    ([":total"], NameArg, "Check the totality of a name"),
    ([":r",":reload"], NoArg, "Reload current file"),
    ([":l",":load"], FileArg, "Load a new file"),
    ([":cd"], FileArg, "Change working directory"),
    ([":m",":module"], ModuleArg, "Import an extra module"), -- NOTE: dragons
    ([":e",":edit"], NoArg, "Edit current file using $EDITOR or $VISUAL"),
    ([":m",":metavars"], MetaVarArg, "Show remaining proof obligations (metavariables)"),
    ([":p",":prove"], MetaVarArg, "Prove a metavariable"),
    ([":a",":addproof"], NameArg, "Add proof to source file"),
    ([":rmproof"], NameArg, "Remove proof from proof stack"),
    ([":showproof"], NameArg, "Show proof"),
    ([":proofs"], NoArg, "Show available proofs"),
    ([":x"], ExprArg, "Execute IO actions resulting from an expression using the interpreter"),
    ([":c",":compile"], FileArg, "Compile to an executable <filename>"),
    ([":js", ":javascript"], FileArg, "Compile to JavaScript <filename>"),
    ([":exec",":execute"], NoArg, "Compile to an executable and run"),
    ([":dynamic"], FileArg, "Dynamically load a C library (similar to %dynamic)"),
    ([":dynamic"], NoArg, "List dynamically loaded C libraries"),
    ([":?",":h",":help"], NoArg, "Display this help text"),
    ([":set"], OptionArg, "Set an option (errorcontext, showimplicits)"),
    ([":unset"], OptionArg, "Unset an option"),
    ([":colour", ":color"], ColourArg, "Turn REPL colours on or off; set a specific colour"),
    ([":q",":quit"], NoArg, "Exit the Idris system")
  ]

-- | Use these for completion, but don't show them in :help
extraHelp ::[([String], CmdArg, String)]
extraHelp =
    [ ([":casesplit", ":cs"], NoArg, ":cs <line> <name> splits the pattern variable on the line")
    , ([":casesplit!", ":cs!"], NoArg, ":cs! <line> <name> destructively splits the pattern variable on the line")
    , ([":addclause", ":ac"], NoArg, ":ac <line> <name> adds a clause for the definition of the name on the line")
    , ([":addclause!", ":ac!"], NoArg, ":ac! <line> <name> destructively adds a clause for the definition of the name on the line")
    , ([":makewith", ":mw"], NoArg, ":mw <line> <name> adds a with clause for the definition of the name on the line")
    , ([":makewith!", ":mw!"], NoArg, ":mw! <line> <name> destructively adds a with clause for the definition of the name on the line")
    , ([":proofsearch", ":ps"], NoArg, ":ps <line> <name> <names> does proof search for name on line, with names as hints")
    , ([":proofsearch!", ":ps!"], NoArg, ":ps! <line> <name> <names> destructively does proof search for name on line, with names as hints")
    , ([":addproofclause", ":apc"], NoArg, ":apc <line> <name> adds a pattern-matching proof clause to name on line")
    , ([":addproofclause!", ":apc!"], NoArg, ":apc! <line> <name> destructively adds a pattern-matching proof clause to name on line")
    ]