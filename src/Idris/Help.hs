module Idris.Help (CmdArg(..), help) where

data CmdArg = ExprArg -- ^ The command takes an expression
            | NameArg -- ^ The command takes a name
            | FileArg -- ^ The command takes a file
            | ModuleArg -- ^ The command takes a module name
            | OptionArg -- ^ The command takes an option
            | MetaVarArg -- ^ The command takes a metavariable
            | NoArg -- ^ No completion (yet!?)
            | SpecialHeaderArg -- ^ do not use

instance Show CmdArg where
    show ExprArg = "<expr>"
    show NameArg = "<name>"
    show FileArg = "<filename>"
    show ModuleArg = "<module>"
    show OptionArg = "<option>"
    show MetaVarArg = "<metavar>"
    show NoArg = ""
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
    ([":q",":quit"], NoArg, "Exit the Idris system")
  ]
