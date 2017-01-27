{-|
Module      : Idris.Help
Description : Utilities to aid with the REPL's HELP system.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}

module Idris.Help (CmdArg(..), extraHelp) where

data CmdArg = ExprArg               -- ^ The command takes an expression
            | NameArg               -- ^ The command takes a name
            | FileArg               -- ^ The command takes a file
            | ShellCommandArg       -- ^ The command takes a shell command name
            | ModuleArg             -- ^ The command takes a module name
            | PkgArgs               -- ^ The command takes a list of package names
            | NumberArg             -- ^ The command takes a number
            | NamespaceArg          -- ^ The command takes a namespace name
            | OptionArg             -- ^ The command takes an option
            | MetaVarArg            -- ^ The command takes a metavariable
            | ColourArg             -- ^ The command is the colour-setting command
            | NoArg                 -- ^ No completion (yet!?)
            | SpecialHeaderArg      -- ^ do not use
            | ConsoleWidthArg       -- ^ The width of the console
            | DeclArg               -- ^ An Idris declaration, as might be contained in a file
            | ManyArgs CmdArg       -- ^ Zero or more of one kind of argument
            | OptionalArg CmdArg    -- ^ Zero or one of one kind of argument
            | SeqArgs CmdArg CmdArg -- ^ One kind of argument followed by another

instance Show CmdArg where
    show ExprArg          = "<expr>"
    show NameArg          = "<name>"
    show FileArg          = "<filename>"
    show ShellCommandArg  = "<command>"
    show ModuleArg        = "<module>"
    show PkgArgs          = "<package list>"
    show NumberArg        = "<number>"
    show NamespaceArg     = "<namespace>"
    show OptionArg        = "<option>"
    show MetaVarArg       = "<hole>"
    show ColourArg        = "<option>"
    show NoArg            = ""
    show SpecialHeaderArg = "Arguments"
    show ConsoleWidthArg  = "auto|infinite|<number>"
    show DeclArg = "<top-level declaration>"
    show (ManyArgs a) = "(" ++ show a ++ ")..."
    show (OptionalArg a) = "[" ++ show a ++ "]"
    show (SeqArgs a b) = show a ++ " " ++ show b

-- | Use these for completion, but don't show them in :help
extraHelp ::[([String], CmdArg, String)]
extraHelp =
    [ ([":casesplit!", ":cs!"], NoArg, ":cs! <line> <name> destructively splits the pattern variable on the line")
    , ([":addclause!", ":ac!"], NoArg, ":ac! <line> <name> destructively adds a clause for the definition of the name on the line")
    , ([":addmissing!", ":am!"], NoArg, ":am! <line> <name> destructively adds all missing pattern matches for the name on the line")
    , ([":makewith!", ":mw!"], NoArg, ":mw! <line> <name> destructively adds a with clause for the definition of the name on the line")
    , ([":proofsearch!", ":ps!"], NoArg, ":ps! <line> <name> <names> destructively does proof search for name on line, with names as hints")
    , ([":addproofclause!", ":apc!"], NoArg, ":apc! <line> <name> destructively adds a pattern-matching proof clause to name on line")
    , ([":refine!", ":ref!"], NoArg, ":ref! <line> <name> <name'> destructively attempts to partially solve name on line, with name' as hint, introducing holes for arguments that aren't inferrable")
    ]
