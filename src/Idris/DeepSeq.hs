{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Idris.DeepSeq(module Idris.DeepSeq, module Idris.Core.DeepSeq) where

import Idris.Core.DeepSeq
import Idris.Docstrings
import Idris.Core.TT
import Idris.AbsSyntaxTree
import Idris.Colours
import IRTS.Lang (PrimFn(..))
import IRTS.CodegenCommon (OutputType (..))
import Util.DynamicLinker

import Control.DeepSeq

import qualified Cheapskate.Types as CT
import qualified Idris.Docstrings as D

instance NFData a => NFData (D.Docstring a) where
  rnf (D.DocString opts contents) = rnf opts `seq` rnf contents `seq` ()

instance NFData CT.Options where
  rnf (CT.Options x1 x2 x3 x4) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()

instance NFData ConsoleWidth where
  rnf InfinitelyWide = ()
  rnf (ColsWide x) = rnf x `seq` ()
  rnf AutomaticWidth = ()

instance NFData PrimFn where
    rnf (LPlus x) = rnf x `seq` ()
    rnf (LMinus x) = rnf x `seq` ()
    rnf (LTimes x) = rnf x `seq` ()
    rnf (LUDiv x) = rnf x `seq` ()
    rnf (LSDiv x) = rnf x `seq` ()
    rnf (LURem x) = rnf x `seq` ()
    rnf (LSRem x) = rnf x `seq` ()
    rnf (LAnd x) = rnf x `seq` ()
    rnf (LOr x) = rnf x `seq` ()
    rnf (LXOr x) = rnf x `seq` ()
    rnf (LCompl x) = rnf x `seq` ()
    rnf (LSHL x) = rnf x `seq` ()
    rnf (LLSHR x) = rnf x `seq` ()
    rnf (LASHR x) = rnf x `seq` ()
    rnf (LEq x) = rnf x `seq` ()
    rnf (LLt x) = rnf x `seq` ()
    rnf (LLe x) = rnf x `seq` ()
    rnf (LGt x) = rnf x `seq` ()
    rnf (LGe x) = rnf x `seq` ()
    rnf (LSLt x) = rnf x `seq` ()
    rnf (LSLe x) = rnf x `seq` ()
    rnf (LSGt x) = rnf x `seq` ()
    rnf (LSGe x) = rnf x `seq` ()
    rnf (LSExt x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
    rnf (LZExt x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
    rnf (LTrunc x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
    rnf (LStrConcat) = ()
    rnf (LStrLt) = ()
    rnf (LStrEq) = ()
    rnf (LStrLen) = ()
    rnf (LIntFloat x) = rnf x `seq` ()
    rnf (LFloatInt x) = rnf x `seq` ()
    rnf (LIntStr x) = rnf x `seq` ()
    rnf (LStrInt x) = rnf x `seq` ()
    rnf (LFloatStr) = ()
    rnf (LStrFloat) = ()
    rnf (LChInt x) = rnf x `seq` ()
    rnf (LIntCh x) = rnf x `seq` ()
    rnf (LBitCast x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
    rnf (LFExp) = ()
    rnf (LFLog) = ()
    rnf (LFSin) = ()
    rnf (LFCos) = ()
    rnf (LFTan) = ()
    rnf (LFASin) = ()
    rnf (LFACos) = ()
    rnf (LFATan) = ()
    rnf (LFSqrt) = ()
    rnf (LFFloor) = ()
    rnf (LFCeil) = ()
    rnf (LFNegate) = ()
    rnf (LStrHead) = ()
    rnf (LStrTail) = ()
    rnf (LStrCons) = ()
    rnf (LStrIndex) = ()
    rnf (LStrRev) = ()
    rnf (LStrSubstr) = ()
    rnf (LReadStr) = ()
    rnf (LWriteStr) = ()
    rnf (LSystemInfo) = ()
    rnf (LFork) = ()
    rnf (LPar) = ()
    rnf (LExternal x) = rnf x `seq` ()
    rnf (LNoOp) = ()

instance NFData SyntaxRules where
    rnf (SyntaxRules xs) = rnf xs `seq` ()

instance NFData DynamicLib where
    rnf (Lib x _) = rnf x `seq` ()


instance NFData Opt where
    rnf (Filename str) = rnf  str `seq` ()
    rnf (Quiet) = ()
    rnf (NoBanner) = ()
    rnf (ColourREPL bool) = rnf  bool `seq` ()
    rnf (Idemode) = ()
    rnf (IdemodeSocket) = ()
    rnf (ShowLoggingCats) = ()
    rnf (ShowLibs) = ()
    rnf (ShowLibdir) = ()
    rnf (ShowIncs) = ()
    rnf (ShowPkgs) = ()
    rnf (NoBasePkgs) = ()
    rnf (NoPrelude) = ()
    rnf (NoBuiltins) = ()
    rnf (NoREPL) = ()
    rnf (OLogging i) = rnf  i `seq` ()
    rnf (OLogCats cs) = rnf  cs `seq` ()
    rnf (Output str) = rnf  str `seq` ()
    rnf (Interface) = ()
    rnf (TypeCase) = ()
    rnf (TypeInType) = ()
    rnf (DefaultTotal) = ()
    rnf (DefaultPartial) = ()
    rnf (DefaultCovering) = ()
    rnf (WarnPartial) = ()
    rnf (WarnReach) = ()
    rnf (EvalTypes) = ()
    rnf (DesugarNats) = ()
    rnf (NoCoverage) = ()
    rnf (ErrContext) = ()
    rnf (ShowImpl) = ()
    rnf (Verbose) = ()
    rnf (Port str) = rnf  str `seq` ()
    rnf (IBCSubDir str) = rnf  str `seq` ()
    rnf (ImportDir str) = rnf  str `seq` ()
    rnf (PkgBuild str) = rnf  str `seq` ()
    rnf (PkgInstall str) = rnf  str `seq` ()
    rnf (PkgClean str) = rnf  str `seq` ()
    rnf (PkgCheck str) = rnf  str `seq` ()
    rnf (PkgREPL str) = rnf  str `seq` ()
    rnf (PkgMkDoc str) = rnf  str `seq` ()
    rnf (PkgTest str) = rnf  str `seq` ()
    rnf (PkgIndex fp) = rnf  fp `seq` ()
    rnf (WarnOnly) = ()
    rnf (Pkg str) = rnf  str `seq` ()
    rnf (BCAsm str) = rnf  str `seq` ()
    rnf (DumpDefun str) = rnf  str `seq` ()
    rnf (DumpCases str) = rnf  str `seq` ()
    rnf (UseCodegen cg) = rnf  cg `seq` ()
    rnf (CodegenArgs str) = rnf  str `seq` ()
    rnf (OutputTy ot) = rnf  ot `seq` ()
    rnf (Extension le) = rnf  le `seq` ()
    rnf (InterpretScript str) = rnf  str `seq` ()
    rnf (EvalExpr str) = rnf  str `seq` ()
    rnf (TargetTriple str) = rnf  str `seq` ()
    rnf (TargetCPU str) = rnf  str `seq` ()
    rnf (OptLevel i) = rnf  i `seq` ()
    rnf (AddOpt o) = rnf  o `seq` ()
    rnf (RemoveOpt o) = rnf  o `seq` ()
    rnf (Client str) = rnf  str `seq` ()
    rnf (ShowOrigErr) = ()
    rnf (AutoWidth) = ()
    rnf (AutoSolve) = ()
    rnf (UseConsoleWidth cw) = rnf  cw `seq` ()
    rnf DumpHighlights = ()
    rnf NoElimDeprecationWarnings = ()
    rnf NoOldTacticDeprecationWarnings = ()


instance NFData TIData where
    rnf TIPartial = ()
    rnf (TISolution xs) = rnf xs `seq` ()

instance NFData IOption where
    rnf (IOption
         opt_logLevel
         opt_logcats
         opt_typecase
         opt_typeintype
         opt_coverage
         opt_showimp
         opt_errContext
         opt_repl
         opt_verbose
         opt_nobanner
         opt_quiet
         opt_codegen
         opt_outputTy
         opt_ibcsubdir
         opt_importdirs
         opt_triple
         opt_cpu
         opt_cmdline
         opt_origerr
         opt_autoSolve
         opt_autoImport
         opt_optimise
         opt_printdepth
         opt_evaltypes
         opt_desugarnats
         opt_autoimpls) =
         rnf opt_logLevel
         `seq` rnf opt_typecase
         `seq` rnf opt_typeintype
         `seq` rnf opt_coverage
         `seq` rnf opt_showimp
         `seq` rnf opt_errContext
         `seq` rnf opt_repl
         `seq` rnf opt_verbose
         `seq` rnf opt_nobanner
         `seq` rnf opt_quiet
         `seq` rnf opt_codegen
         `seq` rnf opt_outputTy
         `seq` rnf opt_ibcsubdir
         `seq` rnf opt_importdirs
         `seq` rnf opt_triple
         `seq` rnf opt_cpu
         `seq` rnf opt_cmdline
         `seq` rnf opt_origerr
         `seq` rnf opt_autoSolve
         `seq` rnf opt_autoImport
         `seq` rnf opt_optimise
         `seq` rnf opt_printdepth
         `seq` rnf opt_evaltypes
         `seq` rnf opt_desugarnats
         `seq` rnf opt_autoimpls
         `seq` ()

instance NFData LanguageExt where
    rnf TypeProviders = ()
    rnf ErrorReflection = ()

instance NFData Optimisation where
    rnf PETransform = ()

instance NFData ColourTheme where
    rnf (ColourTheme keywordColour
                     boundVarColour
                     implicitColour
                     functionColour
                     typeColour
                     dataColour
                     promptColour
                     postulateColour) =
        rnf keywordColour
        `seq` rnf boundVarColour
        `seq` rnf implicitColour
        `seq` rnf functionColour
        `seq` rnf typeColour
        `seq` rnf dataColour
        `seq` rnf promptColour
        `seq` rnf postulateColour
        `seq` ()

instance NFData IdrisColour where
  rnf (IdrisColour _ x2 x3 x4 x5) = rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()

instance NFData OutputType where
    rnf Raw        = ()
    rnf Object     = ()
    rnf Executable = ()

instance NFData IBCWrite where
    rnf (IBCFix fixDecl) = rnf fixDecl `seq` ()
    rnf (IBCImp name) = rnf name `seq` ()
    rnf (IBCStatic name) = rnf name `seq` ()
    rnf (IBCClass name) = rnf name `seq` ()
    rnf (IBCInstance b1 b2 n1 n2) = rnf b1 `seq` rnf b2 `seq` rnf n1 `seq` rnf n2 `seq` ()
    rnf (IBCDSL name) = rnf name `seq` ()
    rnf (IBCData name) = rnf name `seq` ()
    rnf (IBCOpt name) = rnf name `seq` ()
    rnf (IBCMetavar name) = rnf name `seq` ()
    rnf (IBCSyntax syntax) = rnf syntax `seq` ()
    rnf (IBCKeyword string) = rnf string `seq` ()
    rnf (IBCImport imp) = rnf imp `seq` ()
    rnf (IBCImportDir filePath) = rnf filePath `seq` ()
    rnf (IBCObj codegen filePath) = rnf codegen `seq` rnf filePath `seq` ()
    rnf (IBCLib codegen string) = rnf codegen `seq` rnf string `seq` ()
    rnf (IBCCGFlag codegen string) = rnf codegen `seq` rnf string `seq` ()
    rnf (IBCDyLib string) = rnf string `seq` ()
    rnf (IBCHeader codegen string) = rnf codegen `seq` rnf string `seq` ()
    rnf (IBCAccess name accessibility) = rnf name `seq` rnf accessibility `seq` ()
    rnf (IBCMetaInformation name metaInformation) = rnf name `seq` rnf metaInformation `seq` ()
    rnf (IBCTotal name totality) = rnf name `seq` rnf totality `seq` ()
    rnf (IBCFlags name fnOpts) = rnf name `seq` rnf fnOpts `seq` ()
    rnf (IBCFnInfo name fnInfo) = rnf name `seq` rnf fnInfo `seq` ()
    rnf (IBCTrans name terms) = rnf name `seq` rnf terms `seq` ()
    rnf (IBCErrRev terms) = rnf terms `seq` ()
    rnf (IBCCG name) = rnf name `seq` ()
    rnf (IBCDoc name) = rnf name `seq` ()
    rnf (IBCCoercion name) = rnf name `seq` ()
    rnf (IBCDef name) = rnf name `seq` ()
    rnf (IBCNameHint names) = rnf names `seq` ()
    rnf (IBCLineApp filePath int pTerm) = rnf filePath `seq` rnf int `seq` rnf pTerm `seq` ()
    rnf (IBCErrorHandler name) = rnf name `seq` ()
    rnf (IBCFunctionErrorHandler n1 n2 n3) = rnf n1 `seq` rnf n2 `seq` rnf n3 `seq` ()
    rnf (IBCPostulate name) = rnf name `seq` ()
    rnf (IBCExtern extern) = rnf extern `seq` ()
    rnf (IBCTotCheckErr fc string) = rnf fc `seq` rnf string `seq` ()
    rnf (IBCParsedRegion fc) = rnf fc `seq` ()
    rnf (IBCModDocs name) = rnf name `seq` ()
    rnf (IBCUsage usage) = rnf usage `seq` ()
    rnf (IBCExport name) = rnf name `seq` ()
    rnf (IBCAutoHint n1 n2) = rnf n1 `seq` rnf n2 `seq` ()
    rnf (IBCDeprecate n1 n2) = rnf n1 `seq` rnf n2 `seq` ()
    rnf (IBCRecord x) = rnf x `seq` ()
    rnf (IBCFragile n1 n2) = rnf n1 `seq` rnf n2 `seq` ()


instance NFData a => NFData (D.Block a) where
  rnf (D.Para lines) = rnf lines `seq` ()
  rnf (D.Header i lines) = rnf i `seq` rnf lines `seq` ()
  rnf (D.Blockquote bs) = rnf bs `seq` ()
  rnf (D.List b t xs) = rnf b `seq` rnf t `seq` rnf xs `seq` ()
  rnf (D.CodeBlock attr txt tm) = rnf attr `seq` rnf txt `seq` ()
  rnf (D.HtmlBlock txt) = rnf txt `seq` ()
  rnf D.HRule = ()

instance NFData a => NFData (D.Inline a) where
  rnf (D.Str txt) = rnf txt `seq` ()
  rnf D.Space = ()
  rnf D.SoftBreak = ()
  rnf D.LineBreak = ()
  rnf (D.Emph xs) = rnf xs `seq` ()
  rnf (D.Strong xs) = rnf xs `seq` ()
  rnf (D.Code xs tm) = rnf xs `seq` rnf tm `seq` ()
  rnf (D.Link a b xs) = rnf a `seq` rnf b `seq` rnf xs `seq` ()
  rnf (D.Image a b c) = rnf a `seq` rnf b `seq` rnf c `seq` ()
  rnf (D.Entity a) = rnf a `seq` ()
  rnf (D.RawHtml x) = rnf x `seq` ()

instance NFData CT.ListType where
  rnf (CT.Bullet c) = rnf c `seq` ()
  rnf (CT.Numbered nw i) = rnf nw `seq` rnf i `seq` ()

instance NFData CT.CodeAttr where
  rnf (CT.CodeAttr a b) = rnf a `seq` rnf b `seq` ()

instance NFData CT.NumWrapper where
  rnf CT.PeriodFollowing = ()
  rnf CT.ParenFollowing = ()

instance NFData DocTerm where
        rnf Unchecked = ()
        rnf (Checked x1) = rnf x1 `seq` ()
        rnf (Example x1) = rnf x1 `seq` ()
        rnf (Failing x1) = rnf x1 `seq` ()

-- All generated by 'derive'

instance NFData SizeChange where
        rnf Smaller = ()
        rnf Same = ()
        rnf Bigger = ()
        rnf Unknown = ()

instance NFData FnInfo where
        rnf (FnInfo x1) = rnf x1 `seq` ()

instance NFData Codegen where
        rnf (Via x1) = rnf x1 `seq` ()
        rnf Bytecode = ()

instance NFData LogCat where
       rnf _ = ()

instance NFData CGInfo where
        rnf (CGInfo x1 x2 x3)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` ()

instance NFData Fixity where
        rnf (Infixl x1) = rnf x1 `seq` ()
        rnf (Infixr x1) = rnf x1 `seq` ()
        rnf (InfixN x1) = rnf x1 `seq` ()
        rnf (PrefixN x1) = rnf x1 `seq` ()

instance NFData FixDecl where
        rnf (Fix x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData Static where
        rnf Static = ()
        rnf Dynamic = ()

instance NFData ArgOpt where
        rnf _ = ()

instance NFData Plicity where
        rnf (Imp x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf (Exp x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (Constraint x1 x2)
          = rnf x1 `seq` rnf x2 `seq` ()
        rnf (TacImp x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()

instance NFData FnOpt where
        rnf Inlinable = ()
        rnf TotalFn = ()
        rnf PartialFn = ()
        rnf CoveringFn = ()
        rnf Coinductive = ()
        rnf AssertTotal = ()
        rnf Dictionary = ()
        rnf Implicit = ()
        rnf NoImplicit = ()
        rnf (CExport x1) = rnf x1 `seq` ()
        rnf ErrorHandler = ()
        rnf ErrorReverse = ()
        rnf Reflection = ()
        rnf (Specialise x1) = rnf x1 `seq` ()
        rnf Constructor = ()
        rnf AutoHint = ()
        rnf PEGenerated = ()

instance NFData DataOpt where
        rnf Codata = ()
        rnf DefaultEliminator = ()
        rnf DefaultCaseFun = ()
        rnf DataErrRev = ()

instance (NFData t) => NFData (PDecl' t) where
        rnf (PFix x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PTy x1 x2 x3 x4 x5 x6 x7 x8)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq` rnf x6 `seq` rnf x7 `seq` rnf x8 `seq` ()
        rnf (PPostulate x1 x2 x3 x4 x5 x6 x7 x8)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq` rnf x6 `seq` rnf x7 `seq` rnf x8 `seq` ()
        rnf (PClauses x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PCAF x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PData x1 x2 x3 x4 x5 x6)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` ()
        rnf (PParams x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PNamespace x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PRecord x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq`
                      rnf x6 `seq`
                        rnf x7 `seq`
                          rnf x8 `seq`
                            rnf x9 `seq`
                              rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` ()
        rnf (PClass x1 x2 x3 x4 x5 x6 x8 x7 x9 x10 x11 x12)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq`
                      rnf x6 `seq`
                        rnf x7 `seq`
                          rnf x8 `seq`
                            rnf x9 `seq`
                              rnf x10 `seq`
                                rnf x11 `seq` rnf x12 `seq` ()
        rnf (PInstance x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq`
                      rnf x6 `seq`
                        rnf x7 `seq`
                          rnf x8 `seq`
                            rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13 `seq` ()
        rnf (PDSL x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PSyntax x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PMutual x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PDirective x1) = ()
        rnf (PProvider x1 x2 x3 x4 x5 x6)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq` rnf x6 `seq` ()
        rnf (PTransform x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PRunElabDecl x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` x3 `seq` ()

instance NFData t => NFData (ProvideWhat' t)  where
        rnf (ProvTerm ty tm)   = rnf ty `seq` rnf tm `seq` ()
        rnf (ProvPostulate tm) = rnf tm `seq` ()

instance NFData PunInfo where
        rnf x = x `seq` ()

instance (NFData t) => NFData (PClause' t) where
        rnf (PClause x1 x2 x3 x4 x5 x6)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` ()
        rnf (PWith x1 x2 x3 x4 x5 x6 x7)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7 `seq` ()
        rnf (PClauseR x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PWithR x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()

instance (NFData t) => NFData (PData' t) where
        rnf (PDatadecl x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PLaterdecl x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()

instance NFData PTerm where
        rnf (PQuote x1) = rnf x1 `seq` ()
        rnf (PRef x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` x3 `seq` ()
        rnf (PInferRef x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` x3 `seq` ()
        rnf (PPatvar x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PLam _ x1 x2 x3 x4) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PPi x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf (PLet _ x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf (PTyped x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PAppImpl x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PApp x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PWithApp x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PAppBind x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PMatchApp x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PCase x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PIfThenElse x1 x2 x3 x4) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PTrue x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PResolveTC x1) = rnf x1 `seq` ()
        rnf (PRewrite x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf (PPair x1 x2 x3 x4 x5) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` x5 `seq` ()
        rnf (PDPair x1 x2 x3 x4 x5 x6)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` x6 `seq` ()
        rnf (PAs x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PAlternative x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PHidden x1) = rnf x1 `seq` ()
        rnf (PType fc) = rnf fc `seq` ()
        rnf (PUniverse _) = ()
        rnf (PGoal x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PConstant x1 x2) = x1 `seq` x2 `seq` ()
        rnf Placeholder = ()
        rnf (PDoBlock x1) = rnf x1 `seq` ()
        rnf (PIdiom x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PReturn x1) = rnf x1 `seq` ()
        rnf (PMetavar x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PProof x1) = rnf x1 `seq` ()
        rnf (PTactics x1) = rnf x1 `seq` ()
        rnf (PElabError x1) = rnf x1 `seq` ()
        rnf PImpossible = ()
        rnf (PCoerced x1) = rnf x1 `seq` ()
        rnf (PDisamb x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PUnifyLog x1) = rnf x1 `seq` ()
        rnf (PNoImplicits x1) = rnf x1 `seq` ()
        rnf (PQuasiquote x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (PUnquote x1) = rnf x1 `seq` ()
        rnf (PQuoteName x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PRunElab x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (PConstSugar x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData PAltType where
        rnf (ExactlyOne x1) = rnf x1 `seq` ()
        rnf FirstSuccess = ()
        rnf TryImplicit = ()

instance (NFData t) => NFData (PTactic' t) where
        rnf (Intro x1) = rnf x1 `seq` ()
        rnf Intros = ()
        rnf (Focus x1) = rnf x1 `seq` ()
        rnf (Refine x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (Rewrite x1) = rnf x1 `seq` ()
        rnf DoUnify = ()
        rnf (Induction x1) = rnf x1 `seq` ()
        rnf (CaseTac x1) = rnf x1 `seq` ()
        rnf (Equiv x1) = rnf x1 `seq` ()
        rnf (Claim x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (MatchRefine x1) = rnf x1 `seq` ()
        rnf (LetTac x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (LetTacTy x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (Exact x1) = rnf x1 `seq` ()
        rnf Compute = ()
        rnf Trivial = ()
        rnf TCInstance = ()
        rnf (ProofSearch r r1 r2 x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf Solve = ()
        rnf Attack = ()
        rnf ProofState = ()
        rnf ProofTerm = ()
        rnf Undo = ()
        rnf (Try x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (TSeq x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (ApplyTactic x1) = rnf x1 `seq` ()
        rnf (ByReflection x1) = rnf x1 `seq` ()
        rnf (Reflect x1) = rnf x1 `seq` ()
        rnf (Fill x1) = rnf x1 `seq` ()
        rnf (GoalType x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf Qed = ()
        rnf Abandon = ()
        rnf (TCheck x1) = rnf x1 `seq` ()
        rnf (TEval x1) = rnf x1 `seq` ()
        rnf (TDocStr x1) = x1 `seq` ()
        rnf (TSearch x1) = rnf x1 `seq` ()
        rnf Skip = ()
        rnf (TFail x1) = rnf x1 `seq` ()
        rnf SourceFC = ()
        rnf Unfocus = ()

instance (NFData t) => NFData (PDo' t) where
        rnf (DoExp x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (DoBind x1 x2 x3 x4) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (DoBindP x1 x2 x3 x4) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (DoLet x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf (DoLetP x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()

instance (NFData t) => NFData (PArg' t) where
        rnf (PImp x1 x2 x3 x4 x5)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()
        rnf (PExp x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PConstraint x1 x2 x3 x4)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()
        rnf (PTacImplicit x1 x2 x3 x4 x5)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()

instance NFData ClassInfo where
        rnf (CI x1 x2 x3 x4 x5 x6 x7)
          = rnf x1 `seq`
              rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7 `seq` ()

instance NFData RecordInfo where
        rnf (RI x1 x2 x3)
          = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()

instance NFData OptInfo where
        rnf (Optimise x1 x2)
          = rnf x1 `seq` rnf x2 `seq` ()

instance NFData TypeInfo where
        rnf (TI x1 x2 x3 x4 x5) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()

instance (NFData t) => NFData (DSL' t) where
        rnf (DSL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq`
                      rnf x6 `seq` rnf x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` ()

instance NFData SynContext where
        rnf PatternSyntax = ()
        rnf TermSyntax = ()
        rnf AnySyntax = ()

instance NFData Syntax where
        rnf (Rule x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()
        rnf (DeclRule x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData SSymbol where
        rnf (Keyword x1) = rnf x1 `seq` ()
        rnf (Symbol x1) = rnf x1 `seq` ()
        rnf (Binding x1) = rnf x1 `seq` ()
        rnf (Expr x1) = rnf x1 `seq` ()
        rnf (SimpleExpr x1) = rnf x1 `seq` ()

instance NFData Using where
        rnf (UImplicit x1 x2) = rnf x1 `seq` rnf x2 `seq` ()
        rnf (UConstraint x1 x2) = rnf x1 `seq` rnf x2 `seq` ()

instance NFData SyntaxInfo where
        rnf (Syn x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
          = rnf x1 `seq`
              rnf x2 `seq`
                rnf x3 `seq`
                  rnf x4 `seq`
                    rnf x5 `seq`
                      rnf x6 `seq` rnf x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13 `seq` rnf x14 `seq` ()

instance NFData OutputMode where
  rnf (RawOutput x) = () -- no instance for Handle, so this is a bit wrong
  rnf (IdeMode x y) = rnf x `seq` ()


instance NFData IState where
  rnf (IState x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40
              x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60
              x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76)
     = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7 `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` () `seq` rnf x11 `seq` rnf x12 `seq` rnf x13 `seq` rnf x14 `seq` rnf x15 `seq` rnf x16 `seq` rnf x17 `seq` rnf x18 `seq` rnf x19 `seq` rnf x20 `seq`
       rnf x21 `seq` rnf x22 `seq` rnf x23 `seq` rnf x24 `seq` rnf x25 `seq` rnf x26 `seq` rnf x27 `seq` rnf x28 `seq` rnf x29 `seq` rnf x30 `seq` rnf x31 `seq` rnf x32 `seq` rnf x33 `seq` rnf x34 `seq` rnf x35 `seq` rnf x36 `seq` rnf x37 `seq` rnf x38 `seq` rnf x39 `seq` rnf x40 `seq`
       rnf x41 `seq` rnf x42 `seq` rnf x43 `seq` rnf x44 `seq` rnf x45 `seq` rnf x46 `seq` rnf x47 `seq` rnf x48 `seq` rnf x49 `seq` rnf x50 `seq` rnf x51 `seq` rnf x52 `seq` rnf x53 `seq` rnf x54 `seq` rnf x55 `seq` rnf x56 `seq` rnf x57 `seq` rnf x58 `seq` rnf x59 `seq` rnf x60 `seq`
       rnf x61 `seq` rnf x62 `seq` rnf x63 `seq` rnf x64 `seq` rnf x65 `seq` rnf x66 `seq` rnf x67 `seq` rnf x68 `seq` rnf x69 `seq` rnf x70 `seq` rnf x71 `seq` rnf x72 `seq` rnf x73 `seq` rnf x74 `seq` rnf x75 `seq` rnf x76 `seq` ()
