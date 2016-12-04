{-|
Module      : Idris.Package.Common
Description : Data structures common to all `iPKG` file formats.
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Package.Common where

import Idris.AbsSyntaxTree (Opt(..))
import Idris.Core.TT (Name)

-- | Description of an Idris package.
data PkgDesc = PkgDesc {
    pkgname       :: String       -- ^ Name associated with a package.
  , pkgdeps       :: [String]     -- ^ List of packages this package depends on.
  , pkgbrief      :: Maybe String -- ^ Brief description of the package.
  , pkgversion    :: Maybe String -- ^ Version string to associate with the package.
  , pkgreadme     :: Maybe String -- ^ Location of the README file.
  , pkglicense    :: Maybe String -- ^ Description of the licensing information.
  , pkgauthor     :: Maybe String -- ^ Author information.
  , pkgmaintainer :: Maybe String -- ^ Maintainer information.
  , pkghomepage   :: Maybe String -- ^ Website associated with the package.
  , pkgsourceloc  :: Maybe String -- ^ Location of the source files.
  , pkgbugtracker :: Maybe String -- ^ Location of the project's bug tracker.
  , libdeps       :: [String]     -- ^ External dependencies.
  , objs          :: [String]     -- ^ Object files required by the package.
  , makefile      :: Maybe String -- ^ Makefile used to build external code. Used as part of the FFI process.
  , idris_opts    :: [Opt]        -- ^ List of options to give the compiler.
  , sourcedir     :: String       -- ^ Source directory for Idris files.
  , modules       :: [Name]       -- ^ Modules provided by the package.
  , idris_main    :: Maybe Name   -- ^ If an executable in which module can the Main namespace and function be found.
  , execout       :: Maybe String -- ^ What to call the executable.
  , idris_tests   :: [Name]       -- ^ Lists of tests to execute against the package.
  } deriving (Show)

-- | Default settings for package descriptions.
defaultPkg :: PkgDesc
defaultPkg = PkgDesc "" [] Nothing Nothing Nothing Nothing
                        Nothing Nothing Nothing Nothing
                        Nothing [] [] Nothing [] "" [] Nothing Nothing []
