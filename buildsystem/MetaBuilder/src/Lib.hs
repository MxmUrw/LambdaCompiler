module Lib
  ( Collection(..)
  , AgdaProjectConfig(..)
  , HaskellStackProjectConfig(..)
  , GlobalConfig(..)
  , build
  )
  where

import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util

import Control.Exception
import Control.Monad

import Data.Typeable
-- import Data.Text
-- import qualified Data.Text.IO as TIO

import System.Directory
import System.FilePath.Find as FP


(.>) :: a -> (a -> b) -> b
(.>) x f = f x
infixl 9 .>

data MBException
  = CouldNotFindRootFile
  | FoundMultipleRootFiles
  deriving (Typeable)

instance Show MBException where
  show CouldNotFindRootFile   = "Error: Could not find a .metabuild-root file."
  show FoundMultipleRootFiles = "Error: Found multiple .metabuild-root files in same directory."

instance Exception MBException

filterRoot :: FilePath -> Bool
filterRoot file = takeExtension file == ".metabuild-root"

findProjectRootFile_impl :: FilePath -> IO FilePath
findProjectRootFile_impl cur_dir = do
  -- roots <- FP.find (return False) (do
  --                               ext <- extension
  --                               return (ext == ".metabuild-root")) cur_dir

  -- roots <- FP.find (return True) (return True) cur_dir
  files <- listDirectory cur_dir
  let filtered = filter filterRoot files
  case filtered of
    [] -> let parent = takeDirectory cur_dir
          in if (isDrive cur_dir || parent == cur_dir)
             then (throw CouldNotFindRootFile)
             else (findProjectRootFile_impl parent)
    [x] -> (return (cur_dir </> x))
    x:xs -> throw (FoundMultipleRootFiles)

findProjectRootFile :: IO FilePath
findProjectRootFile = do
  getCurrentDirectory >>= findProjectRootFile_impl

findProjectRoot :: IO FilePath
findProjectRoot = takeDirectory <$> findProjectRootFile

data AgdaProjectConfig = AgdaProjectConfig
  -- all paths should be relative
  { sourceRelDir               :: FilePath
  , mainRelFile                :: FilePath
  , agdaBin_RelFile            :: String
  , haskellStackTemplateRelDir :: FilePath
  , agdaAutobuild              :: Bool
  }

data ExtraAgdaProjectConfig = ExtraAgdaProjectConfig
  -- absolute versions of paths in `AgdaProjectConfig`
  { transpilationSource_AbDir         :: FilePath
  , transpilationTarget_AbDir         :: FilePath
  , agdaTarget_AbDir                  :: FilePath
  , agdaBin_AbFile                    :: FilePath
  , mainTranspilationSource_AbFile    :: FilePath
  -- derived paths
  , haskellStack_TemplateSource_AbDir :: FilePath
  , haskellStack_TemplateTarget_AbDir :: FilePath
  -- fixed paths
  , ghcshim_AbFile                    :: FilePath
  -- original settings
  , originalAgdaConfig                :: AgdaProjectConfig
  }

data HaskellStackProjectConfig = HaskellStackProjectConfig
  { haskellStackBin_RelFile   :: FilePath
  , haskellStackSource_RelDir :: FilePath
  , haskellStackAutobuild     :: Bool
  }

data ExtraHaskellStackProjectConfig = ExtraHaskellStackProjectConfig
  { haskellStackBin_AbFile     :: FilePath
  , haskellStackSource_AbDir   :: FilePath
  -- original settings
  , originalHaskellStackConfig :: HaskellStackProjectConfig
  }

data GlobalConfig = GlobalConfig
  { buildRelDir      :: FilePath
  , binRelDir        :: FilePath
  }

data ExtraGlobalConfig = ExtraGlobalConfig
  { rootAbDir            :: FilePath
  , buildAbDir           :: FilePath
  , binAbDir             :: FilePath
  }

data Collection = Collection
  { globalConfig         :: GlobalConfig
  , agdaProject          :: AgdaProjectConfig
  , haskellStackProjects :: [HaskellStackProjectConfig]
  }

data ExtraCollection = ExtraCollection
  { extraGlobalConfig         :: ExtraGlobalConfig
  , extraAgdaProject          :: ExtraAgdaProjectConfig
  , extraHaskellStackProjects :: [ExtraHaskellStackProjectConfig]
  }



deriveExtraProjectConfig_Agda :: ExtraGlobalConfig -> AgdaProjectConfig -> ExtraAgdaProjectConfig
deriveExtraProjectConfig_Agda egpc ap =
  ExtraAgdaProjectConfig
  -- sources:
  { transpilationSource_AbDir         = egpc.>rootAbDir </> ap.>sourceRelDir
  , mainTranspilationSource_AbFile    = egpc.>rootAbDir </> ap.>sourceRelDir </> ap.>mainRelFile
  , haskellStack_TemplateSource_AbDir = egpc.>rootAbDir </> ap.>haskellStackTemplateRelDir
  -- targets:
  , agdaTarget_AbDir                  = egpc.>buildAbDir </> ap.>haskellStackTemplateRelDir </> "src"
  , transpilationTarget_AbDir         = egpc.>buildAbDir </> ap.>haskellStackTemplateRelDir </> "src" </> "MAlonzo" </> "Code"
  , haskellStack_TemplateTarget_AbDir = egpc.>buildAbDir </> ap.>haskellStackTemplateRelDir
  , agdaBin_AbFile                    = egpc.>binAbDir </> ap.>agdaBin_RelFile <.> exe
  -- fixed paths:
  , ghcshim_AbFile                    = egpc.>buildAbDir </> "ghcshim" </> "ghc"
  , originalAgdaConfig                = ap
  }

deriveExtraProjectConfig_HaskellStack :: ExtraGlobalConfig -> HaskellStackProjectConfig -> ExtraHaskellStackProjectConfig
deriveExtraProjectConfig_HaskellStack egpc hpc =
  let haskellStackBin_AbFile   = egpc.>binAbDir </> hpc.>haskellStackBin_RelFile <.> exe
      haskellStackSource_AbDir = egpc.>rootAbDir </> hpc.>haskellStackSource_RelDir
  in ExtraHaskellStackProjectConfig
     { haskellStackBin_AbFile     = haskellStackBin_AbFile
     , haskellStackSource_AbDir    = haskellStackSource_AbDir
     , originalHaskellStackConfig  = hpc
     }

deriveExtraProjectConfig_Global :: FilePath -> GlobalConfig -> ExtraGlobalConfig
deriveExtraProjectConfig_Global root gpc =
  let buildAbDir = root </> gpc.>buildRelDir
      binAbDir   = root </> gpc.>binRelDir
  in ExtraGlobalConfig
     { rootAbDir  = root
     , buildAbDir = buildAbDir
     , binAbDir   = binAbDir
     }
-- deriveExtraProjectConfig :: FilePath -> ProjectConfig -> ExtraProjectConfig
-- deriveExtraProjectConfig root pc =
--   let buildAbDir = root </> pc.>buildRelDir
--       binAbDir   = root </> pc.>binRelDir

--       extraAgdaProject = deriveExtraProjectConfig_Agda root (pc.>agdaProject)

--   in ExtraProjectConfig
--      { buildAbDir       = buildAbDir
--      , binAbDir         = binAbDir
--      , extraAgdaProject = extraAgdaProject
--      }

deriveExtraCollection :: FilePath -> Collection -> ExtraCollection
deriveExtraCollection root c =
  let extraGlobalConfig = deriveExtraProjectConfig_Global root (c.>globalConfig)
      extraAgdaProject  = deriveExtraProjectConfig_Agda extraGlobalConfig (c.>agdaProject)
      extraHaskellStackProjects = deriveExtraProjectConfig_HaskellStack extraGlobalConfig <$> (c.>haskellStackProjects)
  in ExtraCollection
     { extraGlobalConfig         = extraGlobalConfig
     , extraAgdaProject          = extraAgdaProject
     , extraHaskellStackProjects = extraHaskellStackProjects
     }

makeRules_HaskellStackProject :: ExtraGlobalConfig -> ExtraHaskellStackProjectConfig -> Rules ()
makeRules_HaskellStackProject egpc ehc = do
  if (ehc.>originalHaskellStackConfig.>haskellStackAutobuild)
    then want [ehc.>haskellStackBin_AbFile]
    else return ()

  phony (ehc.>originalHaskellStackConfig.>haskellStackBin_RelFile) $ do
    need [ehc.>haskellStackBin_AbFile]

  haskellStack_Files <- liftIO $ getDirectoryFilesIO (ehc.>haskellStackSource_AbDir) ["//*.hs", "//*.yaml", "//*.cabal"]
  let haskellStackSource_Files = ((ehc.>haskellStackSource_AbDir </>) <$> haskellStack_Files)

  ehc.>haskellStackBin_AbFile %> \_ -> do
    need haskellStackSource_Files
    cmd_ "stack" (Cwd (ehc.>haskellStackSource_AbDir)) ["install", "--local-bin-path=" ++ egpc.>binAbDir]


makeRules_AgdaProject :: ExtraGlobalConfig -> ExtraAgdaProjectConfig -> Rules ()
makeRules_AgdaProject egpc eapc = do
  if (eapc.>originalAgdaConfig.>agdaAutobuild)
    then want [eapc.>agdaBin_AbFile]
    else return ()

  phony (eapc.>originalAgdaConfig.>agdaBin_RelFile) $ do
    need [eapc.>agdaBin_AbFile]

  haskellStack_Template_Files <- liftIO $ getDirectoryFilesIO (eapc.>haskellStack_TemplateSource_AbDir) ["//*.hs", "//*.yaml"]
  let filtered_haskellStack_Template_Files = filter (\f -> not (elem ".stack-work" (splitDirectories f))) haskellStack_Template_Files
  let haskellStack_TemplateSource_Files = ((eapc.>haskellStack_TemplateSource_AbDir </>) <$> filtered_haskellStack_Template_Files)
  let haskellStack_TemplateTarget_Files = ((eapc.>haskellStack_TemplateTarget_AbDir </>) <$> filtered_haskellStack_Template_Files)

  transpilation_Files <- liftIO $ getDirectoryFilesIO (eapc.>transpilationSource_AbDir) ["//*.agda"]
  let transpilationSource_Files = ((\f -> eapc.>transpilationSource_AbDir </> f)            <$> transpilation_Files)
  let transpilationTarget_Files = ((\f -> eapc.>transpilationTarget_AbDir </> f -<.> ".hs") <$> transpilation_Files)

  eapc.>agdaBin_AbFile %> \a -> do
    -- _ <- getDirectoryFiles (eapc.>haskellStack_TemplateSource_AbDir) ["//*.hs", "//*.yaml"] -- needed for tracking the file list
    need (transpilationTarget_Files ++ haskellStack_TemplateTarget_Files)
    cmd_ "stack" (Cwd (eapc.>haskellStack_TemplateTarget_AbDir)) ["install", "--local-bin-path=" ++ egpc.>binAbDir]

  transpilationTarget_Files &%> \files -> do
    -- _ <- getDirectoryFiles (eapc.>transpilationSource_AbDir) ["//*.agda"] -- needed for tracking the file list
    need transpilationSource_Files
    need [eapc.>ghcshim_AbFile]
    let ghc_shimpath = takeDirectory (eapc.>ghcshim_AbFile)
    cmd_ "agda" (AddPath [ghc_shimpath] []) ["--compile", "--compile-dir=" ++ eapc.>agdaTarget_AbDir, eapc.>mainTranspilationSource_AbFile]

  (eapc.>haskellStack_TemplateTarget_AbDir ++ "//*") %> \file -> do
    let relfile = makeRelative (eapc.>haskellStack_TemplateTarget_AbDir) file
    let sourceFile = eapc.>haskellStack_TemplateSource_AbDir </> relfile
    let targetFile = eapc.>haskellStack_TemplateTarget_AbDir </> relfile
    putInfo $ "Copying " ++ relfile ++ " from " ++ eapc.>haskellStack_TemplateSource_AbDir
    copyFile' sourceFile targetFile

  (eapc.>ghcshim_AbFile) %> \file -> do
    putInfo "Generating ghc shim"
    liftIO $ writeFile file "#!/bin/bash"
    perm <- liftIO $ getPermissions file
    let perm2 = setOwnerExecutable True perm
    liftIO $ setPermissions file perm2

makeRules_Clean :: ExtraGlobalConfig -> Rules ()
makeRules_Clean epc = do
  phony "clean" $ do
    putInfo $ "Cleaning files in " ++ epc.>buildAbDir
    removeFilesAfter (epc.>buildAbDir) ["//*"]
    putInfo $ "Cleaning files in " ++ epc.>binAbDir
    removeFilesAfter (epc.>binAbDir) ["//*"]


build :: Collection -> IO ()
build c = do

  root <- findProjectRoot
  let ec = deriveExtraCollection root c

  shakeArgs shakeOptions{shakeFiles=ec.>extraGlobalConfig.>buildAbDir} $ do
    makeRules_AgdaProject (ec.>extraGlobalConfig) (ec.>extraAgdaProject)
    mapM_ (makeRules_HaskellStackProject (ec.>extraGlobalConfig)) (ec.>extraHaskellStackProjects)
    makeRules_Clean (ec.>extraGlobalConfig)


