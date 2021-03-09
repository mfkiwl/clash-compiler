{-|
  Copyright   :  (C) 2012-2016, University of Twente,
                     2016-2017, Myrtle Software Ltd,
                     2017     , QBayLogic, Google Inc.
                     2020       QBayLogic

  License     :  BSD2 (see the file LICENSE)
  Maintainer  :  QBayLogic B.V. <devops@qbaylogic.com>

  Module that connects all the parts of the Clash compiler library
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Clash.Driver where

import qualified Control.Concurrent.Supply        as Supply
import           Control.DeepSeq
import           Control.Exception                (throw)
import           Control.Lens                     (view, _4)
import qualified Control.Monad                    as Monad
import           Control.Monad                    (unless, foldM, forM, filterM)
import           Control.Monad.Catch              (MonadMask)
import           Control.Monad.Extra              (whenM, ifM, unlessM)
import           Control.Monad.IO.Class           (MonadIO)
import           Control.Monad.State              (evalState, get)
import           Control.Monad.State.Strict       (State)
import qualified Control.Monad.State.Strict       as State
import qualified Crypto.Hash.SHA256               as Sha256
import           Data.ByteString                  (ByteString)
import qualified Data.ByteString                  as ByteString
import qualified Data.ByteString.Lazy             as ByteStringLazy
import qualified Data.ByteString.Lazy.Char8       as ByteStringLazyChar8
import           Data.Char                        (isAscii, isAlphaNum)
import           Data.Coerce                      (coerce)
import           Data.Default
import           Data.Hashable                    (hash)
import           Data.HashMap.Strict              (HashMap)
import qualified Data.HashMap.Strict              as HashMap
import qualified Data.HashSet                     as HashSet
import           Data.Proxy                       (Proxy(..))
import           Data.IntMap                      (IntMap)
import           Data.List                        (intercalate)
import           Data.Maybe                       (fromMaybe, maybeToList)
import           Data.Semigroup.Monad
import qualified Data.Text
import           Data.Text.Lazy                   (Text)
import qualified Data.Text.Lazy                   as Text
import           Data.Text.Lazy.Encoding          as Text
import qualified Data.Text.Lazy.IO                as Text
import           Data.Text.Prettyprint.Doc.Extra
  (Doc, LayoutOptions (..), PageWidth (..) , layoutPretty, renderLazy)
import qualified Data.Time.Clock                  as Clock
import qualified Language.Haskell.Interpreter     as Hint
import qualified Language.Haskell.Interpreter.Extension as Hint
import qualified Language.Haskell.Interpreter.Unsafe as Hint
import qualified System.Directory                 as Directory
import           System.Directory
  (doesPathExist, listDirectory, doesDirectoryExist, createDirectoryIfMissing,
   removeDirectoryRecursive, doesFileExist)
import           System.Environment               (getExecutablePath)
import           System.FilePath                  ((</>), (<.>), takeDirectory, takeFileName, isAbsolute)
import qualified System.FilePath                  as FilePath
import qualified System.IO                        as IO
import           System.IO.Temp
  (getCanonicalTemporaryDirectory, withTempDirectory)
import           Text.Trifecta.Result
  (Result(Success, Failure), _errDoc)

#if MIN_VERSION_ghc(9,0,0)
import           GHC.Builtin.Names                 (eqTyConKey, ipClassKey)
import           GHC.Types.Unique                  (getKey)

import           GHC.Types.SrcLoc                  (SrcSpan)
#else
import           PrelNames               (eqTyConKey, ipClassKey)
import           Unique                  (getKey)

import           SrcLoc                           (SrcSpan)
#endif
import           GHC.BasicTypes.Extra             ()

import           Clash.Annotations.Primitive
  (HDL (..))
import           Clash.Annotations.BitRepresentation.Internal
  (CustomReprs)
import           Clash.Annotations.TopEntity
  (TopEntity (..), PortName(PortName, PortProduct))
import           Clash.Annotations.TopEntity.Extra ()
import           Clash.Backend

#if EXPERIMENTAL_EVALUATOR
import           Clash.Core.PartialEval           (Evaluator)
#else
import           Clash.Core.Evaluator.Types       (Evaluator)
#endif

import           Clash.Core.Name                  (Name (..))
import           Clash.Core.Pretty                (PrettyOptions(..), showPpr')
import           Clash.Core.Type
  (Type(ForAllTy, LitTy, AnnType), TypeView(..), tyView, mkFunTy, LitTy(SymTy))
import           Clash.Core.TyCon                 (TyConMap, TyConName)
import           Clash.Core.Util                  (shouldSplit)
import           Clash.Core.Var
  (Id, varName, varUniq, varType)
import           Clash.Core.VarEnv
  (VarEnv, elemVarEnv, eltsVarEnv, emptyVarEnv, lookupVarEnv, lookupVarEnv', mkVarEnv)
import           Clash.Debug                      (debugIsOn)
import           Clash.Driver.Types
import           Clash.Driver.Manifest            (Manifest(..), readFreshManifest, UnexpectedModification, pprintUnexpectedModifications, mkManifest, writeManifest, manifestFilename)
import           Clash.Edalize.Edam
import           Clash.Netlist                    (genNetlist, genTopNames)
import           Clash.Netlist.BlackBox.Parser    (runParse)
import           Clash.Netlist.BlackBox.Types     (BlackBoxTemplate, BlackBoxFunction)
import qualified Clash.Netlist.Id                 as Id
import           Clash.Netlist.Types
  (IdentifierText, BlackBox (..), Component (..), FilteredHWType, HWMap, SomeBackend (..),
   TopEntityT(..), TemplateFunction, findClocks)
import           Clash.Normalize                  (checkNonRecursive, cleanupGraph,
                                                   normalize, runNormalization)
import           Clash.Normalize.Util             (callGraph, tvSubstWithTyEq)
import qualified Clash.Primitives.Sized.ToInteger as P
import qualified Clash.Primitives.Sized.Vector    as P
import qualified Clash.Primitives.GHC.Int         as P
import qualified Clash.Primitives.GHC.Word        as P
import qualified Clash.Primitives.Intel.ClockGen  as P
import qualified Clash.Primitives.Verification    as P
import           Clash.Primitives.Types
import           Clash.Signal.Internal
import           Clash.Unique                     (Unique)
import           Clash.Util.Interpolate           (i)
import           Clash.Util
  (ClashException(..), HasCallStack, first, reportTimeDiff,
   wantedLanguageExtensions, unwantedLanguageExtensions, curLoc)
import           Clash.Util.Graph                 (reverseTopSort)
import qualified Clash.Util.Interpolate           as I

-- | Worker function of 'splitTopEntityT'
splitTopAnn
  :: TyConMap
  -> SrcSpan
  -- ^ Source location of top entity (for error reporting)
  -> Type
  -- ^ Top entity body
  -> TopEntity
  -- ^ Port annotations for top entity
  -> TopEntity
  -- ^ New top entity with split ports (or the old one if not applicable)
splitTopAnn tcm sp typ@(tyView -> FunTy {}) t@Synthesize{t_inputs} =
  t{t_inputs=go typ t_inputs}
 where
  go :: Type -> [PortName] -> [PortName]
  go _ [] = []
  go (tyView -> FunTy a res) (p:ps)
   | shouldNotHavePortName a
     -- Insert dummy PortName for args for which the user shouldn't have
     -- to provide a name.
     -- Ideally this would be any (non Hidden{Clock,Reset,Enable}) constraint.
     -- But because we can't properly detect constraints,
     -- we only skip some specific one. see "shouldNotHavePortName"
     = PortName "" : go res (p:ps)
   | otherwise =
    case shouldSplit tcm a of
      Just (_,argTys@(_:_:_)) ->
        -- Port must be split up into 'n' pieces.. can it?
        case p of
          PortProduct nm portNames0 ->
            let
              n = length argTys
              newPortNames = map (PortName . show) [(0::Int)..]
              portNames1 = map (prependName nm) (portNames0 ++ newPortNames)
              newLam = foldr1 mkFunTy (argTys ++ [res])
            in
              go newLam (take n portNames1 ++ ps)
          PortName nm ->
            throw (flip (ClashException sp) Nothing $ [i|
              Couldn't separate clock, reset, or enable from a product type due
              to a malformed Synthesize annotation. All clocks, resets, and
              enables should be given a unique port name. Type to be split:

                #{showPpr' (PrettyOptions False True False False) a}

              Given port annotation: #{p}. You might want to use the
              following instead: PortProduct #{show nm} []. This allows Clash to
              autogenerate names based on the name #{show nm}.
            |])
      _ ->
        -- No need to split the port, carrying on..
        p : go res ps
  go (ForAllTy _tyVar ty) ps = go ty ps
  go _ty ps = ps

  prependName :: String -> PortName -> PortName
  prependName "" pn = pn
  prependName p (PortProduct nm ps) = PortProduct (p ++ "_" ++ nm) ps
  prependName p (PortName nm) = PortName (p ++ "_" ++ nm)

  -- Returns True for
  --   * type equality constraints (~)
  --   * HasCallStack
  shouldNotHavePortName :: Type -> Bool
  shouldNotHavePortName (tyView -> TyConApp (nameUniq -> tcUniq) tcArgs)
    | tcUniq == getKey eqTyConKey = True
    | tcUniq == getKey ipClassKey
    , [LitTy (SymTy "callStack"), _] <- tcArgs = True
  shouldNotHavePortName _ = False

splitTopAnn tcm sp (ForAllTy _tyVar typ) t = splitTopAnn tcm sp typ t
splitTopAnn tcm sp (AnnType _anns typ) t = splitTopAnn tcm sp typ t
splitTopAnn _tcm _sp _typ t = t

-- When splitting up a single argument into multiple arguments (see docs of
-- 'separateArguments') we should make sure to update TopEntity annotations
-- accordingly. See: https://github.com/clash-lang/clash-compiler/issues/1033
splitTopEntityT
  :: HasCallStack
  => TyConMap
  -> BindingMap
  -> TopEntityT
  -> TopEntityT
splitTopEntityT tcm bindingsMap tt@(TopEntityT id_ (Just t@(Synthesize {})) _) =
  case lookupVarEnv id_ bindingsMap of
    Just (Binding _id sp _ _ _) ->
      tt{topAnnotation=Just (splitTopAnn tcm sp (varType id_) t)}
    Nothing ->
      error "Internal error in 'splitTopEntityT'. Please report as a bug."
splitTopEntityT _ _ t = t

-- | Remove constraints such as 'a ~ 3'.
removeForAll :: TopEntityT -> TopEntityT
removeForAll (TopEntityT var annM isTb) =
  TopEntityT var{varType=tvSubstWithTyEq (varType var)} annM isTb

-- | Given a list of all found top entities and _maybe_ a top entity (+dependencies)
-- passed in by '-main-is', return the list of top entities Clash needs to
-- compile.
selectTopEntities :: [TopEntityT] -> Maybe (TopEntityT, [TopEntityT]) -> [TopEntityT]
selectTopEntities topEntities mainTopEntity =
  maybe topEntities (uncurry (:)) mainTopEntity

-- | Get modification data of current clash binary.
getClashModificationDate :: IO Clock.UTCTime
getClashModificationDate = Directory.getModificationTime =<< getExecutablePath

hdlFromBackend :: forall backend. Backend backend => Proxy backend -> HDL
hdlFromBackend _ = hdlKind (undefined :: backend)

replaceChar :: Char -> Char -> String -> String
replaceChar a b = map go
 where
  go c
    | c == a = b
    | otherwise = c

-- | Create a set of target HDL files for a set of functions
generateHDL
  :: forall backend . Backend backend
  => CustomReprs
  -> HashMap Data.Text.Text VDomainConfiguration
  -- ^ Known domains to configurations
  -> BindingMap
  -- ^ Set of functions
  -> Maybe backend
  -> CompiledPrimMap
  -- ^ Primitive / BlackBox Definitions
  -> TyConMap
  -- ^ TyCon cache
  -> IntMap TyConName
  -- ^ Tuple TyCon cache
  -> (CustomReprs -> TyConMap -> Type ->
      State HWMap (Maybe (Either String FilteredHWType)))
  -- ^ Hardcoded 'Type' -> 'HWType' translator
  -> Evaluator
  -- ^ Hardcoded evaluator for partial evaluation
  -> [TopEntityT]
  -- ^ All topentities
  -> Maybe (TopEntityT, [TopEntityT])
  -- ^ Main top entity to compile. If Nothing, all top entities in previous
  -- argument will be compiled.
  -> ClashOpts
  -- ^ Debug information level for the normalization process
  -> (Clock.UTCTime,Clock.UTCTime)
  -> IO ()
generateHDL reprs domainConfs bindingsMap hdlState primMap tcm tupTcm typeTrans eval
  topEntities0 mainTopEntity opts (startTime,prepTime) = do
    case opt_dbgRewriteHistoryFile opts of
      Nothing -> pure ()
      Just histFile -> whenM (Directory.doesFileExist histFile) (Directory.removeFile histFile)
    let (tes, deps) = sortTop bindingsMap topEntities1
     in go prepTime initIs HashMap.empty deps tes
 where
  (compNames, initIs) = genTopNames topPrefixM escpIds lwIds hdl topEntities1
  topEntityMap = mkVarEnv (fmap (\x -> (topId x, x)) topEntities1)
  topPrefixM = opt_componentPrefix opts
  hdl = hdlFromBackend (Proxy @backend)
  escpIds = opt_escapedIds opts
  lwIds = opt_lowerCaseBasicIds opts
  topEntities1 =
    map
      (removeForAll . splitTopEntityT tcm bindingsMap)
      (selectTopEntities topEntities0 mainTopEntity)

  go
    :: Clock.UTCTime
    -> Id.IdentifierSet
    -> HashMap Unique [EdamFile]
    -> HashMap Unique [Unique]
    -> [TopEntityT]
    -> IO ()
  go prevTime _ _ _ [] =
    putStrLn $ "Clash: Total compilation took " ++ reportTimeDiff prevTime startTime

  -- Process the next TopEntity
  go prevTime seen0 edamFiles0 deps (TopEntityT topEntity annM isTb:topEntities') = do
  let topEntityS = Data.Text.unpack (nameOcc (varName topEntity))
  putStrLn $ "Clash: Compiling " ++ topEntityS

  -- Some initial setup
  let -- TODO: 'modName1' should be run through 'seen0'
      modName1 = filter (\c -> isAscii c && (isAlphaNum c || c == '_')) (replaceChar '.' '_' topEntityS)
      topNm = lookupVarEnv' compNames topEntity
      (modNameS, fmap Data.Text.pack -> prefixM) = case topPrefixM of
        Just (Data.Text.unpack -> p)
          | not (null p) -> case annM of
            -- Prefix top names with 'p', prefix other with 'p_tname'
            Just ann ->
              let nm = p <> "_" <> t_name ann in
              (nm, Just nm)
            -- Prefix top names with 'p', prefix other with 'p'
            _ -> (p <> "_" <> modName1, Just p)
          | Just ann <- annM -> case hdl of
              -- Prefix other with 't_name'
              VHDL -> (t_name ann, Just modNameS)
              _    -> (t_name ann, Nothing)
        _ -> case annM of
          Just ann -> case hdlKind (undefined :: backend) of
            VHDL -> (t_name ann, Nothing)
            -- Prefix other with 't_name'
            _ -> (t_name ann, Just modNameS)
          _ -> (modName1, Nothing)
      modNameT  = Data.Text.pack modNameS
      iw        = opt_intWidth opts
      hdlsyn    = opt_hdlSyn opts
      forceUnd  = opt_forceUndefined opts
      xOpt      = coerce (opt_aggressiveXOptBB opts)
      hdlState' = setModName modNameT
                $ fromMaybe (initBackend iw hdlsyn escpIds lwIds forceUnd xOpt :: backend) hdlState
      hdlDir    = fromMaybe (Clash.Backend.name hdlState') (opt_hdlDir opts) </> topEntityS
      manPath   = hdlDir </> manifestFilename
      ite       = ifThenElseExpr hdlState'
      topNmT    = Id.toText topNm

  unless (opt_cachehdl opts) $ putStrLn "Clash: Ignoring previously made caches"

  -- Get manifest file if cache is not stale and caching is enabled. This is used
  -- to prevent unnecessary recompilation.
  clashModDate <- getClashModificationDate
  (userModifications, maybeManifest, topHash) <-
    readFreshManifest topEntities0 (bindingsMap, topEntity) primMap opts clashModDate manPath

  supplyN <- Supply.newSupply
  let topEntityNames = map topId topEntities1

  (topTime, seen2, edamFiles2) <- case maybeManifest of
    Just manifest0@Manifest{fileNames} | Just [] <- userModifications -> do
      -- Found a 'manifest' files. Use it to extend "seen" set. Generate EDAM
      -- files if necessary.
      putStrLn ("Clash: Using cached result for: " ++ topEntityS)
      topTime <- Clock.getCurrentTime
      let seen1 = State.execState (mapM_ Id.addRaw (componentNames manifest0)) seen0

      (edamFiles1, fileNames1) <-
        if opt_edalize opts
        then writeEdam hdlDir (topNm, varUniq topEntity) deps edamFiles0 fileNames
        else pure (edamFiles0, fileNames)

      writeManifest manPath manifest0{fileNames=fileNames1}

      return
        ( topTime
        , seen1
        , edamFiles1
        )

    _ -> do
      -- 1. Prepare HDL directory
      --
      -- [Note] Create HDL dir before netlist generation
      --
      -- Already create the directory where the HDL ends up being generated, as
      -- we use directories relative to this final directory to find manifest
      -- files belonging to other top entities. Failing to do so leads to #463
      () <- prepareDir hdlDir opts userModifications

      -- 2. Normalize topEntity
      let transformedBindings = normalizeEntity reprs bindingsMap primMap tcm tupTcm
                                  typeTrans eval topEntityNames opts supplyN
                                  topEntity

      normTime <- transformedBindings `deepseq` Clock.getCurrentTime
      let prepNormDiff = reportTimeDiff normTime prevTime
      putStrLn $ "Clash: Normalization took " ++ prepNormDiff

      -- 3. Generate netlist for topEntity
      (topComponent, netlist, seen2) <-
        genNetlist isTb opts reprs transformedBindings topEntityMap compNames primMap
                   tcm typeTrans iw ite (SomeBackend hdlState') seen0 hdlDir prefixM topEntity

      netlistTime <- netlist `deepseq` Clock.getCurrentTime
      let normNetDiff = reportTimeDiff netlistTime normTime
      putStrLn $ "Clash: Netlist generation took " ++ normNetDiff

      -- 4. Generate topEntity wrapper
      let
        (hdlDocs, dfiles, mfiles) =
          createHDL hdlState' modNameT seen2 netlist domainConfs topComponent topNmT

      -- TODO: Data files should go into their own directory
      -- FIXME: Files can silently overwrite each other
      hdlDocDigests <- mapM (writeHDL hdlDir) hdlDocs
      dataFilesDigests <- copyDataFiles (opt_importPaths opts) hdlDir dfiles
      memoryFilesDigests <- writeMemoryDataFiles hdlDir mfiles

      let
        components = map (view _4) (eltsVarEnv netlist)
        filesAndDigests0 =
             zip (map fst hdlDocs) hdlDocDigests
          <> zip (map snd dfiles) dataFilesDigests
          <> zip (map fst mfiles) memoryFilesDigests

      (edamFiles1, filesAndDigests1) <-
        if opt_edalize opts
        then writeEdam hdlDir (topNm, varUniq topEntity) deps edamFiles0 filesAndDigests0
        else pure (edamFiles0, filesAndDigests0)

      let manifest = mkManifest opts topComponent components filesAndDigests1 topHash
      writeManifest manPath manifest

      topTime <- hdlDocs `seq` Clock.getCurrentTime
      return (topTime, seen2, edamFiles1)

  go topTime seen2 edamFiles2 deps topEntities'

-- | Interpret a specific function from a specific module. This action tries
-- two things:
--
--   1. Interpret without explicitly loading the module. This will succeed if
--      the module was already loaded through a package database (set using
--      'interpreterArgs').
--
--   2. If (1) fails, it does try to load it explicitly. If this also fails,
--      an error is returned.
--
loadImportAndInterpret
  :: (MonadIO m, MonadMask m)
  => [String]
  -- ^ Extra search path (usually passed as -i)
  -> [String]
  -- ^ Interpreter args
  -> String
  -- ^ The folder in which the GHC bootstrap libraries (base, containers, etc.)
  -- can be found
  -> Hint.ModuleName
  -- ^ Module function lives in
  -> String
  -- ^ Function name
  -> String
  -- ^ Type name ('BlackBoxFunction' or 'TemplateFunction')
  -> m (Either Hint.InterpreterError a)
loadImportAndInterpret iPaths0 interpreterArgs topDir qualMod funcName typ = do
  Hint.liftIO $ Monad.when debugIsOn $
    putStr "Hint: Interpreting " >> putStrLn (qualMod ++ "." ++ funcName)
  -- Try to interpret function *without* loading module explicitly. If this
  -- succeeds, the module was already in the global package database(s).
  bbfE <- Hint.unsafeRunInterpreterWithArgsLibdir interpreterArgs topDir $ do
    iPaths1 <- (++iPaths0) <$> Hint.get Hint.searchPath
    Hint.set [Hint.searchPath Hint.:= iPaths1]
    Hint.setImports [ "Clash.Netlist.Types", "Clash.Netlist.BlackBox.Types", qualMod]
    Hint.unsafeInterpret funcName typ

  case bbfE of
    Left _ -> do
      -- Try to interpret module as a local module, not yet present in the
      -- global package database(s).
      Hint.unsafeRunInterpreterWithArgsLibdir interpreterArgs topDir $ do
        Hint.reset
        iPaths1 <- (iPaths0++) <$> Hint.get Hint.searchPath
        Hint.set [ Hint.searchPath Hint.:= iPaths1
                 , Hint.languageExtensions Hint.:= langExts]
        Hint.loadModules [qualMod]
        Hint.setImports [ "Clash.Netlist.BlackBox.Types", "Clash.Netlist.Types", qualMod]
        Hint.unsafeInterpret funcName typ
    Right _ -> do
      return bbfE
 where
   langExts = map Hint.asExtension $
                map show wantedLanguageExtensions ++
                map ("No" ++ ) (map show unwantedLanguageExtensions)

-- | List of known BlackBoxFunctions used to prevent Hint from firing. This
--  improves Clash startup times.
knownBlackBoxFunctions :: HashMap String BlackBoxFunction
knownBlackBoxFunctions =
  HashMap.fromList $ map (first show) $
    [ ('P.checkBBF, P.checkBBF)
    , ('P.bvToIntegerVHDL, P.bvToIntegerVHDL)
    , ('P.bvToIntegerVerilog, P.bvToIntegerVerilog)
    , ('P.foldBBF, P.foldBBF)
    , ('P.indexIntVerilog, P.indexIntVerilog)
    , ('P.indexToIntegerVerilog, P.indexToIntegerVerilog)
    , ('P.indexToIntegerVHDL, P.indexToIntegerVHDL)
    , ('P.intTF, P.intTF)
    , ('P.iterateBBF, P.iterateBBF)
    , ('P.signedToIntegerVerilog, P.signedToIntegerVerilog)
    , ('P.signedToIntegerVHDL, P.signedToIntegerVHDL)
    , ('P.unsignedToIntegerVerilog, P.unsignedToIntegerVerilog)
    , ('P.unsignedToIntegerVHDL, P.unsignedToIntegerVHDL)
    , ('P.wordTF, P.wordTF)
    ]

-- | List of known TemplateFunctions used to prevent Hint from firing. This
--  improves Clash startup times.
knownTemplateFunctions :: HashMap String TemplateFunction
knownTemplateFunctions =
  HashMap.fromList $ map (first show) $
    [ ('P.altpllQsysTF, P.altpllQsysTF)
    , ('P.alteraPllQsysTF, P.alteraPllQsysTF)
    , ('P.alteraPllTF, P.alteraPllTF)
    , ('P.altpllTF, P.altpllTF)
    ]

-- | Compiles blackbox functions and parses blackbox templates.
compilePrimitive
  :: [FilePath]
  -- ^ Import directories (-i flag)
  -> [FilePath]
  -- ^ Package databases
  -> FilePath
  -- ^ The folder in which the GHC bootstrap libraries (base, containers, etc.)
  -- can be found
  -> ResolvedPrimitive
  -- ^ Primitive to compile
  -> IO CompiledPrimitive
compilePrimitive idirs pkgDbs topDir (BlackBoxHaskell bbName wf usedArgs multiRes bbGenName source) = do
  bbFunc <-
    -- TODO: Use cache for hint targets. Right now Hint will fire multiple times
    -- TODO: if multiple functions use the same blackbox haskell function.
    case HashMap.lookup fullName knownBlackBoxFunctions of
      Just f -> pure f
      Nothing -> do
        Monad.when debugIsOn (putStr "Hint: interpreting " >> putStrLn (show fullName))
        let interpreterArgs = concatMap (("-package-db":) . (:[])) pkgDbs
        -- Compile a blackbox template function or fetch it from an already compiled file.
        r <- go interpreterArgs source
        processHintError
          (show bbGenName)
          bbName
          id
          r

  pure (BlackBoxHaskell bbName wf usedArgs multiRes bbGenName (hash source, bbFunc))
 where
    fullName = qualMod ++ "." ++ funcName
    qualMod = intercalate "." modNames
    BlackBoxFunctionName modNames funcName = bbGenName

    -- | Create directory based on base name and directory. Return path
    -- of directory just created.
    createDirectory'
      :: FilePath
      -> FilePath
      -> IO FilePath
    createDirectory' base sub =
      let new = base </> sub in
      Directory.createDirectory new >> return new

    go
      :: [String]
      -> Maybe Text
      -> IO (Either Hint.InterpreterError BlackBoxFunction)
    go args (Just source') = do
      -- Create a temporary directory with user module in it, add it to the
      -- list of import direcotries, and run as if it were a "normal" compiled
      -- module.
      tmpDir0 <- getCanonicalTemporaryDirectory
      withTempDirectory tmpDir0 "clash-prim-compile" $ \tmpDir1 -> do
        modDir <- foldM createDirectory' tmpDir1 (init modNames)
        Text.writeFile (modDir </> (last modNames ++ ".hs")) source'
        loadImportAndInterpret (tmpDir1:idirs) args topDir qualMod funcName "BlackBoxFunction"

    go args Nothing = do
      loadImportAndInterpret idirs args topDir qualMod funcName "BlackBoxFunction"

compilePrimitive idirs pkgDbs topDir
  (BlackBox pNm wf rVoid multiRes tkind () oReg libM imps fPlural incs rM riM templ) = do
  libM'  <- mapM parseTempl libM
  imps'  <- mapM parseTempl imps
  incs'  <- mapM (traverse parseBB) incs
  templ' <- parseBB templ
  rM'    <- traverse parseBB rM
  riM'   <- traverse parseBB riM
  return (BlackBox pNm wf rVoid multiRes tkind () oReg libM' imps' fPlural incs' rM' riM' templ')
 where
  iArgs = concatMap (("-package-db":) . (:[])) pkgDbs

  parseTempl
    :: Applicative m
    => Text
    -> m BlackBoxTemplate
  parseTempl t = case runParse t of
    Failure errInfo
      -> error ("Parsing template for blackbox " ++ Data.Text.unpack pNm ++ " failed:\n"
               ++ show (_errDoc errInfo))
    Success t'
      -> pure t'

  parseBB
    :: ((TemplateFormat,BlackBoxFunctionName), Maybe Text)
    -> IO BlackBox
  parseBB ((TTemplate,_),Just t)     = BBTemplate <$> parseTempl t
  parseBB ((TTemplate,_),Nothing)    =
    error ("No template specified for blackbox: " ++ show pNm)
  parseBB ((THaskell,bbGenName),Just source) = do
    let BlackBoxFunctionName modNames funcName = bbGenName
        qualMod = intercalate "." modNames
    tmpDir <- getCanonicalTemporaryDirectory
    r <- withTempDirectory tmpDir "clash-prim-compile" $ \tmpDir' -> do
      let modDir = foldl (</>) tmpDir' (init modNames)
      Directory.createDirectoryIfMissing True modDir
      Text.writeFile (modDir </> last modNames <.>  "hs") source
      loadImportAndInterpret (tmpDir':idirs) iArgs topDir qualMod funcName "TemplateFunction"
    let hsh = hash (qualMod, source)
    processHintError (show bbGenName) pNm (BBFunction (Data.Text.unpack pNm) hsh) r
  parseBB ((THaskell,bbGenName),Nothing) = do
    let BlackBoxFunctionName modNames funcName = bbGenName
        qualMod = intercalate "." modNames
        hsh     = hash qualMod
        fullName = qualMod ++ "." ++ funcName
    tf <-
      case HashMap.lookup fullName knownTemplateFunctions of
        Just f -> pure f
        Nothing -> do
          r <- loadImportAndInterpret idirs iArgs topDir qualMod funcName "TemplateFunction"
          processHintError (show bbGenName) pNm id r
    pure (BBFunction (Data.Text.unpack pNm) hsh tf)

compilePrimitive _ _ _ (Primitive pNm wf typ) =
  return (Primitive pNm wf typ)
{-# SCC compilePrimitive #-}

processHintError
  :: Monad m
  => String
  -> Data.Text.Text
  -> (t -> r)
  -> Either Hint.InterpreterError t
  -> m r
processHintError fun bb go r = case r of
  Left (Hint.GhcException err) ->
    error' "GHC Exception" err
  Left (Hint.NotAllowed err) ->
    error' "NotAllowed error" err
  Left (Hint.UnknownError err) ->
    error' "an unknown error" err
  Left (Hint.WontCompile ghcErrs) ->
    error' "compilation errors" (intercalate "\n\n" $ map Hint.errMsg ghcErrs)
  Right f ->
    return $ go f
 where
  error' errType report =
    error $ unwords [ "Encountered", errType, "while compiling blackbox template"
                    , "function", show fun, "for function", show bb ++ "."
                    , "Compilation reported: \n\n" ++ report ]

-- | Pretty print Components to HDL Documents
createHDL
  :: Backend backend
  => backend
  -- ^ Backend
  -> IdentifierText
  -- ^ Module hierarchy root
  -> Id.IdentifierSet
  -- ^ Component names
  -> VarEnv ([Bool],SrcSpan,Id.IdentifierSet,Component)
  -- ^ List of components
  -> HashMap Data.Text.Text VDomainConfiguration
  -- ^ Known domains to configurations
  -> Component
  -- ^ Top component
  -> IdentifierText
  -- ^ Name of the manifest file
  -> ([(String,Doc)],[(String,FilePath)],[(String,String)])
  -- ^ The pretty-printed HDL documents
  -- + The data files that need to be copied
createHDL backend modName seen components domainConfs top topName = flip evalState backend $ getMon $ do
  let componentsL = eltsVarEnv components
  (hdlNmDocs,incs) <-
    unzip <$> mapM (\(_wereVoids,sp,ids,comp) ->
                      genHDL modName sp (Id.union seen ids) comp)
              componentsL
  hwtys <- HashSet.toList <$> extractTypes <$> Mon get
  typesPkg <- mkTyPackage modName hwtys
  dataFiles <- Mon getDataFiles
  memFiles  <- Mon getMemoryDataFiles
  let
    hdl = map (first (<.> Clash.Backend.extension backend)) (typesPkg ++ hdlNmDocs)
    qincs = concat incs
    topFiles = hdl ++ qincs

    topClks = findClocks top
    sdcInfo = fmap findDomainConfig <$> topClks
    sdcFile = Data.Text.unpack topName <.> "sdc"
    sdcDoc  = (sdcFile, pprSDC (SdcInfo sdcInfo))
    sdc = if null sdcInfo then Nothing else Just sdcDoc

  return (maybeToList sdc <> topFiles, dataFiles, memFiles)
 where
  findDomainConfig dom =
    HashMap.lookupDefault
      (error $ $(curLoc) ++ "Unknown synthesis domain: " ++ show dom)
      dom
      domainConfs

writeEdam ::
  FilePath ->
  (Id.Identifier, Unique) ->
  HashMap Unique [Unique] ->
  HashMap Unique [EdamFile] ->
  [(FilePath, ByteString)] ->
  IO (HashMap Unique [EdamFile], [(FilePath, ByteString)])
writeEdam hdlDir (topNm, topEntity) deps edamFiles0 filesAndDigests = do
  let
    (edamFiles1, edamInfo) =
      createEDAM (topNm, topEntity) deps edamFiles0 (map fst filesAndDigests)
  edamDigest <- writeHDL hdlDir ("edam.py", pprEdam edamInfo)
  pure (edamFiles1, ("edam.py", edamDigest) : filesAndDigests)

-- | Create an Edalize metadata file for using Edalize to build the project.
--
-- TODO: Handle libraries. Also see: https://github.com/olofk/edalize/issues/220
createEDAM ::
  -- Top entity name and unique
  (Id.Identifier, Unique) ->
  -- | Top entity dependency map
  HashMap Unique [Unique] ->
  -- | Edam files of each top entity
  HashMap Unique [EdamFile] ->
  -- | Files to include in Edam file
  [FilePath] ->
  -- | (updated map, edam)
  (HashMap Unique [EdamFile], Edam)
createEDAM (topName, topUnique) deps edamFileMap files =
  (HashMap.insert topUnique (edamFiles edam) edamFileMap, edam)
 where
  edam = Edam
    { edamProjectName = Id.toText topName
    , edamTopEntity   = Id.toText topName
    , edamFiles       = fmap (asEdamFile topName) files <> fmap asIncFile incFiles
    , edamToolOptions = def
    }

  incFiles =
    concatMap
      (\u -> HashMap.lookupDefault [] u edamFileMap)
      (HashMap.lookupDefault [] topUnique deps)

  asIncFile f =
    f { efName = ".." </> Data.Text.unpack (efLogicalName f) </> efName f }

asEdamFile :: Id.Identifier -> FilePath -> EdamFile
asEdamFile topName path =
  EdamFile path edamFileType (Id.toText topName)
 where
  edamFileType =
    case FilePath.takeExtension path of
      ".vhdl" -> VhdlSource
      ".v" -> VerilogSource
      ".sv" -> SystemVerilogSource
      ".tcl" -> TclSource
      ".qsys" -> QSYS
      ".sdc" -> SDC
      _ -> Clash.Edalize.Edam.Unknown

-- | Prepares directory for writing HDL files.
prepareDir ::
  -- | HDL directory to prepare
  FilePath ->
  -- | Relevant options: @-fclash-no-clean@
  ClashOpts ->
  -- | Did directory contain unexpected modifications? See 'readFreshManifest'
  Maybe [UnexpectedModification] ->
  IO ()
prepareDir hdlDir ClashOpts{opt_clear} mods = do
  ifM
    (doesPathExist hdlDir)
    (ifM
      (doesDirectoryExist hdlDir)
      (detectCaseIssues >> clearOrError >> createDir)
      (error [I.i|Tried to write HDL files to #{hdlDir}, but it wasn't a directory.|]))
    createDir

 where
  createDir = createDirectoryIfMissing True hdlDir

  -- Windows considers 'foo' and 'FOO' the same directory. Error if users tries
  -- to synthesize two top entities with conflicting (in this sense) names.
  detectCaseIssues = do
    allPaths <- listDirectory (takeDirectory hdlDir)
    unless (takeFileName hdlDir `elem` allPaths) (error [I.i|
      OS indicated #{hdlDir} existed, but Clash could not find it among the
      list of existing directories in #{takeDirectory hdlDir}:

        #{allPaths}

      This probably means your OS or filesystem is case-insensitive. Rename your
      top level binders in order to prevent this error message.
    |])

  clearOrError =
    case mods of
      Just [] ->
        -- No unexpected changes, so no user work will get lost
        removeDirectoryRecursive hdlDir
      _ | opt_clear ->
        -- Unexpected changes / non-empty directory, but @-fclash-clear@ was
        -- set, so remove directory anyway.
        removeDirectoryRecursive hdlDir
      Just unexpected ->
        -- Unexpected changes; i.e. modifications were made after last Clash run
        error [I.i|
          Changes were made to #{hdlDir} after last Clash run:

            #{pprintUnexpectedModifications 5 unexpected}

          Use '-fclash-clear' if you want Clash to clear out the directory.
          Warning: this will remove the complete directory, be cautious of data
          loss.
        |]
      Nothing ->
        -- No manifest file was found. Refuse to write if directory isn't empty.
        unlessM
          (null <$> listDirectory hdlDir)
          (error [I.i|
            Tried to write HDL files to #{hdlDir}, but directory wasn't empty.

            Use '-fclash-clear' if you want Clash to clear out the directory.
            Warning: this will remove the complete directory, be cautious of data
            loss.
          |])

-- | Write a file to disk in chunks. Returns SHA256 sum of file contents.
writeAndHash :: FilePath -> ByteStringLazy.ByteString -> IO ByteString
writeAndHash path bs =
  IO.withFile path IO.WriteMode $ \handle ->
      fmap Sha256.finalize
    $ foldM (writeChunk handle) Sha256.init
    $ ByteStringLazy.toChunks bs
 where
  writeChunk :: IO.Handle -> Sha256.Ctx -> ByteString -> IO Sha256.Ctx
  writeChunk h !ctx chunk = do
    ByteString.hPut h chunk
    pure (Sha256.update ctx chunk)

-- | Writes a HDL file to the given directory. Returns SHA256 hash of written
-- file.
writeHDL :: FilePath -> (FilePath, Doc) -> IO ByteString
writeHDL dir (cname, hdl) = do
  let
    layout = LayoutOptions (AvailablePerLine 120 0.4)
    rendered0 = renderLazy (layoutPretty layout hdl)
    rendered1 = Text.unlines (map Text.stripEnd (Text.lines rendered0))
  writeAndHash (dir </> cname) (Text.encodeUtf8 (rendered1 <> "\n"))

-- | Copy given files
writeMemoryDataFiles
    :: FilePath
    -- ^ Directory to copy  files to
    -> [(FilePath, String)]
    -- ^ (filename, content)
    -> IO [ByteString]
writeMemoryDataFiles dir files =
  forM files $ \(fname, content) ->
    writeAndHash (dir </> fname) (ByteStringLazyChar8.pack content)

-- | Copy data files added with ~FILEPATH
copyDataFiles
  :: [FilePath]
  -- ^ Import directories passed in with @-i@
  -> FilePath
  -- ^ Directory to copy to
  -> [(FilePath,FilePath)]
  -- ^ [(name of newly made file in HDL output dir, file to copy)]
  -> IO [ByteString]
  -- ^ SHA256 hashes of written files
copyDataFiles idirs targetDir = mapM copyDataFile
 where
  copyDataFile :: (FilePath, FilePath) -> IO ByteString
  copyDataFile (newName, toCopy)
    | isAbsolute toCopy = do
      ifM
        (doesFileExist toCopy)
        (copyAndHash toCopy (targetDir </> newName))
        (error [I.i|Could not find data file #{show toCopy}. Does it exist?|])
    | otherwise = do
      let candidates = map (</> toCopy) idirs
      found <- filterM doesFileExist candidates
      case found of
        [] -> error [I.i|
          Could not find data file #{show toCopy}. The following directories were
          searched:

            #{idirs}

          You can add directories Clash will look in using `-i`.
        |]
        (_:_:_) -> error [I.i|
          Multiple data files for #{show toCopy} found. The following candidates
          were found:

            #{found}

          Please disambiguate data files.
        |]
        [c] ->
          copyAndHash c (targetDir </> newName)

  copyAndHash src dst = do
    ifM
      (doesPathExist dst)
      (error [I.i|
        Tried to copy data file #{src} to #{dst} but a file or directory with
        that name already existed. This is a bug in Clash, please report it.
      |])
      (ByteStringLazy.readFile src >>= writeAndHash dst)

-- | Normalize a complete hierarchy
normalizeEntity
  :: CustomReprs
  -> BindingMap
  -- ^ All bindings
  -> CompiledPrimMap
  -- ^ BlackBox HDL templates
  -> TyConMap
  -- ^ TyCon cache
  -> IntMap TyConName
  -- ^ Tuple TyCon cache
  -> (CustomReprs -> TyConMap -> Type ->
      State HWMap (Maybe (Either String FilteredHWType)))
  -- ^ Hardcoded 'Type' -> 'HWType' translator
  -> Evaluator
  -- ^ Hardcoded evaluator for partial evaluation
  -> [Id]
  -- ^ TopEntities
  -> ClashOpts
  -- ^ Debug information level for the normalization process
  -> Supply.Supply
  -- ^ Unique supply
  -> Id
  -- ^ root of the hierarchy
  -> BindingMap
normalizeEntity reprs bindingsMap primMap tcm tupTcm typeTrans eval topEntities
  opts supply tm = transformedBindings
  where
    doNorm = do norm <- normalize [tm]
                let normChecked = checkNonRecursive norm
                cleaned <- cleanupGraph tm normChecked
                return cleaned
    transformedBindings = runNormalization opts supply bindingsMap
                            typeTrans reprs tcm tupTcm eval primMap emptyVarEnv
                            topEntities doNorm

-- | topologically sort the top entities
sortTop
  :: BindingMap
  -> [TopEntityT]
  -> ([TopEntityT], HashMap Unique [Unique])
sortTop bindingsMap topEntities =
  let (nodes,edges) = unzip (map go topEntities)
      edges' = concat edges
  in  case reverseTopSort nodes edges' of
        Left msg   -> error msg
        Right tops -> (tops, mapFrom edges')
 where
  go t@(TopEntityT topE _ _) =
    let topRefs = goRefs topE topE
    in  ((varUniq topE,t)
         ,map ((\top -> (varUniq topE, varUniq (topId top)))) topRefs)

  goRefs top i_ =
    let cg = callGraph bindingsMap i_
    in
      filter
        (\t -> topId t /= top && topId t /= i_ && topId t `elemVarEnv` cg)
        topEntities

  mapFrom = HashMap.fromListWith mappend . fmap (fmap pure)
