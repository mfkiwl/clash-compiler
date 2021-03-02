{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Clash.Util.Interpolate    as I

import           Clash.Annotations.Primitive (HDL(..))
import           Control.Exception         (finally)
import qualified Data.Text                 as Text
import           Data.Default              (def)
import           Data.List                 ((\\), intercalate)
import           Data.Version              (versionBranch)
import           System.Directory
  (createDirectoryIfMissing, removeDirectoryRecursive, getCurrentDirectory,
   doesDirectoryExist, makeAbsolute)
import           System.Environment
import           System.Exit
  (exitWith, ExitCode(ExitSuccess, ExitFailure))
import           System.FilePath           ((</>))
import           System.Info
import           System.Process            (readCreateProcessWithExitCode, proc)
import           GHC.Conc                  (numCapabilities)
import           GHC.Stack
import           GHC.IO.Unsafe             (unsafePerformIO)
import           Text.Printf               (printf)

import           Test.Tasty
import           Test.Tasty.Clash

-- | GHC version as major.minor.patch1. For example: 8.10.2.
ghcVersion3 :: String
ghcVersion3 =
#ifdef __GLASGOW_HASKELL_PATCHLEVEL2__
  let ghc_p1 = __GLASGOW_HASKELL_PATCHLEVEL1__
      ghc_p2 = __GLASGOW_HASKELL_PATCHLEVEL2__ in
  intercalate "." (map show (versionBranch compilerVersion <> [ghc_p1,ghc_p2]))
#else
  let ghc_p1 = __GLASGOW_HASKELL_PATCHLEVEL1__ in
  intercalate "." (map show (versionBranch compilerVersion <> [ghc_p1]))
#endif

-- Directory clash binary is expected to live in
cabalClashBinDir :: IO String
cabalClashBinDir = makeAbsolute rel_path
 where
  rel_path = printf templ platform ghcVersion3 (VERSION_clash_ghc :: String)
  platform = "x86_64-linux" :: String -- XXX: Hardcoded
  templ = "dist-newstyle/build/%s/ghc-%s/clash-ghc-%s/x/clash/build/clash/" :: String

-- | Set GHC_PACKAGE_PATH for local Cabal install. Currently hardcoded for Unix.
setCabalPackagePaths :: IO ()
setCabalPackagePaths = do
  home <- getEnv "HOME"
  here <- getCurrentDirectory
  setEnv "GHC_PACKAGE_PATH" $
       home <> "/.cabal/store/ghc-" <> ghcVersion3 <> "/package.db"
    <> ":"
    <> here <> "/dist-newstyle/packagedb/ghc-" <> ghcVersion3
    <> ":"

-- | See 'compiledWith'
data RunWith
  = Stack
  | Cabal
  | Global
  deriving (Show, Eq)

-- | Detects Clash binary the testsuite should use (in order):
--
--     * If USE_GLOBAL_CLASH=1, use globally installed Clash
--     * If STACK_EXE is present, use Stack's Clash
--     * If dist-newstyle is present, use Cabal's Clash
--     * Use globally installed Clash
--
compiledWith :: RunWith
compiledWith = unsafePerformIO $ do
  clash_global <- lookupEnv "USE_GLOBAL_CLASH"
  stack_exe <- lookupEnv "STACK_EXE"
  distNewstyleExists <- doesDirectoryExist "dist-newstyle"

  pure $ case (clash_global, stack_exe, distNewstyleExists) of
    (Just "1", Just _, _   ) -> error "Can't use global clash with 'stack run'"
    (Just "1", _,      _   ) -> Global
    (_,        Just _, _   ) -> Stack
    (_,        _     , True) -> Cabal
    (_,        _     , _   ) -> Global
{-# NOINLINE compiledWith #-}

-- | Set environment variables that allow Clash to be executed by simply calling
-- 'clash' without extra arguments.
setClashEnvs :: HasCallStack => RunWith -> IO ()
setClashEnvs Global = setEnv "GHC_ENVIRONMENT" "-"
setClashEnvs Stack = pure ()
setClashEnvs Cabal = do
  -- Make sure environment variable exists
  let cp = proc "cabal" ["--write-ghc-environment-files=always", "v2-run", "--", "clash", "--help"]
  (exitCode, stdout, stderr) <- readCreateProcessWithExitCode cp ""
  case exitCode of
    ExitSuccess -> do
      binDir <- cabalClashBinDir
      path <- getEnv "PATH"
      setEnv "PATH" (binDir <> ":" <> path)
      setCabalPackagePaths
    ExitFailure _ -> do
      putStrLn "'cabal run clash' failed"
      putStrLn ">>> stdout:"
      putStrLn stdout
      putStrLn ">>> stderr:"
      putStrLn stderr
      exitWith exitCode

clashTestRoot
  :: [[TestName] -> TestTree]
  -> TestTree
clashTestRoot testTrees =
  clashTestGroup "." testTrees []

-- | `clashTestGroup` and `clashTestRoot` make sure that each test knows its
-- fully qualified test name at construction time. This is used to create
-- dependency patterns.
clashTestGroup
  :: TestName
  -> [[TestName] -> TestTree]
  -> ([TestName] -> TestTree)
clashTestGroup testName testTrees =
  \parentNames ->
    testGroup testName $
      zipWith ($) testTrees (repeat (testName : parentNames))

runClashTest :: IO ()
runClashTest = defaultMain $ clashTestRoot
  [ clashTestGroup "netlist"
    [ clashLibTest ("tests" </> "shouldwork" </> "Netlist") allTargets [] "Identity" "main"
    , clashLibTest ("tests" </> "shouldwork" </> "Netlist") [VHDL] [] "NoDeDup" "main"
    ]
  , clashTestGroup "examples"
    [ runTest "ALU" def{hdlSim=False}
    , let _opts = def { hdlSim=False
                      , hdlTargets=[VHDL]
                      , entities=Entities [["blinker"]]
                      , topEntities=TopEntities ["blinker"]
                      }
       in runTest "Blinker" _opts
    , runTest "BlockRamTest" def{hdlSim=False}
    , runTest "Calculator" def
    , runTest "CHIP8" def{hdlSim=False}
    , runTest "CochleaPlus" def{hdlSim=False}
    , let _opts = def { clashFlags=["-fclash-component-prefix", "test"]
                      , entities=Entities [["","test_testBench"]]
                      , topEntities=TopEntities ["test_testBench"]
                      }
       in runTest "FIR" _opts
    , runTest "Fifo" def{hdlSim=False}
    , runTest "MAC" def
    , runTest "MatrixVect" def
    , runTest "Queens" def{hdlSim=False}
    , runTest "Reducer" def{hdlSim=False}
    , runTest "Sprockell" def{hdlSim=False}
    , runTest "Windows" def{hdlSim=False}
    , clashTestGroup "crc32"
        [ runTest "CRC32" def
        ]
    , clashTestGroup "i2c"
        [ let _opts = def { clashFlags=["-O2","-fclash-component-prefix","test"]
                        , entities=Entities [["test_i2c","test_bitmaster","test_bytemaster"]]
                        , topEntities=TopEntities ["test_i2c"]
                        , hdlSim=False
                        }
           in runTest "I2C" _opts
        , let _opts = def { entities = Entities [[ ".." </> "I2C" </> "i2c"
                                                 , ".." </> "I2C" </> "bitmaster"
                                                 , ".." </> "I2C" </> "bytemaster"
                                                 , "configi2c"
                                                 , "slave"
                                                 , "system"
                                                 ]]
                          , topEntities = TopEntities ["system"]
                          , hdlTargets = [Verilog]
                          , hdlSim = True
                          , vvpStderrEmptyFail = False
                          }
           in runTest "I2Ctest" _opts
        ]
    ]
  , clashTestGroup "tests"
    [ clashTestGroup "shouldfail"
      [ clashTestGroup "BlackBox"
        [ runTest "WrongReference" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, Text.pack [I.i|
              Function WrongReference.myMultiply was annotated with an inline
              primitive for WrongReference.myMultiplyX. These names should be
              the same. |])
          }
        ]
      , clashTestGroup "InvalidPrimitive"
        [ runTest "InvalidPrimitive" def{
            hdlTargets=[VHDL]
          , clashFlags=["-itests/shouldfail/InvalidPrimitive"]
          , expectClashFail=Just (def, "InvalidPrimitive.json")
          }
        ]
      , clashTestGroup "GADTs"
        [ runTest "T1311" def {
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, Text.pack [I.i|
            Can't translate data types with unconstrained existentials|])
          }
        ]
      , clashTestGroup "PrimitiveGuards"
        [ runTest "DontTranslate" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, Text.pack [I.i|
              Clash was forced to translate 'DontTranslate.primitive', but this
              value was marked with DontTranslate. Did you forget to include a
              blackbox for one of the constructs using this?
            |])
          }
        , runTest "HasBlackBox" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, Text.pack [I.i|
              No BlackBox definition for 'HasBlackBox.primitive' even though
              this value was annotated with 'HasBlackBox'.
            |])
          }
        ]
      , clashTestGroup "Signal"
        [ runTest "MAC" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Couldn't instantiate blackbox for Clash.Signal.Internal.register#")
          }
        ]
      , clashTestGroup "SynthesisAttributes"
        [ runTest "ProductInArgs" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Cannot use attribute annotations on product types of top entities")
          }
        , runTest "ProductInResult" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Cannot use attribute annotations on product types of top entities")
          }
        ]
      , clashTestGroup "TopEntity"
        [ runTest "T1033" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "PortProduct \"wrong\" []")
          }
        , runTest "T1063" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Saw a PortProduct in a Synthesize annotation")
          }
        ]
      , clashTestGroup "Verification"
        [ let n = 9 -- GHDL only has VERY basic PSL support
              _opts = def { hdlTargets=[VHDL]
                          , entities=Entities [["fails" ++ show i] | i <- [(1::Int)..n]]
                          , topEntities=TopEntities ["fails" ++ show i | i <- [(1::Int)..n]]
                          , expectSimFail=Just (def, "psl assertion failed")
                          }
           in runTest "NonTemporalPSL" _opts
        , let n = 13
              _opts = def { hdlTargets=[SystemVerilog]
                          , entities=Entities [["fails" ++ show i] | i <- [(1::Int)..n]]
                          , topEntities=TopEntities ["fails" ++ show i | i <- [(1::Int)..n]]
                          -- Only QuestaSim supports simulating SVA/PSL, but ModelSim does check
                          -- for syntax errors.
                          , hdlSim=False
                          }
           in runTest "NonTemporalPSL" _opts
        , let is = [(1::Int)..13] \\ [4, 6, 7, 8, 10, 11, 12] in
          runTest "NonTemporalSVA" def{
            hdlTargets=[SystemVerilog]
          , entities=Entities [["fails" ++ show i] | i <- is]
          , topEntities=TopEntities ["fails" ++ show i | i <- is]
          -- Only QuestaSim supports simulating SVA/PSL, but ModelSim does check
          -- for syntax errors.
          , hdlSim=False
          }
        ]
      , clashTestGroup "ZeroWidth"
        [ runTest "FailGracefully1" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Unexpected projection of zero-width type")
          }
        , runTest "FailGracefully2" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Unexpected projection of zero-width type")
          }
        , runTest "FailGracefully3" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (def, "Unexpected projection of zero-width type")
          }
        ]
      , runTest "LiftRecursiveGroup" def{
          hdlTargets=[VHDL]
        , expectClashFail=Just (def,"Callgraph after normalization contains following recursive components:")
        }
      , runTest "Poly" def{
          hdlTargets=[VHDL]
        , expectClashFail=Just (def, "Clash can only normalize monomorphic functions, but this is polymorphic:")
        }
      , runTest "Poly2" def{
          hdlTargets=[VHDL]
        , clashFlags=["-fclash-error-extra"]
        , expectClashFail=Just (def, "Even after applying type equality constraints it remained polymorphic:")
        }
      , runTest "RecursiveBoxed" def{
          hdlTargets=[VHDL]
        , expectClashFail=Just (def, "already inlined 20 times")
        }
      , runTest "RecursiveDatatype" def{
          hdlTargets=[VHDL]
        , expectClashFail=Just (def, "This bndr has a non-representable return type and can't be normalized:")
        }
--        Disabled, due to it eating gigabytes of memory:
--      , runTest "RecursivePoly" def{
--          hdlTargets=[VHDL]
--        , expectClashFail=Just (def, "??")
--        }
      ]
    , clashTestGroup "shouldwork"
      [ clashTestGroup "AutoReg"
        [ outputTest ("tests" </> "shouldwork" </> "AutoReg") allTargets [] [] "AutoReg" "main"
        , runTest "T1507" def{hdlSim=False}
        , runTest "T1632" def{hdlSim=False, hdlTargets=[VHDL]}
        ]
      , clashTestGroup "Basic"
        [ runTest "AES" def{hdlSim=False}
        , runTest "BangData" def{hdlSim=False}
        , runTest "Trace" def{hdlSim=False}
        , runTest "DivMod" def{hdlSim=False}
        , runTest "LambdaDrop" def{hdlSim=False}
        , runTest "IrrefError" def{hdlSim=False}
#ifdef CLASH_MULTIPLE_HIDDEN
        , runTest "MultipleHidden" def
#endif
        , outputTest ("tests" </> "shouldwork" </> "Basic") allTargets [] [] "NameInlining" "main"
        , runTest "NameInstance" def{hdlSim=False}
        , outputTest ("tests" </> "shouldwork" </> "Basic") allTargets [] [] "NameInstance" "main"
        , outputTest ("tests" </> "shouldwork" </> "Basic") [VHDL] [] [] "SetName" "main"
        , runTest "PatError" def{hdlSim=False}
        , runTest "ByteSwap32" def
        , runTest "CharTest" def
        , runTest "ClassOps" def
        , runTest "CountTrailingZeros" def
        , runTest "DeepseqX" def
        , runTest "LotOfStates" def
        , let _opts = def { entities = Entities [["nameoverlap"]]
                          , topEntities = TopEntities ["nameoverlap"]
                          , hdlSim = False
                          }
           in runTest "NameOverlap" _opts
        , runTest "NestedPrimitives" def{hdlSim=False}
        , runTest "NestedPrimitives2" def{hdlSim=False}
        , runTest "NORX" def
        , runTest "Parameters" def{hdlTargets=[VHDL]}
        , runTest "PopCount" def
        , runTest "RecordSumOfProducts" def{hdlSim=False}
        , runTest "Replace" def
        , runTest "TestIndex" def{hdlSim=False}
        , runTest "Time" def
        , runTest "Shift" def{hdlSim=False}
        , runTest "SimpleConstructor" def{hdlSim=False}
        , runTest "TyEqConstraints" def{
            hdlSim=False
          , entities=Entities [["top1"]]
          , topEntities=TopEntities ["top1"]
          }
        , runTest "T1012" def{hdlSim=False}
        , runTest "T1240" def{hdlSim=False}
        , let _opts = def {hdlTargets = [VHDL], hdlSim = False}
           in runTest "T1297" _opts
        , runTest "T1254" def{hdlTargets=[VHDL,SystemVerilog],hdlSim=False}
        , runTest "T1242" def{hdlSim=False}
        , runTest "T1292" def{hdlTargets=[VHDL]}
        , let _opts = def { hdlTargets = [VHDL], hdlLoad = False }
           in runTest "T1304" _opts
        , let _opts = def { hdlTargets=[VHDL]
                          , hdlSim=False
                          , clashFlags=["-main-is", "plus"]
                          , topEntities=TopEntities ["plus"]
                          }
           in runTest "T1305" _opts
        , let _opts = def {hdlTargets = [VHDL], hdlSim = False}
           in runTest "T1316" _opts
        , runTest "T1322" def{hdlTargets=[VHDL]}
        , let _opts = def {hdlTargets = [VHDL], hdlSim = False}
           in runTest "T1340" _opts
#if MIN_VERSION_ghc(8,6,1)
          -- GHC 8.4 doesn't constant fold constructs on naturals. This tricks
          -- Clash into thinking binders variables aren't constant, while in
          -- reality the are. A proper solution would be to:
          --
          --   1. Normalize any global binders applied to constant-only arguments
          --      before finishing normalizing binders they're used in.
          --   2. Implement a proper partial evaluator.
          --
          -- As (2) is in the works, we've decided to not persue (1) for now and
          -- simply advice users encountering this bug to use >8.4.
        , let _opts = def { hdlTargets = [VHDL], hdlSim = False}
           in runTest "T1354A" _opts
#endif
        , let _opts = def { hdlTargets = [VHDL], hdlSim = False}
           in runTest "T1354B" _opts
        , runTest "T1402" def{clashFlags=["-O"]}
        , runTest "T1402b" def{hdlTargets=[VHDL], hdlSim=False}
        , runTest "T1556" def
        , runTest "T1591" def{hdlTargets=[VHDL], hdlSim=False}
        , runTest "TagToEnum" def{hdlSim=False}
        , runTest "TwoFunctions" def{hdlSim=False}
        , runTest "XToError" def{hdlSim=False}
        ]
      , clashTestGroup "BitVector"
        [ runTest "Box" def
        , runTest "BoxGrow" def
        , runTest "CLZ" def
        , runTest "RePack" def{hdlSim=False}
        , runTest "ReduceZero" def
        , runTest "ReduceOne" def
        , runTest "ExtendingNumZero" def
        , runTest "AppendZero" def
        , runTest "GenericBitPack" def{clashFlags=["-fconstraint-solver-iterations=15"]}
        , runTest "UnpackUndefined" def{hdlSim=False}
        ]
      , clashTestGroup "BlackBox"
        [ outputTest ("tests" </> "shouldwork" </> "BlackBox") [VHDL]   [] [] "TemplateFunction"   "main"
        , outputTest ("tests" </> "shouldwork" </> "BlackBox") [VHDL]   [] [] "BlackBoxFunction"   "main"
        , runTest "BlackBoxFunctionHO" def{hdlTargets=[VHDL]}
        , outputTest ("tests" </> "shouldwork" </> "Signal") allTargets [] [] "BlockRamLazy" "main"
        , outputTest ("tests" </> "shouldwork" </> "BlackBox") [VHDL]   [] [] "ZeroWidth"          "main"
        , outputTest ("tests" </> "shouldwork" </> "BlackBox") [VHDL]   [] [] "MultiResult"        "main"
        , runTest "MultiResult" def
        , runTest "T919" def{hdlSim=False}
        , runTest "T1524" def
        ]
      , clashTestGroup "BoxedFunctions"
        [ runTest "DeadRecursiveBoxed" def{hdlSim=False}
        ]
      , clashTestGroup "CSignal"
        [ runTest "MAC" def{hdlSim=False}
        , runTest "CBlockRamTest" def{hdlSim=False}
        ]
#ifdef COSIM
      , clashTestGroup "CoSim"
        [ runTest "Multiply" def{hdlTargets=[Verilog]}
        , runTest "Register" def{hdlTargets=[Verilog]}
        ]
#endif
      , clashTestGroup "CustomReprs"
        [ clashTestGroup "RotateC"
          [ runTest "RotateC" def
          , runTest "ReprCompact" def
          , runTest "ReprCompactScrambled"   def
          , runTest "ReprLastBitConstructor" def
          , let _opts = def { hdlTargets = [VHDL, Verilog] }
             in runTest "ReprStrangeMasks" _opts
          , runTest "ReprWide" def
          , runTest "RotateCScrambled" def
          ]
        , clashTestGroup "RotateCNested"
          [ runTest "RotateCNested" def
          ]
        , clashTestGroup "Rotate"
          [ runTest "Rotate" def
          ]
        , clashTestGroup "Deriving"
          [ runTest "BitPackDerivation" def
          ]
        , clashTestGroup "Indexed"
          [ runTest "Indexed" def
          ]
        ]
      , clashTestGroup "CustomReprs"
        [ clashTestGroup "ZeroWidth"
          [ runTest "ZeroWidth" def{hdlSim=False}
          ]
        , runTest "T694" def{hdlSim=False,hdlTargets=[VHDL]}
        ]
      , clashTestGroup "DDR"
        [ runTest "DDRinGA" def
        , runTest "DDRinGS" def
        , runTest "DDRinUA" def
        , runTest "DDRinUS" def
        , runTest "DDRoutUA" def
        , runTest "DDRoutUS" def
        , runTest "DDRoutGA" def
        , runTest "DDRoutGS" def
        ]
      , clashTestGroup "DSignal"
        [ runTest "DelayedFold" def
        , runTest "DelayI" def
        , runTest "DelayN" def
        ]
      , clashTestGroup "Feedback"
        [ runTest "Fib" def
#ifdef CLASH_MULTIPLE_HIDDEN
        , runTest "MutuallyRecursive" def
#endif
        ]
      , clashTestGroup "Fixed"
        [ runTest "Mixer" def
        , runTest "SFixedTest" def
        , runTest "SatWrap" def{hdlSim=False}
        , runTest "ZeroInt" def
        ]
      , clashTestGroup "Floating"
        [ runTest "FloatPack" def{hdlSim=False, clashFlags=["-fclash-float-support"]}
        , runTest "FloatConstFolding" def{clashFlags=["-fclash-float-support"]}
        ]
      , clashTestGroup "GADTs"
        [ runTest "Constrained" def
        , runTest "Head" def
        , runTest "HeadM" def
        , runTest "MonomorphicTopEntity" def
        , runTest "Record" def
        , runTest "Tail" def
        , runTest "TailM" def
        , runTest "TailOfTail" def
        , runTest "T1310" def{hdlSim=False}
        , runTest "T1536" def{hdlSim=False}
        ]
      , clashTestGroup "HOPrim"
        [ runTest "HOIdx" def
        , runTest "HOImap" def
        , runTest "Map" def
        , runTest "Map2" def
        , runTest "TestMap" def
        , runTest "Transpose" def
        , runTest "VecFun" def
      ]
      , clashTestGroup "Issues" $
        [ let _opts = def { hdlSim = False, hdlTargets = [Verilog] }
           in runTest "T1187" _opts
        , clashLibTest ("tests" </> "shouldwork" </> "Issues") [VHDL] [] "T1388" "main"
        , outputTest ("tests" </> "shouldwork" </> "Issues") allTargets [] [] "T1171" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "Issues") [VHDL] [] "T1439" "main"
        , runTest "T1477" def{hdlSim=False}
        , runTest "T1506A" def{hdlSim=False, clashFlags=["-fclash-aggressive-x-optimization-blackboxes"]}
        , outputTest ("tests" </> "shouldwork" </> "Issues") allTargets ["-fclash-aggressive-x-optimization-blackboxes"] ["-itests/shouldwork/Issues"] "T1506B" "main"
        , runTest "T1615" def{hdlSim=False, hdlTargets=[Verilog]}
        , runTest "T1663" def{hdlTargets=[VHDL], hdlSim=False}
        ] <>
        if compiledWith == Cabal then
          -- This tests fails without environment files present, which are only
          -- generated by Cabal. It complains it is trying to import "BasicTypes"
          -- which is a member of the hidden package 'ghc'. Passing
          -- '-package ghc' doesn't seem to help though. TODO: Investigate.
          [clashLibTest ("tests" </> "shouldwork" </> "Issues") allTargets [] "T1568" "main"]
        else
          []
      , clashTestGroup "Naming"
        [ runTest "T967a" def{hdlSim=False}
        , runTest "T967b" def{hdlSim=False}
        , runTest "T967c" def{hdlSim=False}
        , clashLibTest ("tests" </> "shouldwork" </> "Naming") allTargets [] "T1041" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "Naming") [VHDL,Verilog] [] "NameHint" "main"
        ]
      , clashTestGroup "Numbers"
        [ runTest "BitInteger" def
#if MIN_VERSION_base(4,14,0)
        , runTest "BitReverse" def
#endif
        , runTest "Bounds" def
        , runTest "DivideByZero" def
        , let _opts = def { clashFlags=["-itests/shouldwork/Numbers", "-fconstraint-solver-iterations=15"] }
           in runTest "ExpWithGhcCF" _opts
        , let _opts = def { clashFlags=["-itests/shouldwork/Numbers", "-fconstraint-solver-iterations=15"] }
           in runTest "ExpWithClashCF" _opts
        , outputTest ("tests" </> "shouldwork" </> "Numbers") allTargets ["-itests/shouldwork/Numbers"] ["-itests/shouldwork/Numbers"] "ExpWithClashCF" "main"
        , let _opts = def { hdlTargets = [VHDL], hdlSim = False }
           in runTest "HalfAsBlackboxArg" _opts
        , runTest "IntegralTB" def{clashFlags=["-itests/shouldwork/Numbers"]}
        , runTest "NumConstantFoldingTB_1" def{clashFlags=["-itests/shouldwork/Numbers"]}
        , outputTest ("tests" </> "shouldwork" </> "Numbers") allTargets ["-fconstraint-solver-iterations=15"] ["-itests/shouldwork/Numbers"] "NumConstantFolding_1" "main"
        , runTest "NumConstantFoldingTB_2" def{clashFlags=["-itests/shouldwork/Numbers"]}
        , outputTest ("tests" </> "shouldwork" </> "Numbers") allTargets ["-fconstraint-solver-iterations=15"] ["-itests/shouldwork/Numbers"] "NumConstantFolding_2" "main"
#if MIN_VERSION_base(4,12,0)
        -- Naturals are broken on GHC <= 8.4. See https://github.com/clash-lang/clash-compiler/pull/473
        , runTest "Naturals" def
        , runTest "NaturalToInteger" def{hdlSim=False}
#endif
        , runTest "NegativeLits" def
        , runTest "Resize" def
        , runTest "Resize2" def
        , runTest "Resize3" def
        , runTest "SatMult" def{hdlSim=False}
        , runTest "ShiftRotate" def{clashFlags=["-itests/shouldwork/Numbers"]}
        , runTest "SignedProjectionTB" def
        , runTest "SignedZero" def
        , runTest "Signum" def
        , runTest "Strict" def
        , runTest "T1019" def{hdlSim=False}
        , runTest "T1351" def
        , outputTest ("tests" </> "shouldwork" </> "Numbers") allTargets [] ["-itests/shouldwork/Numbers"] "UndefinedConstantFolding" "main"
        , runTest "UnsignedZero" def
        ]
      , clashTestGroup "Polymorphism"
        [ runTest "ExistentialBoxed" def{hdlSim=False}
        , runTest "FunctionInstances" def
        , runTest "GADTExistential" def{hdlSim=False}
        , runTest "LocalPoly" def{hdlSim=False}
        ]
      , clashTestGroup "PrimitiveGuards"
        [ runTest "WarnAlways" def{
            hdlTargets=[VHDL]
          , expectClashFail=Just (NoTestExitCode, "You shouldn't use 'primitive'!")
          }
        ]
      , clashTestGroup "PrimitiveReductions"
        [ runTest "Lambda" def
        , runTest "ReplaceInt" def
        ]
      , clashTestGroup "RTree"
        [ runTest "TZip" def{hdlSim=False}
        , runTest "TFold" def{hdlSim=False}
        , runTest "TRepeat" def
        , runTest "TRepeat2" def
        ]
      , clashTestGroup "Shadowing"
        [ runTest "T990" def
        ]
      , clashTestGroup "Signal"
        [ runTest "AlwaysHigh" def{hdlSim=False}
        , runTest "BangPatterns" def
        , runTest "BlockRamFile" def
        , runTest "BlockRam0" def
        , runTest "BlockRam1" def
        , runTest "Ram" def
        , runTest "ResetGen" def
        , runTest "RomFile" def
        , outputTest ("tests" </> "shouldwork" </> "Signal") allTargets [] [] "BlockRamLazy" "main"
        , runTest "BlockRamTest" def{hdlSim=False}
        , runTest "Compression" def
        , runTest "DelayedReset" def
        , let _opts = def { entities=Entities [["example"]]
                          , topEntities=TopEntities ["example"]
                          , hdlSim=False
                          }
           in runTest "NoCPR" _opts
        , runTest "Oversample" def
        , runTest "RegisterAR" def
        , runTest "RegisterSR" def
        , runTest "RegisterAE" def
        , runTest "RegisterSE" def
        , runTest "ResetSynchronizer" def
        , runTest "ResetSynchronizerSync" def
        , runTest "ResetLow" def
        , runTest "Rom" def
        , runTest "SigP" def{hdlSim=False}
        , outputTest ("tests" </> "shouldwork" </> "Signal") [VHDL] [] [] "T1102A" "main"
        , outputTest ("tests" </> "shouldwork" </> "Signal") [VHDL] [] [] "T1102B" "main"

        , clashTestGroup "BiSignal"
          [ runTest "Counter" def
          , runTest "CounterHalfTuple" def
          , runTest "CounterHalfTupleRev" def
          ]
        , runTest "T1007" def{hdlSim=False}
        ]
      , clashTestGroup "SimIO"
        [ let _opts = def { hdlTargets=[Verilog]
                          , vvpStderrEmptyFail=False
                          , topEntities=TopEntities ["topEntity"]
                          }
           in runTest "Test00" _opts
        ]
      , clashTestGroup "SynthesisAttributes"
        [ outputTest ("tests" </> "shouldwork" </> "SynthesisAttributes") allTargets [] [] "Simple" "main"
        , outputTest ("tests" </> "shouldwork" </> "SynthesisAttributes") allTargets [] [] "Product" "main"
        , outputTest ("tests" </> "shouldwork" </> "SynthesisAttributes") allTargets [] [] "InstDeclAnnotations" "main"
        , runTest "Product" def
        ]
      , clashTestGroup "Testbench"
        [ runTest "TB" def{clashFlags=["-fclash-inline-limit=0"]}
        , runTest "SyncTB" def
        ]
      , clashTestGroup "Types"
        [ runTest "TypeFamilyReduction" def{hdlSim=False}
        , runTest "NatExp" def{hdlSim=False}
        ]
      , clashTestGroup "TopEntity"
        -- VHDL tests disabled for now: I can't figure out how to generate a static name whilst retaining the ability to actually test..
        [ outputTest ("tests" </> "shouldwork" </> "TopEntity") allTargets [] [] "PortGeneration" "main"
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortNamesWithSingletonVector" "main"
        , runTest "TopEntHOArg" def{entities=Entities [["f", "g"]], topEntities=TopEntities ["f"], hdlSim=False}
        , runTest "T701" def {hdlSim=False,entities=Entities [["mynot", ""]]}
        , runTest "T1033" def {hdlSim=False,entities=Entities [["top", ""]], topEntities=TopEntities ["top"]}
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") allTargets [] [] "T1033" "main"
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") allTargets [] [] "T1072" "main"
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") allTargets [] [] "T1074" "main"
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [SystemVerilog] ["-main-is", "topEntity1"] [] "Multiple" "main1"
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [VHDL] ["-main-is", "topEntity3"] [] "Multiple" "main3"
        , runTest "T1139" def{hdlSim=False}
        , let _opts = def { hdlTargets=[Verilog]
                          , entities=Entities [["", "PortNames_topEntity", "PortNames_testBench"]]
                          , topEntities=TopEntities ["PortNames_testBench"]
                          }
           in runTest "PortNames" _opts
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortNames" "main"
        , let _opts = def { hdlTargets=[Verilog]
                          , entities=Entities [["", "PortProducts_topEntity", "PortProducts_testBench"]]
                          , topEntities=TopEntities ["PortProducts_testBench"]
                          }
           in runTest "PortProducts" _opts
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortProducts" "main"
        , let _opts = def { hdlTargets=[Verilog]
                          , entities=Entities [["", "PortProductsSum_topEntity", "PortProductsSum_testBench"]]
                          , topEntities=TopEntities ["PortProductsSum_testBench"]
                          }
           in runTest "PortProductsSum" _opts
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortProductsSum" "main"
        , let _opts = def { hdlTargets=[Verilog]
                          , entities=Entities [["", "PortNamesWithUnit_topEntity", "PortNamesWithUnit_testBench"]]
                          , topEntities=TopEntities ["PortNamesWithUnit_testBench"]
                          }
           in runTest "PortNamesWithUnit" _opts
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortNamesWithUnit" "main"
        , let _opts = def { hdlTargets=[Verilog]
                          , entities=Entities [["", "PortNamesWithVector_topEntity", "PortNamesWithVector_testBench"]]
                          , topEntities=TopEntities ["PortNamesWithVector_testBench"]
                          }
           in runTest "PortNamesWithVector" _opts
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortNamesWithVector" "main"
        , let _opts = def { hdlTargets=[Verilog]
                          , entities=Entities [["", "PortNamesWithRTree_topEntity", "PortNamesWithRTree_testBench"]]
                          , topEntities=TopEntities ["PortNamesWithRTree_testBench"]
                          }
           in runTest "PortNamesWithRTree" _opts
        , outputTest ("tests" </> "shouldwork" </> "TopEntity") [Verilog] [] [] "PortNamesWithRTree" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "TopEntity") allTargets [] "T1182A" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "TopEntity") allTargets [] "T1182B" "main"
        ]
      , clashTestGroup "Unit"
        [ runTest "Imap" def
        , runTest "ZipWithUnitVector" def
        , runTest "ZipWithTupleWithUnitLeft" def
        , runTest "ZipWithTupleWithUnitRight" def
        , runTest "ZipWithTripleWithUnitMiddle" def
        , runTest "ZipWithUnitSP" def
        , runTest "ZipWithUnitSP2" def
        ]
      , clashTestGroup "Vector"
        [ runTest "EnumTypes" def{hdlSim=False}
        , runTest "HOCon" def{hdlSim=False}
        , runTest "VMapAccum" def{hdlSim=False}
        , runTest "VScan" def{hdlSim=False}
        , runTest "VZip" def{hdlSim=False}
        , runTest "VecConst" def{hdlSim=False}
        , runTest "FirOddSize" def
        , runTest "IndexInt" def
        , runTest "Concat" def
        , runTest "DFold" def
        , runTest "DFold2" def
        , runTest "DTFold" def
        , runTest "FindIndex" def
        , runTest "Fold" def
        , runTest "FoldlFuns" def{hdlSim=False}
        , runTest "Foldr" def
        , runTest "FoldrEmpty" def
        , runTest "HOClock" def{hdlSim=False}
        , runTest "HOPrim" def{hdlSim=False}
        , runTest "Indices" def
        , runTest "Iterate" def
        , outputTest ("tests" </> "shouldwork" </> "Vector") [VHDL] [] [] "IterateCF" "main"
        , runTest "Minimum" def
        , runTest "MovingAvg" def{hdlSim=False}
        , runTest "PatHOCon" def{hdlSim=False}
        , runTest "Scatter" def
        , runTest "Split" def{hdlSim=False}
        , runTest "ToList" def
        , runTest "Unconcat" def
        , runTest "VACC" def{hdlSim=False}
        , runTest "VEmpty" def
        , runTest "VIndex" def{hdlSim=False}
        , runTest "VIndicesI" def
        , runTest "VFold" def
        , runTest "VMerge" def
        , runTest "VReplace" def
        , runTest "VReverse" def
        , runTest "VRotate" def
        , runTest "VSelect" def
        , runTest "VecOfSum" def{hdlSim=False}
        , runTest "T452" def{hdlSim=False}
        , let _opts = def { hdlSim = False, hdlTargets = [VHDL]}
           in runTest "T895" _opts
        , let _opts = def { hdlSim = False, hdlTargets = [VHDL], clashFlags = ["-fclash-hdlsyn", "Vivado"]}
           in runTest "T1360" _opts
        ] -- end vector
      , clashTestGroup "XOptimization"
        [ outputTest  ("tests" </> "shouldwork" </> "XOptimization") allTargets [] [] "Conjunction" "main"
        , outputTest  ("tests" </> "shouldwork" </> "XOptimization") allTargets [] [] "Disjunction" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "XOptimization") allTargets [] "OneDefinedDataPat" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "XOptimization") allTargets [] "OneDefinedLitPat" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "XOptimization") allTargets [] "OneDefinedDefaultPat" "main"
        , clashLibTest ("tests" </> "shouldwork" </> "XOptimization") allTargets [] "ManyDefined" "main"
        ]
      ] -- end shouldwork
    ] -- end tests
  ] -- end .

main :: IO ()
main = do
  setEnv "TASTY_NUM_THREADS" (show numCapabilities)
  createDirectoryIfMissing True temporaryDirectory
  setClashEnvs compiledWith
  finally runClashTest (removeDirectoryRecursive temporaryDirectory)
