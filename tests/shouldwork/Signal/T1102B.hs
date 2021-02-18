module T1102B where

import Clash.Prelude
import qualified Prelude as P
import Data.List (isInfixOf)
import System.Environment (getArgs)
import System.FilePath ((</>), takeDirectory)


{-# NOINLINE topEntity #-}
{-# ANN topEntity Synthesize {t_name = "top", t_inputs = [PortName "x"], t_output = PortName "y"} #-}
topEntity
  :: Signal System (Int, Int, Int, Int, Int)
  -> Signal System (Int, Int, Int, Int, Int)
topEntity = bundle . unbundle

assertIn :: String -> String -> IO ()
assertIn needle haystack
  | needle `isInfixOf` haystack = return ()
  | otherwise                   = P.error $ P.concat [ "Expected:\n\n  ", needle
                                                     , "\n\nIn:\n\n", haystack ]

mainVHDL :: IO ()
mainVHDL = do
  [topDir] <- getArgs
  content <- readFile (takeDirectory topDir </> "top/top.vhdl")

  -- TODO: Could we remove bitvector noise?
  assertIn "x_0 <= top_types.fromSLV(x);" content
  assertIn "y_0 <= x_0;" content
