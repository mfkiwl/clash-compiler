module I2C where

import Clash.Prelude

import I2C.BitMaster
import I2C.ByteMaster
import I2C.Types

{-# ANN i2c
  (Synthesize
    { t_name     = "i2c"
    , t_inputs   = [ PortName "clk"
                   , PortName "arst"
                   , PortName "rst"
                   , PortName "ena"
                   , PortName "clkCnt"
                   , PortName "start"
                   , PortName "stop"
                   , PortName "read"
                   , PortName "write"
                   , PortName "ackIn"
                   , PortName "din"
                   , PortName "i2cI"]
    , t_output   = PortProduct ""
                     [ PortName "dout"
                     , PortName "hostAck"
                     , PortName "busy"
                     , PortName "al"
                     , PortName "ackOut"
                     , PortProduct "" [PortName "i2cO_clk"]
                     ]
    }) #-}
i2c :: Clock System
                                  -> Reset System
                                  -> Signal "System" Bool
                                  -> Signal "System" Bool
                                  -> Signal "System" (Unsigned 16)
                                  -> Signal "System" Bool
                                  -> Signal "System" Bool
                                  -> Signal "System" Bool
                                  -> Signal "System" Bool
                                  -> Signal "System" Bool
                                  -> Signal "System" (BitVector 8)
                                  -> Signal "System" (Bit, Bit)
                                  -> (Signal "System" (BitVector 8), Signal "System" Bool,
                                      Signal "System" Bool, Signal "System" Bool, Signal "System" Bool,
                                      Signal "System" (Bit, Bool, Bit, Bool))
i2c clk arst rst ena clkCnt start stop read write ackIn din i2cI = (dout,hostAck,busy,al,ackOut,i2cO)
  where
    (hostAck,ackOut,dout,bitCtrl) = unbundle (pure (False, False, 0, (I2Cnop, 0)))
    (bitResp,busy,i2cO)           = unbundle (pure ((False, False, 0), False, (0, False, 0, False)))
    (cmdAck,al,dbout)             = unbundle bitResp
{-# INLINE i2c #-}
