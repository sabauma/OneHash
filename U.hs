{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RecursiveDo      #-}

module U where

import OneHash
import Phi


-- It's worth noting that if we "encode" the program via the operation
-- called toEncoding below, we can totally get away with using lookup
-- for both R4 and the program instructions in R1 by abstracting it a
-- bit more.
----------------------------------------------------------------------------
-- The "green" step.
--
-- Assumptions:
--
-- 0) The registers are as follows:
--      R1: the input program p
--      R2: an instruction number 1n
--      R3: the nth instruction of p
--      R4: the contents of all regsiters, encoded as above
--
-- 1) It uses R5 as the register being manipulated (denoted as n below)
--
-- 2) lookupReg will look up the nth register and place it in R6, preserving
--    R5
--
-- 3) updateReg will update up the nth register with the value in R6
--
-- 4) The program is pre-parsed into:
--      1^n#     => #1^n
--      1^n##    => ##11^n
--      1^n###   => ###1^n
--      1^n####  => ####1^n
--      1^n##### => #####1^n
--
green :: OneHash ()
green = withLabels $ \ start end -> mdo
  cases r3 end end  noop
  cases r3 end (add1 r5 >> move r3 r5 >> write1  end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> writeh  end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> jumpadd end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> jumpsub end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> caseh   end) noop
    where
      write1  end = lookupReg >> add1 r6 >> updateReg >> end
      writeh  end = lookupReg >> addh r6 >> updateReg >> end
      jumpadd end = move r5 r2 >> end
      jumpsub end = subDestructive r2 r5 >> end
      caseh   end = lookupReg >> (cases r6 (add1 r2)
                                       (add1 r2 >> add1 r2)
                                       (add1 r2 >> add1 r2 >> add1 r2))
                          >> updateReg >> end

----------------------------------------------------------------------------
-- Turns a register r into the encoded version via r7 as:
-- 1     => 11
-- #     => 1#
-- empty => ##
-- This program will also separate strings of 1^n#^m via ##, such as
-- 1#1# => 111# ## 111#
toEncoding :: OneHash ()
toEncoding r = withLabels $
              \ start end -> mdo
                  cases r (addh r7 >> addh r7 >> move r7 r >> end)
                          (add1 r7 >> add1 r7 >> oneloop)
                          (add1 r7 >> addh r7 >> hashloop)
                  oneloop <- label
                  cases r (addh r7 >> addh r7 >> move r7 r >> end)
                          (add1 r7 >> add1 r7 >> oneloop)
                          (add1 r7 >> addh r7 >> hashloop)
                  hashloop <- label
                  cases r (addh r7 >> addh r7 >> move r7 r >> end)
                          (addh r7 >> addh r7 >> add1 r7 >> add1 r7 >> oneloop)
                          (add1 r7 >> addh r7 >> hashloop)

----------------------------------------------------------------------------
-- Should look at r4 and find the nth register where r5 = 1^n
-- and place the resulting register in r6. It should also preserve
-- r5 maybe.
lookupReg :: Reg -> Reg -> OneHash ()
lookupReg rin n = undefined

----------------------------------------------------------------------------
-- Should update the nth register of r4 with the value in r6 where
-- r5 = 1^n
updateReg = undefined


