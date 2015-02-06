{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RecursiveDo                #-}

module U where

import           Control.Monad
import           OneHash
import           Phi           hiding (decode)


-- It's worth noting that if we "encode" the program via the operation
-- called toEncoding below, we can totally get away with using lookup
-- for both R4 and the program instructions in R1 by abstracting it a
-- bit more.
----------------------------------------------------------------------------
-- The "step" step.
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
step :: OneHash ()
step = withLabels $ \ start end -> mdo
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
      caseh   end = lookupReg >> cases r6 (add1 r2)
                                   (add1 r2 >> add1 r2)
                                   (add1 r2 >> add1 r2 >> add1 r2)
                              >> updateReg >> end

----------------------------------------------------------------------------
-- Turns a register r into the encoded version via r7 as:
-- 1     => 11
-- #     => 1#
-- empty => ##
-- This program will also separate strings of 1^n#^m via ##, such as
-- 1#1# => 111# ## 111#
toEncoding :: Reg -> Reg -> OneHash ()
toEncoding r r' = withLabels $ \ start end -> mdo
  cases r (addh r' >> addh r' >> end)
          (add1 r' >> add1 r' >> oneloop)
          (add1 r' >> addh r' >> hashloop)
  oneloop <- label
  cases r (addh r' >> addh r' >> end)
          (add1 r' >> add1 r' >> oneloop)
          (add1 r' >> addh r' >> hashloop)
  hashloop <- label
  cases r (addh r' >> addh r' >> end)
          (addh r' >> addh r' >> add1 r' >> add1 r' >> oneloop)
          (add1 r' >> addh r' >> hashloop)

-- Generate the desired encoding of data, which is slightly different than for
-- code, which will separate instructions by ##.
-- This converts the entire contents of rin to the encoding and places
-- a terminatior at the end.
toDataEncoding :: Reg -> Reg -> OneHash()
toDataEncoding rin rout = do
  loop' rin (add1 rout >> add1 rout) (add1 rout >> addh rout)
  addh rout
  addh rout

-- Decode one cell on an encoded tape
decode :: Reg -> Reg -> OneHash ()
decode rin rout = do
  start <- label
  cases rin noop
    (cases rin noop (add1 rout >> start) (addh rout >> start))
    (cases rin noop noop noop)

-- Eats a cell in the encoding, but does not decode it.
-- This will not save the trailing termination character.
eatCell :: Reg -> Reg -> OneHash ()
eatCell rin rout = do
  start <- label
  cases rin noop
    (add1 rout >> cases rin noop (add1 rout >> start) (addh rout >> start))
    (cases rin noop noop noop)

----------------------------------------------------------------------------
-- Should look at r4 and find the nth register where r5 = 1^n
-- and place the resulting register in r6. It should also preserve
-- r5 maybe.
lookupReg :: OneHash ()
lookupReg = lookupReg' r4 r5 r6

lookupReg' :: Reg -> Reg -> Reg -> OneHash ()
lookupReg' rin n rout = withRegs $ \rin' n' -> do
  -- Copy registers to preserve their contents
  copy rin  rin'
  copy n    n'
  -- Convert to 0-indexing
  chomp n'
  -- Consume the first n things
  loop' n' (decode rin' rout) noop
  clear rout
  -- Decode the current value into rout
  decode rin' rout

updateReg' :: Reg -> Reg -> Reg -> OneHash ()
updateReg' regSet n val = withRegs $ \n' tmp -> do
  copy n n'
  chomp n'
  -- Seek to the desired register
  loop' n' (eatCell regSet tmp >> addh tmp >> addh tmp) noop
  -- Consume the current register and throw it away
  withRegs $ eatCell regSet
  toDataEncoding val tmp
  -- Move everything back
  move regSet tmp
  move tmp regSet

----------------------------------------------------------------------------
-- Should update the nth register of r4 with the value in r6 where
-- r5 = 1^n
updateReg :: OneHash ()
updateReg = updateReg' r4 r5 r6

testLookup :: OneHash ()
testLookup = do
  forM_ [1 .. 10] (\i -> replicateM_ i (add1 r1) >> addh r1)
  toEncoding r1 r2
  replicateM_ 4 (add1 r3)
  lookupReg' r2 r3 r4

testUpdate :: OneHash ()
testUpdate = do
  forM_ [1 .. 10] $ \i -> replicateM_ i (add1 r1) >> addh r1
  toEncoding r1 r2
  replicateM_ 10 $ add1 r3 >> updateReg' r2 r3 r4

test1 = phi (compileValue testLookup) []
test2 = phi (compileValue testUpdate) []

