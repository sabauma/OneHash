{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module U where

import           Prelude hiding (init)
import           Control.Monad
import           OneHash
import           Phi           hiding (decode)
import           Text.Printf

-- It's worth noting that if we "encode" the program via the operation
-- called toEncoding below, we can totally get away with using lookup
-- for both R4 and the program instructions in R1 by abstracting it a
-- bit more.
----------------------------------------------------------------------------
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
  comment "begin step function"
  cases r3 end end  noop
  cases r3 end (add1 r5 >> move r3 r5 >> write1  end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> writeh  end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> jumpadd end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> jumpsub end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> caseh   end) noop
  comment "end step function"
    where
      write1  end = lookupReg >> add1 r6 >> updateReg >> add1 r2 >> end
      writeh  end = lookupReg >> addh r6 >> updateReg >> add1 r2 >> end
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
  comment $ printf "encode program in %s into %s" (show r) (show r')
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
  comment "end encode function"

-- Generate the desired encoding of data, which is slightly different than for
-- code, which will separate instructions by ##.
-- This converts the entire contents of rin to the encoding and places
-- a terminatior at the end.
toDataEncoding :: Reg -> Reg -> OneHash()
toDataEncoding rin rout = do
  comment $ printf "encode data in %s into %s" (show rin) (show rout)
  loop' rin (add1 rout >> add1 rout) (add1 rout >> addh rout)
  addh rout
  addh rout
  comment "end data encoding"

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

lookupInstr :: Reg -> Reg -> Reg -> OneHash ()
lookupInstr rin n rout = withRegs $ \rtmp -> do
  lookupReg' rin n rtmp
  reverseReg rtmp rout

----------------------------------------------------------------------------
-- Should update the nth register of r4 with the value in r6 where
-- r5 = 1^n
updateReg :: OneHash ()
updateReg = updateReg' r4 r5 r6

updateReg' :: Reg -> Reg -> Reg -> OneHash ()
updateReg' regSet n val = withRegs $ \n' tmp -> do
  copy n n'
  chomp n'
  -- Seek to the desired register
  loop' n' (eatCell regSet tmp >> addh tmp >> addh tmp) noop
  -- Consume the current register and throw it away
  withRegs $ decode regSet
  toDataEncoding val tmp
  -- Move everything back
  move regSet tmp
  move tmp regSet

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
test3 = phi (compileValue $ updateReg' r1 r2 r3 >> updateReg' r1 r4 r5) [[], [One, One, One], [Hash]]
test4 = phi (compileValue $ lookupReg' r1 r2 r3) [[Hash, Hash, One, Hash, Hash, Hash], [One, One]]


----------------------------------------------------------------------------

init :: OneHash ()
init = do
  toEncoding r1 r2
  move r2 r1
  add1 r2

cleanup :: OneHash ()
cleanup = do
  clear r1
  clear r5
  add1 r5
  lookupReg
  decode r6 r1
  clear r2
  clear r3
  clear r4
  clear r5

mainLoop :: OneHash ()
mainLoop = withRegs $ \ (emptyreg :: Reg) -> mdo
  init
  lookupInstr r1 r2 r3
  step
  lookupInstr r1 r2 r3
  step
 -- loop <- label
 -- cmp r3 emptyreg (end) (noop)
 -- step
 -- loop
 -- end <- label
 -- cleanup

-- R1: the input program p
-- R2: an instruction number 1n
-- R3: the nth instruction of p
-- R4: the contents of all regsiters, encoded as above
-- R5: the register to be manipulated (a number)
-- R6: lookupReg puts it here

-- Pick an action depending on whether or not two things are equal
cmp :: Reg -> Reg -> OneHash () -> OneHash () -> OneHash ()
cmp a b eq neq = withRegs $ \s1 s2 -> do
  copy a s1
  copy b s2
  withLabels $ \start end -> do
    cases s1
      (cases s2 (eq >>  end) (neq >> end) (neq >> end))
      (cases s2 (neq >> end) start        (neq >> end))
      (cases s2 (neq >> end) (neq >> end) start)
    clear s1 >> clear s2

