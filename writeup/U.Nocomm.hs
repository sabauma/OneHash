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

step :: OneHash ()
step = withLabels $ \ start end -> mdo
  comment "begin step function"
  clear r5
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

toDataEncoding :: Reg -> Reg -> OneHash()
toDataEncoding rin rout = do
  comment $ printf "encode data in %s into %s" (show rin) (show rout)
  loop' rin (add1 rout >> add1 rout) (add1 rout >> addh rout)
  addh rout
  addh rout
  comment "end data encoding"

decode :: Reg -> Reg -> OneHash ()
decode rin rout = do
  start <- label
  cases rin noop
    (cases rin noop (add1 rout >> start) (addh rout >> start))
    (cases rin noop noop noop)

eatCell :: Reg -> Reg -> OneHash ()
eatCell rin rout = do
  start <- label
  cases rin noop
    (add1 rout >> cases rin noop (add1 rout >> start) (addh rout >> start))
    (cases rin noop noop noop)

lookupReg :: OneHash ()
lookupReg = lookupReg' r4 r5 r6

lookupReg' :: Reg -> Reg -> Reg -> OneHash ()
lookupReg' rin n rout = withRegs $ \rin' n' -> do
  copy rin  rin'
  copy n    n'
  chomp n'
  loop' n' (decode rin' rout) noop
  clear rout
  decode rin' rout

lookupInstr :: OneHash ()
lookupInstr = withRegs $ \rtmp -> do
  lookupReg' r1 r2 rtmp
  reverseReg rtmp r3

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
  move r6 r1
  clear r2
  clear r3
  clear r4
  clear r5

-- R1: the input program p
-- R2: an instruction number 1n
-- R3: the nth instruction of p
-- R4: the contents of all regsiters, encoded as above
-- R5: the register to be manipulated (a number)
-- R6: lookupReg puts it here



mainLoop :: OneHash ()
mainLoop = withRegs $ \ (emptyreg :: Reg) -> mdo
  init
  loop <- label
  lookupInstr
  cmp r3 emptyreg (end) (noop)
  step
  loop
  end <- label
  cleanup

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

