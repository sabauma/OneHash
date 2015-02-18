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

