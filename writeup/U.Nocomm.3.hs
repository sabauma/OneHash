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

