module BackwardsBinary where

import           Control.Monad
import           Control.Monad.Fix
import           OneHash
import           Text.Printf

add1bb :: Reg -> Reg -> OneHash ()
add1bb r1 result = void $ mfix $ \ ~(nocarry, carry, done) -> do
  comment "begin add1"
  comment "carries"
  carry'   <- label
  cases r1
    (add1 result >> done)
    (addh result >> carry)
    (add1 result >> nocarry)
  comment "no carries"
  nocarry' <- label
  cases r1
    done
    (add1 result >> nocarry)
    (addh result >> nocarry)
  done'    <- label
  comment "end add1"
  return (nocarry', carry', done')

-- | In place variant of add1
add1bb' :: Reg -> OneHash ()
add1bb' rin = withRegs $ \s -> move rin s >> add1bb s rin

-- This function has the additional restriction that all BB numbers have a 1
-- as their most significant digit.
-- This makes things easier and is a generally sensible thing to do
toBB :: Reg -> Reg -> OneHash ()
toBB r result = addh result >> loop' r (add1bb' result) noop

toUnary :: Reg -> Reg -> OneHash ()
toUnary r result = withRegs $ \s -> do
  reverseReg r s
  loop' s (withRegs (double result) >> add1 result) (withRegs $ double result)

-- | Add two backwards binary numbers destructively
addBB' :: Reg -> Reg -> Reg -> OneHash ()
addBB' r1 r2 result = void $ mfix $ \ ~(nocarry, carry, done) -> do
  nocarry' <- label
  cases r1
    (cases r2
       done                       -- 0 ε ε
       (add1 result >> nocarry)   -- 0 ε 1
       (addh result >> nocarry))  -- 0 ε #
    (cases r2
        (add1 result >> nocarry)  -- 0 1 ε
        (addh result >> carry)    -- 0 1 1
        (add1 result >> nocarry)) -- 0 1 #
    (cases r2
        (addh result >> nocarry)  -- 0 # ε
        (add1 result >> nocarry)  -- 0 # 1
        (addh result >> nocarry)) -- 0 # #
  carry' <- label
  cases r1
    (cases r2
       (add1 result >> done)      -- 1 ε ε
       (addh result >> carry)     -- 1 ε 1
       (add1 result >> nocarry))  -- 1 ε #
    (cases r2
       (addh result >> carry)     -- 1 1 ε
       (add1 result >> carry)     -- 1 1 1
       (addh result >> carry))    -- 1 1 #
    (cases r2
       (add1 result >> nocarry)   -- 1 # ε
       (addh result >> carry)     -- 1 # 1
       (add1 result >> carry))    -- 1 # #
  done' <- label
  return (nocarry', carry', done')

-- | Non-destructive version BB addition.
addBB :: Reg -> Reg -> Reg -> OneHash ()
addBB r1 r2 result = withRegs $ \t1 t2 -> do
  copy r1 t1
  copy r2 t2
  addBB' t1 t2 result

-- Save a register into the target register using a special encoding.
-- # -> ##
-- 1 -> #1
-- Stop -> 1
save :: Reg -> Reg -> OneHash ()
save source target = do
  loop' source (addh target >> add1 target) (addh target >> addh target)
  add1 target

-- Restore a register's contents which were saved using the @save@ function.
restore :: Reg -> Reg -> OneHash ()
restore source target = do
  start <- label
  cases source noop noop
    (cases source noop (add1 target >> start) (addh target >> start))

-- Save all other registers to R15
-- saveAll :: OneHash ()
-- saveAll = mapM_ (`save` R15) [R1 .. R14]

-- Restore all registers from R15
-- restoreAll :: OneHash ()
-- restoreAll = mapM_ (restore R15) [R1 .. R14]

clear12 :: OneHash ()
clear12 = void $ mfix $ \ ~(clear1, clear2) -> do
  comment "dispatch table"
  dispatch <- label
  cases r3 noop (cases r3 clear1 clear2 noop) noop
  comment "clear register 1"
  clear1' <- label
  cases r1 (add1 r3 >> add1 r3 >> dispatch) (add1 r3 >> dispatch) (add1 r3 >> dispatch)
  clear2' <- label
  comment "clear register 2"
  cases r2 noop (add1 r3 >> add1 r3 >> dispatch) (add1 r3 >> add1 r3 >> dispatch)
  return (clear1', clear2')

