module BackwardsBinary where

import           Control.Monad
import           Control.Monad.Fix
import           OneHash
import           Text.Printf

add1bb :: Reg -> Reg -> OneHash ()
add1bb r1 result = void $ mfix $ \ ~(nocarry, carry, done) -> do
  carry'   <- label
  cases r1
    (add1 result >> done)
    (addh result >> carry)
    (add1 result >> nocarry)
  nocarry' <- label
  cases r1
    done
    (add1 result >> nocarry)
    (addh result >> nocarry)
  done'    <- label
  return (nocarry', carry', done')

-- | In place variant of add1
add1bb' :: Reg -> OneHash ()
add1bb' r1 = withRegs $ \s -> move r1 s >> add1bb s r1

-- This function has the additional restriction that all BB numbers have a 1
-- as their most significant digit.
-- This makes things easier and is a generally sensible thing to do
toBB :: Reg -> Reg -> OneHash ()
toBB r result = loop' r (add1bb' result) noop

toUnary :: Reg -> Reg -> OneHash ()
toUnary r result = withRegs $ \s -> do
  reverseReg r s
  loop' s (withRegs (double result) >> add1 result) (withRegs $ double result)

addBB :: Reg -> Reg -> Reg -> OneHash ()
addBB r1 r2 result = void $ mfix $ \ ~(nocarry, carry, done) -> do
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

multBB :: Reg -> Reg -> Reg -> OneHash ()
multBB r1 r2 result = void $ mfix $ \ ~(nocarry, carry, done) -> do
  nocarry' <- label
  cases r1 done done done
  carry'   <- label
  cases r1 done done done
  done'    <- label
  return (nocarry', carry', done')

