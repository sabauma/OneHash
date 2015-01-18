{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
module OneHash
  ( Reg (..)
  , Scratches (..)
  , OneHash
  , compile
  , add1, addh
  , cases
  , label
  , loop, loop'
  , while
  , eatChar
  , moveChar
  , clear
  , copy, copy'
  , move
  , noop
  , fillCounter
  , add, add'
  , mult, mult'
  , getCharAt
  , reverseReg
  ) where

import           Prelude                hiding (break)
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix      (mfix)
import           Control.Monad.Identity (runIdentity)
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Function          (on)
import           Data.List              (unfoldr)
import           Data.Maybe             (fromJust, mapMaybe)

data Reg = R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  deriving (Eq, Enum, Show)

scratchRegisters :: [Reg]
scratchRegisters = [R10 .. R15]

regIndex :: Reg -> Int
regIndex = (+1) . fromEnum

data Ins
  = Add1 Reg
  | AddH Reg
  | Label String
  | Jump String
  | Case Reg -- Instructions Instructions Instructions
  deriving Show

type Instructions = [Ins]

data Flattened
  = Add1F Int
  | AddHF Int
  | ForwardF Int
  | BackwardF Int
  | CaseF Int
  deriving (Show)

computeMapping :: Instructions -> [(String, Int)]
computeMapping = mapMaybe f . enumInstructions
  where
    f (n, Label v) = Just (v, n)
    f _            = Nothing

enumInstructions :: Instructions -> [(Int, Ins)]
enumInstructions ys = unfoldr f (ys, 1)
  where
    incr Label{} = 0
    incr _       = 1

    f ([],   _) = Nothing
    f (i:is, n) = Just ((n, i), (is, incr i + n))

lookupFail :: Eq a => a -> [(a, b)] -> b
lookupFail = (fromJust .) . lookup

-- Compute the absolute jump locations from the specification given here
computeAddrs :: Instructions -> [Flattened]
computeAddrs xs = concatMap (uncurry relativizeLabel) $ enumInstructions xs
  where
    relativizeLabel n (Jump x)
      | m > n                        = [ForwardF  (m - n)]
      | otherwise                    = [BackwardF (n - m)]
      where m = lookupFail x mapping
    relativizeLabel _ (Case r)       = [CaseF (regIndex r)]
    relativizeLabel _ (Add1 r)       = [Add1F (regIndex r)]
    relativizeLabel _ (AddH r)       = [AddHF (regIndex r)]
    relativizeLabel _ _              = []

    -- Maps labels to instruction indices
    mapping = computeMapping xs

unary :: Int -> String
unary n = replicate n '1'

encode :: [Flattened] -> String
encode = unlines . map enc
  where
    enc :: Flattened -> String
    enc (Add1F r)     = unary r ++ "#"
    enc (AddHF r)     = unary r ++ "##"
    enc (ForwardF r)  = unary r ++ "###"
    enc (BackwardF r) = unary r ++ "####"
    enc (CaseF r)     = unary r ++ "#####"

-- example2 = [Label "Start", Case R3 [Jump "Done"] [Add1 R1] [Add1 R2], Jump "Start", Label "Done"]
--
-- example =
--   [ Label "Start"
--   , Case R1 [Jump "Done1"] [Add1 R3, Jump "Start"] [Jump "Exit"]
--   , Label "Done1"
--   , Label "Start2"
--   , Case R2 [Jump "Done2"] [Add1 R3, Jump "Start"] [Jump "Exit"]
--   , Label "Done2"
--   , Label "Exit"
--   ]

compile :: OneHash a -> String
compile = encode . computeAddrs . runASM

newtype Label = MkL { name :: String }
  deriving (Show)

data OneHashState = OneHashState
  { counter :: !Int
  , temps   :: [Reg]
  } deriving (Show)


-- A monad for generating 1# program.
-- The monadic actions are compiled down to a more reasonable version of 1# with
-- features like direct jumps and labels, and nestable case statements which
-- behave more like case statements in standard languages.
-- This intermediate representation is then converted to a sequence of 1#
-- instructions.
newtype OneHash a = OneHash { unHash :: StateT OneHashState (Writer [Ins]) a }
  deriving (Functor, Applicative, Monad, MonadState OneHashState, MonadWriter [Ins], MonadFix)

runASM :: OneHash a -> Instructions
runASM = runIdentity . execWriterT . flip evalStateT initial . unHash
  where
    initial = OneHashState { counter = 0, temps = scratchRegisters }

add1, addh :: Reg -> OneHash ()
add1 r = tell [Add1 r]
addh r = tell [AddH r]

mkClause :: OneHash () -> OneHash () -> OneHash (OneHash ())
mkClause c end = label <* c <* end

cases :: Reg -> OneHash () -> OneHash () -> OneHash () -> OneHash ()
cases r c1 c2 c3 = void $ mfix $ \ ~(j1, j2, j3, jend) -> do
  -- Make a case statement with the 3 jumps directly after it.
  -- This could produce fewer instructions by going directly to the third clause
  -- without an intervening jump.
  tell [Case r] >> j1 >> j2 >> j3
  (,,,) <$> mkClause c1 jend <*> mkClause c2 jend <*> mkClause c3 jend <*> label

newLabelName :: String -> OneHash Label
newLabelName nm = do
  st <- get
  put $ st { counter = counter st + 1 }
  return $ MkL $ "LABEL_" ++ nm ++ show (counter st)

jump :: Label -> OneHash ()
jump l = tell [Jump $ name l]

emitLabel :: Label -> OneHash ()
emitLabel l = tell [Label $ name l]

-- Produce a label at the invoked location with a name based on the given
-- string. The name is purely for diagnostic purposes.
-- The action returned jumps to the label that was generated.
namedLabel :: String -> OneHash (OneHash ())
namedLabel nm = do
  l <- newLabelName nm
  emitLabel l
  return $ jump l

-- Generates a label which can be jumped to using the returned OneHash action.
label :: OneHash (OneHash ())
label = namedLabel ""

-- Produces a loop where the two function are called depending on which value
-- is in the loop register.
-- The actions supplied to each function correspond to continue and break
-- operations
loop :: Reg                                      -- Loop control register
     -> (OneHash () -> OneHash () -> OneHash ()) -- Got a 1
     -> (OneHash () -> OneHash () -> OneHash ()) -- Got a #
     -> OneHash ()
loop r one hash = void $ mfix $ \ ~(continue, break) -> do
  continue' <- label
  cases r break (one continue break >> continue) (hash continue break >> continue)
  break'    <- label
  return (continue', break')

k2 :: a -> b -> c -> a
k2 = const . const

-- Like `loop`, but the two conditions do not care about
loop' :: Reg -> OneHash () -> OneHash () -> OneHash ()
loop' r = loop r `on` k2

-- Loop on a register performing the same action disregarding the character
-- from the loop control register.
while :: Reg -> OneHash () -> OneHash ()
while r m = loop' r m m

-- Functions for register allocation
popReg :: OneHash Reg
popReg = do
  st <- get
  case temps st of
       []     -> error "no free temp registers"
       (x:xs) -> put st { temps = xs } >> return x

pushReg :: Reg -> OneHash ()
pushReg r = modify (\st -> st { temps = r : temps st })

-- Allocate a single register from the scratch pool and supply it to the
-- given function.
withScratchRegister :: (Reg -> OneHash ()) -> OneHash ()
withScratchRegister f = popReg >>= \r -> f r >> pushReg r

class Scratches a where
  withRegs  :: a -> OneHash ()
  -- Variant which does not ensure that the scratch register is empty
  withRegs' :: a -> OneHash ()

instance Scratches (OneHash a) where
  withRegs  = void
  withRegs' = void

instance Scratches b => Scratches (Reg -> b) where
  withRegs  f = withScratchRegister $ \r -> clear r >> withRegs' (f r)
  withRegs' f = withScratchRegister (withRegs . f)

noop :: OneHash ()
noop = return ()

eatChar :: Reg -> OneHash ()
eatChar reg = cases reg noop noop noop

moveChar :: Reg -> Reg -> OneHash ()
moveChar r1 r2 = cases r1 noop (add1 r2) (addh r2)

-- Empty out a register
clear :: Reg -> OneHash ()
clear r = while r noop

-- Perform a copy from the source to the target register using an intermediate
-- scratch pad.
copy' :: Reg -> Reg -> Reg -> OneHash ()
copy' source target scratch = do
  loop' source  (add1 scratch)               (addh scratch)
  loop' scratch (add1 target >> add1 source) (addh target >> addh source)

copy :: Reg -> Reg -> OneHash ()
copy s t = withRegs $ copy' s t

-- Move which retains ordering
move :: Reg -> Reg -> OneHash ()
move source target = loop' source (add1 target) (addh target)

-- Fill a counter register with a given number of 1's
fillCounter :: Reg -> Int -> OneHash ()
fillCounter r n = void $ replicateM n (add1 r)

add' :: Reg -> Reg -> Reg -> Reg -> OneHash ()
add' n m result scratch = copy' n result scratch >> copy' m result scratch

add :: Reg -> Reg -> Reg -> OneHash ()
add n m result = withRegs $ add' n m result

-- Destructive multiplication
mult' :: Reg -> Reg -> Reg -> Reg -> OneHash ()
mult' n m result scratch = loop m (k2 $ copy' n result scratch) (\_ br -> br)

mult :: Reg -> Reg -> Reg -> OneHash ()
mult n m result = withRegs $ mult' n m result

-- Gets the character in the source register and places it at the target
-- register
getCharAt :: Reg -> Reg -> Reg -> OneHash ()
getCharAt source target idx = withRegs $ \b1 b2 -> do
  -- Backup the source register into s1
  copy source b1
  copy idx    b2
  -- Discard idx # of characters from source
  while idx $ eatChar source
  -- Move the character from source to the target
  moveChar source target
  -- Restore the saved source and index register from the backup copies
  -- the backup.
  clear source
  move b1 source
  move b2 idx

-- Compute the square of a given register using second register as a scratch
-- pad.
double :: Reg -> Reg -> OneHash ()
double work s1 = do
  loop work (k2 $ add1 s1 >> add1 s1) (\_ br -> br) >> move s1 work
  move s1 work

reverseReg :: Reg -> Reg -> OneHash ()
reverseReg source target = withRegs $ \idx -> do
  withRegs $ copy source idx
  while idx $
    getCharAt source target idx

