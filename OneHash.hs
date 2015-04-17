-- By Spenser Bauman
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TypeFamilies               #-}
module OneHash
  ( Reg
  , Scratches (..)
  , OneHash
  , Value (..)
  , compile, compile', compile'', compileValue
  , add1, addh
  , comment
  , cases
  , dispatch
  , label
  , namedLabel
  , loop, loop'
  , while
  , chomp
  , moveChar
  , clear
  , copy, copy'
  , move
  , noop
  , fillCounter
  , add
  , mult
  , power
  , double
  , getCharAt
  , reverseReg
  , r1, r2, r3, r4, r5, r6, r7, r8, r9
  , reg
  , subDestructive
  , withLabels
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix      (mfix)
import           Control.Monad.Identity (runIdentity)
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Function          (on)
import           Data.List              (foldl', unfoldr)
import           Data.Hashable
import qualified Data.HashMap.Strict    as M
import           Data.Maybe             (fromJust, mapMaybe)
import           Prelude                hiding (break)
import           Text.Printf            (printf)

newtype Reg = Reg Int
  deriving (Eq, Enum, Show)

data Value = One | Hash
  deriving Eq

instance Show Value where
  show One  = "1"
  show Hash = "#"

  showList  = foldr ((.) . shows) id

r1, r2, r3, r4, r5, r6, r7, r8, r9 :: Reg
r1 = Reg 1
r2 = Reg 2
r3 = Reg 3
r4 = Reg 4
r5 = Reg 5
r6 = Reg 6
r7 = Reg 7
r8 = Reg 8
r9 = Reg 9

reg :: Int -> Reg
reg = Reg

-- | We treat the first 9 registers as general user registers and the rest are
-- used for scratch space by the register allocator functions below.
scratchRegisters :: [Reg]
scratchRegisters = [Reg 10 .. ]

regIndex :: Reg -> Int
regIndex (Reg i) = i

data Instruction
  = Add1 Reg
  | AddH Reg
  | Label String
  | Jump String
  | Case Reg
  | Nop
  | Comment String
  deriving Show

type Instructions = [Instruction]

data Flattened
  = Add1F Int
  | AddHF Int
  | ForwardF Int
  | BackwardF Int
  | CaseF Int
  | CommentF String
  deriving Show

type LabelMapping = M.HashMap String Int

isComment :: Flattened -> Bool
isComment CommentF{} = True
isComment _          = False

computeMapping :: Instructions -> LabelMapping
computeMapping = foldl' f M.empty . enumInstructions
  where
    f acc (n, Label v) = M.insert v n acc
    f acc _            = acc

enumInstructions :: Instructions -> [(Int, Instruction)]
enumInstructions ys = unfoldr f (ys, 1)
  where
    incr Label{}   = 0
    incr Comment{} = 0
    incr _         = 1

    f ([],   _) = Nothing
    f (i:is, n) = Just ((n, i), (is, incr i + n))

lookupFail :: (Eq a, Hashable a) => a -> M.HashMap a b -> b
lookupFail = (fromJust .) . M.lookup

-- Eliminate zero-length jumps from the program by inserting a no-op operation
-- into the program before any jumps that go backwards to themselves.
-- It is not actually possible to express such a thing in OneHash, but is
-- possible in the DSL, so we handle it gracefully by lengthening the jump
-- length to 1 with a no-op.
fixupZeroJumps :: Instructions -> Instructions
fixupZeroJumps xs = concatMap (uncurry f) $ enumInstructions xs
  where
    f n ins@(Jump x)
      | m == n    = [Nop, ins]
      where m = lookupFail x mapping
    f n ins       = [ins]

    mapping = computeMapping xs

-- Compute the absolute jump locations from the specification given here
computeAddrs :: Instructions -> [Flattened]
computeAddrs (fixupZeroJumps -> xs) =
  concatMap (uncurry relativizeLabel) $ enumInstructions xs
  where
    relativizeLabel n (Jump x)
      | m > n                        = [ForwardF  (m - n)]
      | otherwise                    = [BackwardF (n - m)]
      where m = lookupFail x mapping
    relativizeLabel _ (Case r)       = [CaseF (regIndex r)]
    relativizeLabel _ (Add1 r)       = [Add1F (regIndex r)]
    relativizeLabel _ (AddH r)       = [AddHF (regIndex r)]
    relativizeLabel _ (Comment s)    = [CommentF s]
    relativizeLabel _ Nop            = [ForwardF 1]
    relativizeLabel _ _              = []

    -- Maps labels to instruction indices
    mapping = computeMapping xs

encode' :: [Flattened] -> String
encode' = foldr (++) "" . map enc
  where
    unary :: Int -> String
    unary n = replicate n '1'

    enc :: Flattened -> String
    enc (Add1F r)     = unary r ++ "#"
    enc (AddHF r)     = unary r ++ "##"
    enc (ForwardF r)  = unary r ++ "###"
    enc (BackwardF r) = unary r ++ "####"
    enc (CaseF r)     = unary r ++ "#####"
    enc (CommentF s)  = ";; " ++ s

-- Encode operation which generates fancy LaTeX instructions
encode'' :: [Flattened] -> String
encode'' = unlines . map enc
  where
    unary :: Int -> String
    unary n = "1^{" ++ show n ++ "}"

    enc :: Flattened -> String
    enc (Add1F r)     = unary r ++ "#"
    enc (AddHF r)     = unary r ++ "##"
    enc (ForwardF r)  = unary r ++ "###"
    enc (BackwardF r) = unary r ++ "####"
    enc (CaseF r)     = unary r ++ "#####"
    enc (CommentF s)  = ";; " ++ s

encode :: [Flattened] -> String
encode = unlines . map enc
  where
    unary :: Int -> String
    unary n = replicate n '1'

    enc :: Flattened -> String
    enc (Add1F r)     = unary r ++ "#"
    enc (AddHF r)     = unary r ++ "##"
    enc (ForwardF r)  = unary r ++ "###"
    enc (BackwardF r) = unary r ++ "####"
    enc (CaseF r)     = unary r ++ "#####"
    enc (CommentF s)  = []

encodeValue :: [Flattened] -> [Value]
encodeValue = concatMap enc
  where
    unary :: Int -> [Value]
    unary n = replicate n One

    enc :: Flattened -> [Value]
    enc (Add1F r)     = unary r ++ [Hash]
    enc (AddHF r)     = unary r ++ [Hash, Hash]
    enc (ForwardF r)  = unary r ++ [Hash, Hash, Hash]
    enc (BackwardF r) = unary r ++ [Hash, Hash, Hash, Hash]
    enc (CaseF r)     = unary r ++ [Hash, Hash, Hash, Hash, Hash]
    enc (CommentF _)  = []

execOneHash :: OneHash a -> [Flattened]
execOneHash = computeAddrs . runASM

compileValue :: OneHash a -> [Value]
compileValue = encodeValue . execOneHash

compile :: OneHash a -> String
compile = encode . execOneHash

compile' :: OneHash a -> String
compile'  = encode' . filter (not . isComment) . execOneHash
compile'' = encode''  . execOneHash

newtype Label = MkL { name :: String }
  deriving Show

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
newtype OneHash a = OneHash { unHash :: StateT OneHashState (Writer [Instruction]) a }
  deriving (Functor, Applicative, Monad, MonadState OneHashState, MonadWriter [Instruction], MonadFix)

runASM :: OneHash a -> Instructions
runASM = execWriter . flip evalStateT initial . unHash
  where
    initial = OneHashState { counter = 0, temps = scratchRegisters }

add1, addh :: Reg -> OneHash ()
add1 r = tell [Add1 r]
addh r = tell [AddH r]

comment :: String -> OneHash ()
comment s = tell [Comment s]

cases :: Reg -> OneHash () -> OneHash () -> OneHash () -> OneHash ()
cases r c1 c2 c3 = void $ mfix $ \ ~(j1, j2, jend) -> do
  -- The first two clauses for a case are jumps to their respective segments
  -- The final case falls through to c3.
  -- The c2 clause is the last segment of code for the case statement, so
  -- its fallthrough behaviour take us out of the case statement
  tell [Case r] >> j1 >> j2 >> c3 >> jend
  liftA3 (,,) (label <* c1 <* jend) (label <* c2) label

-- A variant of cases with fallthrough semantics.
dispatch :: Reg -> OneHash () -> OneHash () -> OneHash () -> OneHash ()
dispatch r c1 c2 c3 = void $ mfix $ \ ~(j1, j2, j3) -> do
  tell [Case r] >> j1 >> j2 >> j3
  liftA3 (,,) (label <* c1) (label <* c2) (label <* c3)

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

-- Emulate the with-labels operation found in William Byrd's solution.
withLabels :: (OneHash () -> OneHash () -> OneHash ()) -> OneHash ()
withLabels body = void $ mfix $ \ ~(start, end) ->
  (,) <$> label <* body start end <*> label

-- Produces a loop where the two function are called depending on which value
-- is in the loop register.
-- The actions supplied to each function correspond to continue and break
-- operations
loop :: Reg                                      -- Loop control register
     -> (OneHash () -> OneHash () -> OneHash ()) -- Got a 1
     -> (OneHash () -> OneHash () -> OneHash ()) -- Got a #
     -> OneHash ()
loop r one hash = withLabels $ \cont break ->
  cases r break (one cont break >> cont) (hash cont break >> cont)

k² :: a -> b -> c -> a
k² = const . const

-- Like `loop`, but the two conditions do not care about
loop' :: Reg -> OneHash () -> OneHash () -> OneHash ()
loop' r = loop r `on` k²

-- Loop on a register performing the same action disregarding the character
-- from the loop control register.
-- Though this function is convenient, it duplicates the code for `m`, so
-- consider using `loop'` if you only expect one character type to be in `r`.
while :: Reg -> OneHash () -> OneHash ()
while r m = withLabels $ \start end -> cases r end noop noop >> m >> start

-- Functions for register allocation
popReg :: OneHash Reg
popReg = do
  st <- get
  case temps st of
       x:xs -> put st { temps = xs } >> return x

pushReg :: Reg -> OneHash ()
pushReg r = modify $ \st -> st { temps = r : temps st }

-- Allocate a single register from the scratch pool and supply it to the
-- given function.
-- Users must take care to never return a register from this function, doing
-- so will have unexpected results in the generated program.
withScratchRegister :: (Reg -> OneHash a) -> OneHash a
withScratchRegister f = popReg >>= \r -> f r <* pushReg r

class Scratches a where
  type Result a :: *
  withRegs  :: a -> OneHash (Result a)
  -- Variant which does not ensure that the scratch register is empty.
  withRegs' :: a -> OneHash (Result a)

instance Scratches (OneHash a) where
  type Result (OneHash a) = a
  withRegs  = id
  withRegs' = id

instance Scratches b => Scratches (Reg -> b) where
  type Result (Reg -> b) = Result b
  withRegs f = withScratchRegister $ \r -> withRegs (f r) <* clear r
  withRegs'  = withScratchRegister . (withRegs' .)

noop :: OneHash ()
noop = return ()

chomp :: Reg -> OneHash ()
chomp reg = cases reg noop noop noop

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
fillCounter r n = replicateM_ n (add1 r)

add' :: Reg -> Reg -> Reg -> Reg -> OneHash ()
add' n m result scratch = copy' n result scratch >> copy' m result scratch

add :: Reg -> Reg -> Reg -> OneHash ()
add n m result = withRegs $ add' n m result

mult' :: Reg -> Reg -> Reg -> Reg -> Reg -> OneHash ()
mult' n m result s1 s2 = do
  copy' m s2 s1
  loop' s2 (copy' n result s1) noop

-- This function will not work if the result register matches either of the
-- source registers.
mult :: Reg -> Reg -> Reg -> OneHash ()
mult n m result = withRegs $ \s ->
  copy m s >> loop' s (copy n result) noop

multDestructive :: Reg -> Reg -> Reg -> OneHash ()
multDestructive n m result = loop' m (copy n result) noop

power :: Reg -> Reg -> Reg -> OneHash ()
power n m result = withRegs $ \s s' -> do
  comment $ printf "%s = %s ^ %s" (show result) (show n) (show m)
  copy m s
  add1 result
  loop' s (multDestructive n result s' >> move s' result) noop
  comment $ printf "done computing power"

-- Gets the character in the source register and places it at the target
-- register
getCharAt :: Reg -> Reg -> Reg -> OneHash ()
getCharAt source target idx = withRegs $ \b1 b2 -> do
  -- Backup the source register into s1
  copy source b1
  copy idx    b2
  -- Discard idx # of characters from source
  while idx $ chomp source
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
  loop work (k² $ add1 s1 >> add1 s1) (\_ br -> br)
  move s1 work

reverseReg :: Reg -> Reg -> OneHash ()
reverseReg source target = withRegs $ \idx -> do
  comment $ "reversing register " ++ show source ++ " into " ++ show target
  copy source idx
  while idx $
    getCharAt source target idx
  comment "done reversing"

-- Algorithm for computing 2^n
prob4 :: Int -> OneHash ()
prob4 n = withRegs' $ \temp -> do
  fillCounter temp n
  add1 r1
  loop' temp (double r1 r2) noop

subDestructive :: Reg -> Reg -> OneHash ()
subDestructive n m = while m (chomp n)

