module Phi
  ( Value (..)
  , phi
  , phi'
  , decode
  , fromChar
  , extract
  ) where

import           Control.Applicative
import qualified Data.IntMap         as M
import qualified Data.Sequence       as S
import qualified Data.Vector         as V
import           OneHash             (Value (..))
import           Data.Foldable       (toList)

type Register = S.Seq Value

data Opcode
  = Write1
  | WriteH
  | Forward
  | Backward
  | Cases
  deriving (Show, Enum)

type Instruction = (Opcode, Int)
type Program     = [Instruction]
type State       = M.IntMap Register

fromChar :: Char -> Value
fromChar '1' = One
fromChar '#' = Hash
fromChar _   = error "fromChar: not a 1# character"

toOpcode :: [Value] -> Opcode
toOpcode xs
  | all (== Hash) xs = toEnum $ pred $ length xs
  | otherwise        = error "unknown operation"

decode :: [Value] -> Program
decode []                                = []
decode xs
  | not (null hashes) && not (null ones) = (toOpcode hashes, length ones) : decode rest'
  | otherwise                            = error "invalid sequence"
  where
    (ones  , rest)  = break (/= One) xs
    (hashes, rest') = break (/= Hash) rest

appendRegister :: State -> Int -> Value -> State
appendRegister s n v = M.insertWith (flip (S.><)) n (S.singleton v) s

gobbleRegister :: State -> Int -> (Maybe Value, State)
gobbleRegister s n =
  case S.viewl <$> M.lookup n s of
       Just (v S.:< seq) -> (Just v , M.insert n seq s)
       _                 -> (Nothing, s)

offset :: Maybe Value -> Int
offset Nothing     = 1
offset (Just One)  = 2
offset (Just Hash) = 3

phi :: [Value] -> [[Value]] -> State
phi p st = phi' (decode p) (M.fromList $ zip [1 ..] $ map S.fromList st)

phi' :: Program -> State -> State
phi' p = go 0
  where

    v = V.fromList p

    go :: Int -> State -> State
    go n st
      | n >= V.length v || n < 0 = st
      | otherwise                = uncurry go $ step n st

    step :: Int -> State -> (Int, State)
    step n s =
      let (op, r) = v V.! n
      in case op of
             Write1   -> (n + 1, appendRegister s r One)
             WriteH   -> (n + 1, appendRegister s r Hash)
             Forward  -> (n + r, s)
             Backward -> (n - r, s)
             Cases    -> let (g, s') = gobbleRegister s r in (n + offset g, s')

extract :: State -> [Value]
extract st = toList $ st M.! 1

