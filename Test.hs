
module Test where

import           Phi
import           OneHash

program = map fromChar "1#1#1#1##1#####111###11###1###"

write :: OneHash ()
write = withRegs $ \s -> do
  move r1 s
  loop' s (add1 r1 >> addh r1) (add1 r1 >> addh r1 >> addh r1)

pgm :: [Value]
pgm = compileValue write

φ :: [Value] -> [Value] -> [Value]
φ r1 p = extract (phi p [r1])

example = φ [] $ φ program pgm
