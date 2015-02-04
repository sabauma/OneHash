
module Test where

import           Phi
import           OneHash

program = map fromChar "1#1#1#1##1#####111###11###1###"

write :: OneHash ()
write = withRegs $ \s -> do
  move r1 s
  loop' s (add1 r1 >> addh r1) (add1 r1 >> addh r1 >> addh r1)

diag :: OneHash ()
diag = do
  copy r1 r2
  write
  move r2 r1

diag'  = compileValue diag
write' = compileValue write

pgm :: [Value]
pgm = compileValue write

φ :: [Value] -> [Value] -> [Value]
φ r1 p = extract (phi p [r1])

{-p    = diag' ++ diag'-}
p    = diag' ++ write'
q    = φ p p -- diag'
{-q    = φ (diag' ++ diag') write' ++ diag'-}
q'   = φ q q
q''  = φ q' q'
q''' = φ q'' q''

k    = φ [] q
k'   = φ [] k
k''  = φ [] k'
k''' = φ [] k''

ps = iterate (φ []) q

main = print $ k'' == k'''

-- example  = φ [] $ φ program pgm
-- example2 = φ write' $ compileValue diag
-- example3 = φ [] example2
-- example4 = φ [] example3
-- example5 = φ [] example4
