{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RecursiveDo      #-}

module U where

import OneHash

-- Assume the input has already been parsed, we can do this awesome thing:
-- 1#       => 1
-- 1##      => 11
-- 1#####   => 111
-- 11#      => 1111
-- 11##     => 11111
-- 11#####  => 111111
-- 111#     => 1111111
-- 111##    => 11111111
-- 111##### => 111111111
-- 1^n###   => #1^n
-- 1^n####  => ##1^n

-- The idea here is that this will take three labels and just jump
-- to those instead of building segments for those bodies.
-- This code will behave the same as the `cases` function when given jumps
-- as arguments and now I don't have to export the Case constructor.
--jumpCases r = \ c1 c2 c3 -> tell [Case r] >> c1 >> c2 >> c3
jumpCases = cases

-- Case statement with fallthrough semantics
doCases :: Reg -> OneHash ()
doCases r1 = mdo
  jumpCases r1 addOne addTwo addThree
  addThree <- label
  add1 r2
  addTwo   <- label
  add1 r2
  addOne   <- label
  add1 r2

-- TODO: We can avoid using all these labels by simply using a cases operation
-- and a noop, since we are always jumping to the instruction right after the
-- cases.
green :: OneHash ()
green = withLabels $ \ start end -> mdo
  jumpCases r3 end opcode1 jumps
  opcode1 <- label
  jumpCases r3 write11 opcode2 end
  opcode2 <- label
  jumpCases r3 write1h opcode3 end
  opcode3 <- label
  jumpCases r3 case1   opcode4 end
  opcode4 <- label
  jumpCases r3 write21 opcode5 end
  opcode5 <- label
  jumpCases r3 write2h opcode6 end
  opcode6 <- label
  jumpCases r3 case2   opcode7 end
  opcode7 <- label
  jumpCases r3 write31 opcode8 end
  opcode8 <- label
  jumpCases r3 write3h opcode9 end
  opcode9 <- label
  jumpCases r3 case3   end     end
  write11 <- label
  add1 r4 >> end
  write1h <- label
  addh r4 >> end
  case1 <- label
  doCases r4 >> end
  write21 <- label
  add1 r5 >> end
  write2h <- label
  addh r5 >> end
  case2 <- label
  doCases r4 >> end
  write31 <- label
  add1 r6 >> end
  write3h <- label
  addh r6 >> end
  case3 <- label
  doCases r4 >> end
  jumps <- label
  cases r3 end (add1 r2 >> jumpAdds) jumpSubs
  jumpAdds <- label
  move r3 r2 >> end
  jumpSubs <- label
  subDestructive r2 r3

