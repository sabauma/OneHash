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
jumpCases r = \ c1 c2 c3 -> tell [Case r] >> c1 >> c2 >> c3

doCases :: Reg -> OneHash ()
doCases r1 = mdo jumpCases r1 addOne addTwo addThree
                 addThree <- label
                 add1 R2
                 addTwo   <- label
                 add1 R2
                 addOne   <- label
                 add1 R2

green :: OneHash ()
green = withLabels
          (\ start end -> mdo
              jumpCases R3 end opcode1 jumps
              opcode1 <- label
              jumpCases R3 write11 opcode2 end
              opcode2 <- label
              jumpCases R3 write1h opcode3 end
              opcode3 <- label
              jumpCases R3 case1 opcode4 end
              opcode4 <- label
              jumpCases R3 write21 opcode5 end
              opcode5 <- label
              jumpCases R3 write2h opcode6 end
              opcode6 <- label
              jumpCases R3 case2   opcode7 end
              opcode7 <- label
              jumpCases R3 write31 opcode8 end
              opcode8 <- label
              jumpCases R3 write3h opcode9 end
              opcode9 <- label
              jumpCases R3 case3   end     end
              write11 <- label
              add1 R4 >> end
              write1h <- label
              addh R4 >> end
              case1 <- label
              doCases R4 >> end
              write21 <- label
              add1 R5 >> end
              write2h <- label
              addh R5 >> end
              case2 <- label
              doCases R4 >> end
              write31 <- label
              add1 R6 >> end
              write3h <- label
              addh R6 >> end
              case3 <- label
              doCases R4 >> end
              jumps <- label
              cases R3 end (add1 R2 >> jumpAdds) jumpSubs
              jumpAdds <- label
              move R3 R2 >> end
              jumpSubs <- label
              subDestructive R2 R3)

