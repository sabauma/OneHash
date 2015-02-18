{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses
             RecursiveDo, ScopedTypeVariables        #-}

module U where

import           Prelude hiding (init)
import           Control.Monad
import           OneHash
import           Phi           hiding (decode)
import           Text.Printf

step :: OneHash ()
step = withLabels $ \ start end -> mdo
  comment "begin step function"
  clear r5
  cases r3 end end  noop
  cases r3 end (add1 r5 >> move r3 r5 >> write1  end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> writeh  end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> jumpadd end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> jumpsub end) noop
  cases r3 end (add1 r5 >> move r3 r5 >> caseh   end) noop
  comment "end step function"
    where
      write1  end = lookupReg >> add1 r6 >> updateReg >> add1 r2 >> end
      writeh  end = lookupReg >> addh r6 >> updateReg >> add1 r2 >> end
      jumpadd end = move r5 r2 >> end
      jumpsub end = subDestructive r2 r5 >> end
      caseh   end = lookupReg >> cases r6 (add1 r2)
                                   (add1 r2 >> add1 r2)
                                   (add1 r2 >> add1 r2 >> add1 r2)
                              >> updateReg >> end

toEncoding :: Reg -> Reg -> OneHash ()
toEncoding r r' = withLabels $ \ start end -> mdo
  comment $ printf "encode program in %s into %s" (show r) (show r')
  cases r (addh r' >> addh r' >> end)
          (add1 r' >> add1 r' >> oneloop)
          (add1 r' >> addh r' >> hashloop)
  oneloop <- label
  cases r (addh r' >> addh r' >> end)
          (add1 r' >> add1 r' >> oneloop)
          (add1 r' >> addh r' >> hashloop)
  hashloop <- label
  cases r (addh r' >> addh r' >> end)
          (addh r' >> addh r' >> add1 r' >> add1 r' >> oneloop)
          (add1 r' >> addh r' >> hashloop)
  comment "end encode function"

toDataEncoding :: Reg -> Reg -> OneHash()
toDataEncoding rin rout = do
  comment $ printf "encode data in %s into %s" (show rin) (show rout)
  loop' rin (add1 rout >> add1 rout) (add1 rout >> addh rout)
  addh rout
  addh rout
  comment "end data encoding"

decode :: Reg -> Reg -> OneHash ()
decode rin rout = do
  start <- label
  cases rin noop
    (cases rin noop (add1 rout >> start) (addh rout >> start))
    (cases rin noop noop noop)

