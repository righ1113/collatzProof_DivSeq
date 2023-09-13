{-
$ cd collatzProof_DivSeq/program8
$ chcp 65001
$ idris
> :l ProofColDivSeqMain
-}
module ProofColDivSeqMain

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import Sub02LTE72t45
import Sub03LTE216t81
import Sub04LTE216t153
import Sub05LTE216t225
import Sub06LTE108t27
import Sub07LTE108t63
import Sub08LTE108t99
import Sub09LTE18t15
import Sub11LTE36t21
import Sub12LTE108t39
import Sub13LTE108t75
import Sub14LTE108t111

%default total


-- 示すのに、整礎帰納法を使っている
wfCollatz : ((z : Nat) -> FirstL z -> Cont (AllL z) (FirstL z))
  -> (n : Nat) -> Cont (FirstL n) (FirstL n)
wfCollatz ftoa n = wfInd {P=(\t=>Cont (FirstL t) (FirstL t))} {rel=LT'} (step ftoa) n where
  step : ((z : Nat) -> FirstL z -> Cont (AllL z) (FirstL z))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> Cont (FirstL y) (FirstL y)) -> Cont (FirstL x) (FirstL x)
  step ftoa Z         _  = MkCont $ \_=>IsFirstL10 -- 6*<0>+3 = 3
  step ftoa (S Z)     _  = MkCont $ \_=>IsFirstL01 -- 6*<1>+3 = 9
  step ftoa (S (S x)) rs with (mod3 x)
    -- 6 mod 9
    step ftoa (S (S (j + j + j)))         rs | ThreeZero
            = MkCont $ \_=>(IsFirstL09 j $ ftoa j $ runCont (rs j $ lteToLt' $ lte18t15 j) id)
    -- 3 mod 9
    step ftoa (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
      step ftoa (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
            = MkCont $ \_=>(IsFirstL11 k $ ftoa k $ runCont (rs k $ lteToLt' $ lte36t21 k) id)
      step ftoa (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
        step ftoa no12_18t06 rs | ThreeOne | Odd  | ThreeZero
            = MkCont $ \_=>(IsFirstL12 l $ ftoa (l+l) $ runCont (rs (l+l) $ lteToLt' $ lte108t39 l) id)
        step ftoa no13_18t12 rs | ThreeOne | Odd  | ThreeOne
            = MkCont $ \_=>(IsFirstL13 l $ ftoa (S ((l+l)+(l+l))) $ runCont (rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l) id)
        step ftoa no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
            = MkCont $ \_=>(IsFirstL14 l $ ftoa xx $ runCont (rs xx $ lteToLt' $ lte108t111 l) id) where
                xx : Nat
                xx = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))
    -- 0 mod 9
     step ftoa (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
      step ftoa (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
        step ftoa no06_18t04 rs | ThreeTwo | Even | ThreeZero
            = MkCont $ \_=>(IsFirstL06 l $ ftoa xx $ runCont (rs xx $ lteToLt' $ lte108t27_2 l) id) where
                xx : Nat
                xx = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))
        step ftoa no07_18t10 rs | ThreeTwo | Even | ThreeOne
            = MkCont $ \_=>(IsFirstL07 l $ ftoa xx $ runCont (rs xx $ lteToLt' $ lte108t63_2 l) id) where
                xx : Nat
                xx = (S (S (S (S (l+l+l+l)+(l+l+l+l)))))
        step ftoa no08_18t16 rs | ThreeTwo | Even | ThreeTwo
            = MkCont $ \_=>(IsFirstL08 l $ ftoa xx $ runCont (rs xx $ lteToLt' $ lte108t99_2 l) id) where
                xx : Nat
                xx = (S (S (S ((l+l)+(l+l)))))
      step ftoa (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
        step ftoa no02_12t07 rs | ThreeTwo | Odd | Even
            = MkCont $ \_=>(IsFirstL02 l $ ftoa l $ runCont (rs l $ lteToLt' $ lte72t45_2 l) id)
        step ftoa noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
          step ftoa no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
            = MkCont $ \_=>(IsFirstL03 m $ ftoa (m+m) $ runCont (rs (m+m) $ lteToLt' $ lte216t81_2 m) id)
          step ftoa no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
            = MkCont $ \_=>(IsFirstL04 m $ ftoa (S ((m+m)+(m+m))) $ runCont (rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m) id)
          step ftoa no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
            = MkCont $ \_=>(IsFirstL05 m $ ftoa xx $ runCont (rs xx $ lteToLt' $ lte216t225_2 m) id) where
                xx: Nat
                xx = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))

-- 最終的な定理
-- 示すのに、パースの法則とcallCC を基にしている
limitedDivSeq : (n : Nat) -> FirstL n
limitedDivSeq n = runCont callCC id where
  callCC = MkCont (\k => runCont ((wfCollatz (\_,a => MkCont (\q => q a))) n) k)



