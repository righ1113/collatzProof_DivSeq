{-
$ cd collatzProof_DivSeq/program7
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
-- 最終的な定理
limitedDivSeq : (n : Nat) -> FirstLimited n
limitedDivSeq n = wfInd {P=FirstLimited} {rel=LT'} step n where
  step : (x : Nat) -> ((y : Nat) -> LT' y x -> FirstLimited y) -> FirstLimited x
  step Z         _  = IsFirstLimited10 -- 6*<0>+3 = 3
  step (S Z)     _  = IsFirstLimited01 -- 6*<1>+3 = 9
  step (S (S x)) rs with (mod3 x)
    -- 6 mod 9
    step (S (S (j + j + j)))         rs | ThreeZero
            = IsFirstLimited09 j $ IsFtoA j $ rs j $ lteToLt' $ lte18t15 j
    -- 3 mod 9
    step (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
      step (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
            = IsFirstLimited11 k $ IsFtoA k $ rs k $ lteToLt' $ lte36t21 k
      step (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
        step no12_18t06 rs | ThreeOne | Odd  | ThreeZero
            = IsFirstLimited12 l $ IsFtoA (l+l) $ rs (l+l) $ lteToLt' $ lte108t39 l
        step no13_18t12 rs | ThreeOne | Odd  | ThreeOne
            = IsFirstLimited13 l $ IsFtoA (S ((l+l)+(l+l))) $ rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l
        step no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
            = let x = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) in
              IsFirstLimited14 l $ IsFtoA x $ rs x $ lteToLt' $ lte108t111 l
    -- 0 mod 9
    step (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
      step (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
        step no06_18t04 rs | ThreeTwo | Even | ThreeZero
            = let x = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) in
              IsFirstLimited06 l $ IsFtoA x $ rs x $ lteToLt' $ lte108t27_2 l
        step no07_18t10 rs | ThreeTwo | Even | ThreeOne
            = let x = (S (S (S (S (l+l+l+l)+(l+l+l+l))))) in
              IsFirstLimited07 l $ IsFtoA x $ rs x $ lteToLt' $ lte108t63_2 l
        step no08_18t16 rs | ThreeTwo | Even | ThreeTwo
            = let x = (S (S (S ((l+l)+(l+l))))) in
              IsFirstLimited08 l $ IsFtoA x $ rs x $ lteToLt' $ lte108t99_2 l
      step (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
        step no02_12t07 rs | ThreeTwo | Odd | Even
            = IsFirstLimited02 l $ IsFtoA l $ rs l $ lteToLt' $ lte72t45_2 l
        step noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
          step no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
            = IsFirstLimited03 m $ IsFtoA (m+m) $ rs (m+m) $ lteToLt' $ lte216t81_2 m
          step no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
            = IsFirstLimited04 m $ IsFtoA (S ((m+m)+(m+m))) $ rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m
          step no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
            = let x = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) in
              IsFirstLimited05 m $ IsFtoA x $ rs x $ lteToLt' $ lte216t225_2 m



