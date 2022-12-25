{-
$ cd collatzProof_DivSeq/program6
$ chcp 65001
$ idris
> :l ProofColDivSeqMain
-}
module ProofColDivSeqMain

import ProofColDivSeqBase as B
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
makeLimitedDivSeq : ((k : Nat) -> SingleLimited k -> (ExtsLimited . B.allDivSeq) k) -> (n : Nat) -> SingleLimited n
makeLimitedDivSeq sToE n = wfInd {P=SingleLimited} {rel=LT'} (step sToE) n where
  step : ((k : Nat) -> SingleLimited k -> (ExtsLimited . B.allDivSeq) k)
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> SingleLimited y)
      -> SingleLimited x
  step sToE Z         _  = IsSingleLimited10 -- 6*<0>+3 = 3
  step sToE (S Z)     _  = IsSingleLimited01 -- 6*<1>+3 = 9
  step sToE (S (S x)) rs with (mod3 x)
    -- 6 mod 9
    step sToE (S (S (j + j + j)))         rs | ThreeZero
            = IsSingleLimited09 j $ sToE j $ rs j $ lteToLt' $ lte18t15 j
    -- 3 mod 9
    step sToE (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
      step sToE (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
            = IsSingleLimited11 k $ sToE k $ rs k $ lteToLt' $ lte36t21 k
      step sToE (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
        step sToE no12_18t06 rs | ThreeOne | Odd  | ThreeZero
            = IsSingleLimited12 l $ sToE (l+l) $ rs (l+l) $ lteToLt' $ lte108t39 l
        step sToE no13_18t12 rs | ThreeOne | Odd  | ThreeOne
            = IsSingleLimited13 l $ sToE (S ((l+l)+(l+l))) $ rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l
        step sToE no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
            = let x = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) in
              IsSingleLimited14 l $ sToE x $ rs x $ lteToLt' $ lte108t111 l
    -- 0 mod 9
    step sToE (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
      step sToE (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
        step sToE no06_18t04 rs | ThreeTwo | Even | ThreeZero
            = let x = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) in
              IsSingleLimited06 l $ sToE x $ rs x $ lteToLt' $ lte108t27_2 l
        step sToE no07_18t10 rs | ThreeTwo | Even | ThreeOne
            = let x = (S (S (S (S (l+l+l+l)+(l+l+l+l))))) in
              IsSingleLimited07 l $ sToE x $ rs x $ lteToLt' $ lte108t63_2 l
        step sToE no08_18t16 rs | ThreeTwo | Even | ThreeTwo
            = let x = (S (S (S ((l+l)+(l+l))))) in
              IsSingleLimited08 l $ sToE x $ rs x $ lteToLt' $ lte108t99_2 l
      step sToE (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
        step sToE no02_12t07 rs | ThreeTwo | Odd | Even
            = IsSingleLimited02 l $ sToE l $ rs l $ lteToLt' $ lte72t45_2 l
        step sToE noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
          step sToE no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
            = IsSingleLimited03 m $ sToE (m+m) $ rs (m+m) $ lteToLt' $ lte216t81_2 m
          step sToE no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
            = IsSingleLimited04 m $ sToE (S ((m+m)+(m+m))) $ rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m
          step sToE no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
            = let x = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) in
              IsSingleLimited05 m $ sToE x $ rs x $ lteToLt' $ lte216t225_2 m

-- 十分条件
singleToExts : (n : Nat) -> SingleLimited n -> (ExtsLimited . B.allDivSeq) n
singleToExts n rs = case rs of
  IsSingleLimited10     => IsExtsLimited10 -- 6*<0>+3 = 3
  IsSingleLimited01     => IsExtsLimited01 -- 6*<1>+3 = 9
  IsSingleLimited09 j p => IsExtsLimited09 j p
  IsSingleLimited11 k p => IsExtsLimited11 k p
  IsSingleLimited12 l p => IsExtsLimited12 l p
  IsSingleLimited13 l p => IsExtsLimited13 l p
  IsSingleLimited14 l p => IsExtsLimited14 l p
  IsSingleLimited06 l p => IsExtsLimited06 l p
  IsSingleLimited07 l p => IsExtsLimited07 l p
  IsSingleLimited08 l p => IsExtsLimited08 l p
  IsSingleLimited02 l p => IsExtsLimited02 l p
  IsSingleLimited03 m p => IsExtsLimited03 m p
  IsSingleLimited04 m p => IsExtsLimited04 m p
  IsSingleLimited05 m p => IsExtsLimited05 m p

-- 最終的な定理
limitedDivSeq : (n : Nat) -> SingleLimited n
limitedDivSeq = makeLimitedDivSeq singleToExts



