{-
$ cd collatzProof_DivSeq/program5
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


-- 相互再帰
mutual
  -- 示すのに、整礎帰納法を使っている
  makeLimitedDivSeq : (q : Stream Unit) -> (n : Nat) -> Limited Single q (B.allDivSeq n) n
  makeLimitedDivSeq q n = wfInd {P=(\k=>(Limited Single q (B.allDivSeq k) k))} {rel=LT'} (step q) n where
    step : (q : Stream Unit)
      -> (x : Nat) -> ((y : Nat) -> LT' y x -> Limited Single q (B.allDivSeq y) y)
        -> Limited Single q (B.allDivSeq x) x
    step (()::qs) Z         _  = IsSingleLimited10 qs -- 6*<0>+3 = 3
    step (()::qs) (S Z)     _  = IsSingleLimited01 qs -- 6*<1>+3 = 9
    step (()::qs) (S (S x)) rs with (mod3 x)
      -- 6 mod 9
      step (()::qs) (S (S (j + j + j)))         rs | ThreeZero
              = IsSingleLimited09 qs j $ singleToExts qs j $ rs j $ lteToLt' $ lte18t15 j
      -- 3 mod 9
      step (()::qs) (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
        step (()::qs) (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
              = IsSingleLimited11 qs k $ singleToExts qs k $ rs k $ lteToLt' $ lte36t21 k
        step (()::qs) (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
          step (()::qs) no12_18t06 rs | ThreeOne | Odd  | ThreeZero
              = IsSingleLimited12 qs l $ singleToExts qs (l+l) $ rs (l+l) $ lteToLt' $ lte108t39 l
          step (()::qs) no13_18t12 rs | ThreeOne | Odd  | ThreeOne
              = IsSingleLimited13 qs l $ singleToExts qs (S ((l+l)+(l+l))) $ rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l
          step (()::qs) no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
              = let x = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) in
                IsSingleLimited14 qs l $ singleToExts qs x $ rs x $ lteToLt' $ lte108t111 l
      -- 0 mod 9
      step (()::qs) (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
        step (()::qs) (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
          step (()::qs) no06_18t04 rs | ThreeTwo | Even | ThreeZero
              = let x = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) in
                IsSingleLimited06 qs l $ singleToExts qs x $ rs x $ lteToLt' $ lte108t27_2 l
          step (()::qs) no07_18t10 rs | ThreeTwo | Even | ThreeOne
              = let x = (S (S (S (S (l+l+l+l)+(l+l+l+l))))) in
                IsSingleLimited07 qs l $ singleToExts qs x $ rs x $ lteToLt' $ lte108t63_2 l
          step (()::qs) no08_18t16 rs | ThreeTwo | Even | ThreeTwo
              = let x = (S (S (S ((l+l)+(l+l))))) in
                IsSingleLimited08 qs l $ singleToExts qs x $ rs x $ lteToLt' $ lte108t99_2 l
        step (()::qs) (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
          step (()::qs) no02_12t07 rs | ThreeTwo | Odd | Even
              = IsSingleLimited02 qs l $ singleToExts qs l $ rs l $ lteToLt' $ lte72t45_2 l
          step (()::qs) noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
            step (()::qs) no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
              = IsSingleLimited03 qs m $ singleToExts qs (m+m) $ rs (m+m) $ lteToLt' $ lte216t81_2 m
            step (()::qs) no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
              = IsSingleLimited04 qs m $ singleToExts qs (S ((m+m)+(m+m))) $ rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m
            step (()::qs) no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
              = let x = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) in
                IsSingleLimited05 qs m $ singleToExts qs x $ rs x $ lteToLt' $ lte216t225_2 m

  -- 元十分条件
  singleToExts : (q : Stream Unit) -> (n : Nat) -> Limited Single (()::q) (B.allDivSeq n) n -> Limited Exts q (B.allDivSeq n) n
  singleToExts q n p = IsStoSE q (makeLimitedDivSeq q) n p


namespace S
  u : Stream Unit
  u = repeat ()

-- 最終的な定理
limitedDivSeq : (n : Nat) -> Limited Single S.u (B.allDivSeq n) n
limitedDivSeq = makeLimitedDivSeq S.u



