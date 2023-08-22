{-
$ cd collatzProof_DivSeq/program7
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
-- 最終的な定理
LimitedDivSeq : (n : Nat) -> (FirstLimited . B.allDivSeq) n
LimitedDivSeq n = wfInd {P=(\z=>(FirstLimited . B.allDivSeq) z)} {rel=LT'} (step) n where
  step : (x : Nat) -> ((y : Nat) -> LT' y x -> (FirstLimited . B.allDivSeq) y) -> (FirstLimited . B.allDivSeq) x
  step           Z     _  = IsFirstLimited10                                                          -- 6*<0>+3 = 3
  step (S x) rs with (mod3 x)
    -- 0 mod 9
    step (S (j + j + j)) rs | ThreeZero with (parity j)
      step (S ((Z+Z) + (Z+Z) + (Z+Z)))             rs | ThreeZero | Even = IsFirstLimited01 -- 6*<1>+3 = 9
      step (S (((S k)+(S k)) + ((S k)+(S k)) + ((S k)+(S k))))             rs | ThreeZero | Even with (parity k)
        step (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))                         rs | ThreeZero | Even | Even
          = (IsFirstLimited02 l . IsFtoA l) (rs l $ lteToLt' $ lte72t45 l)
        step (S (((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))))) rs | ThreeZero | Even | Odd  with (mod3 l)
          step (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))                                                                                                 rs | ThreeZero | Even | Odd | ThreeZero
            = (IsFirstLimited03 m . IsFtoA (m+m)) (rs (m+m) $ lteToLt' $ lte216t81 m)
          step (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))                                                 rs | ThreeZero | Even | Odd | ThreeOne
            = (IsFirstLimited04 m . IsFtoA (S ((m+m)+(m+m)))) (rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153 m)
          step (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))))) rs | ThreeZero | Even | Odd | ThreeTwo
            = (IsFirstLimited05 m . IsFtoA (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))) (rs (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) $ lteToLt' $ lte216t225 m)
      step (S ((S (k+k)) + (S (k+k)) + (S (k+k)))) rs | ThreeZero | Odd  with (mod3 k)
        step (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))                                                 rs | ThreeZero | Odd | ThreeZero
          = (IsFirstLimited06 l . IsFtoA (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))) (rs (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) $ lteToLt' $ lte108t27 l)
        step (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))                         rs | ThreeZero | Odd | ThreeOne
          = (IsFirstLimited07 l . IsFtoA (S (S (S (S (l+l+l+l)+(l+l+l+l)))))) (rs (S (S (S (S (l+l+l+l)+(l+l+l+l))))) $ lteToLt' $ lte108t63 l)
        step (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))) rs | ThreeZero | Odd | ThreeTwo
          = (IsFirstLimited08 l . IsFtoA (S (S (S ((l+l)+(l+l)))))) (rs (S (S (S ((l+l)+(l+l))))) $ lteToLt' $ lte108t99 l)
    -- 6 mod 9
    step (S (S (j + j + j)))     rs | ThreeOne
      = (IsFirstLimited09 j . IsFtoA j) (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step (S (S (S (j + j + j)))) rs | ThreeTwo with (parity j)
      step (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeTwo | Even
        = (IsFirstLimited11 k . IsFtoA k) (rs k $ lteToLt' $ lte36t21 k)
      step (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeTwo | Odd  with (mod3 k)
        step (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))                                                 rs | ThreeTwo | Odd  | ThreeZero
          = (IsFirstLimited12 l . IsFtoA (l+l)) (rs (l+l) $ lteToLt' $ lte108t39 l)
        step (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))                         rs | ThreeTwo | Odd  | ThreeOne
          = (IsFirstLimited13 l . IsFtoA (S ((l+l)+(l+l)))) (rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l)
        step (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) rs | ThreeTwo | Odd  | ThreeTwo
          = (IsFirstLimited14 l . IsFtoA (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))) (rs (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) $ lteToLt' $ lte108t111 l)



