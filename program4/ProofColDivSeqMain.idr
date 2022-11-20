{-
$ cd collatzProof_DivSeq/program4
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
  makeLimitedDivSeq : (q, n : Nat) -> (FirstLimited . B.allDivSeqFA q) n
  makeLimitedDivSeq q n = wfInd {P=(FirstLimited . B.allDivSeqFA q)} {rel=LT'} (step q) n where
    step : (q : Nat)
      -> (x : Nat) -> ((y : Nat) -> LT' y x -> (FirstLimited . B.allDivSeqFA q) y)
        -> (FirstLimited . B.allDivSeqFA q) x
    -- q=0 のときは、 -> (FirstLimited . B.allDivSeqFA q) x が FirstLimited (allDivSeq Z) に潰れる
    step q Z     _  = IsFirstLimited10 q                                                          -- 6*<0>+3 = 3
    step q (S x) rs with (mod3 x)
      -- 0 mod 9
      step q (S (j + j + j)) rs | ThreeZero with (parity j)
        step q (S ((Z+Z) + (Z+Z) + (Z+Z)))             rs | ThreeZero | Even = IsFirstLimited01 q -- 6*<1>+3 = 9
        step q (S (((S k)+(S k)) + ((S k)+(S k)) + ((S k)+(S k))))             rs | ThreeZero | Even with (parity k)
          step q (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))                         rs | ThreeZero | Even | Even
            = (IsFirstLimited02 q l . firstToAll q l) (rs l $ lteToLt' $ lte72t45 l)
          step q (S (((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))))) rs | ThreeZero | Even | Odd  with (mod3 l)
            step q (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))                                                                                                 rs | ThreeZero | Even | Odd | ThreeZero
              = (IsFirstLimited03 q m . firstToAll q (m+m)) (rs (m+m) $ lteToLt' $ lte216t81 m)
            step q (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))                                                 rs | ThreeZero | Even | Odd | ThreeOne
              = (IsFirstLimited04 q m . firstToAll q (S ((m+m)+(m+m)))) (rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153 m)
            step q (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))))) rs | ThreeZero | Even | Odd | ThreeTwo
              = (IsFirstLimited05 q m . firstToAll q (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))) (rs (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) $ lteToLt' $ lte216t225 m)
        step q (S ((S (k+k)) + (S (k+k)) + (S (k+k)))) rs | ThreeZero | Odd  with (mod3 k)
          step q (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))                                                 rs | ThreeZero | Odd | ThreeZero
            = (IsFirstLimited06 q l . firstToAll q (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))) (rs (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) $ lteToLt' $ lte108t27 l)
          step q (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))                         rs | ThreeZero | Odd | ThreeOne
            = (IsFirstLimited07 q l . firstToAll q (S (S (S (S (l+l+l+l)+(l+l+l+l)))))) (rs (S (S (S (S (l+l+l+l)+(l+l+l+l))))) $ lteToLt' $ lte108t63 l)
          step q (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))) rs | ThreeZero | Odd | ThreeTwo
            = (IsFirstLimited08 q l . firstToAll q (S (S (S ((l+l)+(l+l)))))) (rs (S (S (S ((l+l)+(l+l))))) $ lteToLt' $ lte108t99 l)
      -- 6 mod 9
      step q (S (S (j + j + j)))     rs | ThreeOne
        = (IsFirstLimited09 q j . firstToAll q j) (rs j $ lteToLt' $ lte18t15 j)
      -- 3 mod 9
      step q (S (S (S (j + j + j)))) rs | ThreeTwo with (parity j)
        step q (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeTwo | Even
          = (IsFirstLimited11 q k . firstToAll q k) (rs k $ lteToLt' $ lte36t21 k)
        step q (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeTwo | Odd  with (mod3 k)
          step q (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))                                                 rs | ThreeTwo | Odd  | ThreeZero
            = (IsFirstLimited12 q l . firstToAll q (l+l)) (rs (l+l) $ lteToLt' $ lte108t39 l)
          step q (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))                         rs | ThreeTwo | Odd  | ThreeOne
            = (IsFirstLimited13 q l . firstToAll q (S ((l+l)+(l+l)))) (rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l)
          step q (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) rs | ThreeTwo | Odd  | ThreeTwo
            = (IsFirstLimited14 q l . firstToAll q (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))) (rs (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) $ lteToLt' $ lte108t111 l)

  -- 元十分条件
  firstToAll : (q, z : Nat) -> (FirstLimited . B.allDivSeqFA q) z -> (AllLimited . B.allDivSeqFA q) z
  firstToAll Z     z _ = IsAllLimited00 z
  firstToAll (S q) z _ = IsFtoA (makeLimitedDivSeq q) (S q) z


-- 最終的な定理
limitedDivSeq : (n : Nat) -> (FirstLimited . B.allDivSeqFA 1) n
limitedDivSeq = makeLimitedDivSeq 1



