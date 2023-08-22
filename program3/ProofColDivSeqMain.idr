{-
$ cd collatzProof_DivSeq/program3
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
makeLimitedDivSeq :
  ((z : Nat) -> ((FirstLimited . B.allDivSeq) z -> (AllLimited . B.allDivSeq) z))
    ->  (n : Nat) -> (FirstLimited . B.allDivSeq) n
makeLimitedDivSeq firstToAll n = wfInd {P=(\z=>(FirstLimited . B.allDivSeq) z)} {rel=LT'} (step firstToAll) n where
  step : ((z : Nat) -> ((FirstLimited . B.allDivSeq) z -> (AllLimited . B.allDivSeq) z))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> (FirstLimited . B.allDivSeq) y)
      -> (FirstLimited . B.allDivSeq) x
  step _          Z     _  = IsFirstLimited10                                                          -- 6*<0>+3 = 3
  step firstToAll (S x) rs with (mod3 x)
    -- 0 mod 9
    step firstToAll (S (j + j + j)) rs | ThreeZero with (parity j)
      step firstToAll (S ((Z+Z) + (Z+Z) + (Z+Z)))             rs | ThreeZero | Even = IsFirstLimited01 -- 6*<1>+3 = 9
      step firstToAll (S (((S k)+(S k)) + ((S k)+(S k)) + ((S k)+(S k))))             rs | ThreeZero | Even with (parity k)
        step firstToAll (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))                         rs | ThreeZero | Even | Even
          = (IsFirstLimited02 l . firstToAll l) (rs l $ lteToLt' $ lte72t45 l)
        step firstToAll (S (((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))))) rs | ThreeZero | Even | Odd  with (mod3 l)
          step firstToAll (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))                                                                                                 rs | ThreeZero | Even | Odd | ThreeZero
            = (IsFirstLimited03 m . firstToAll (m+m)) (rs (m+m) $ lteToLt' $ lte216t81 m)
          step firstToAll (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))                                                 rs | ThreeZero | Even | Odd | ThreeOne
            = (IsFirstLimited04 m . firstToAll (S ((m+m)+(m+m)))) (rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153 m)
          step firstToAll (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))))) rs | ThreeZero | Even | Odd | ThreeTwo
            = (IsFirstLimited05 m . firstToAll (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))) (rs (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) $ lteToLt' $ lte216t225 m)
      step firstToAll (S ((S (k+k)) + (S (k+k)) + (S (k+k)))) rs | ThreeZero | Odd  with (mod3 k)
        step firstToAll (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))                                                 rs | ThreeZero | Odd | ThreeZero
          = (IsFirstLimited06 l . firstToAll (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))) (rs (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) $ lteToLt' $ lte108t27 l)
        step firstToAll (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))                         rs | ThreeZero | Odd | ThreeOne
          = (IsFirstLimited07 l . firstToAll (S (S (S (S (l+l+l+l)+(l+l+l+l)))))) (rs (S (S (S (S (l+l+l+l)+(l+l+l+l))))) $ lteToLt' $ lte108t63 l)
        step firstToAll (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))) rs | ThreeZero | Odd | ThreeTwo
          = (IsFirstLimited08 l . firstToAll (S (S (S ((l+l)+(l+l)))))) (rs (S (S (S ((l+l)+(l+l))))) $ lteToLt' $ lte108t99 l)
    -- 6 mod 9
    step firstToAll (S (S (j + j + j)))     rs | ThreeOne
      = (IsFirstLimited09 j . firstToAll j) (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step firstToAll (S (S (S (j + j + j)))) rs | ThreeTwo with (parity j)
      step firstToAll (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeTwo | Even
        = (IsFirstLimited11 k . firstToAll k) (rs k $ lteToLt' $ lte36t21 k)
      step firstToAll (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeTwo | Odd  with (mod3 k)
        step firstToAll (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))                                                 rs | ThreeTwo | Odd  | ThreeZero
          = (IsFirstLimited12 l . firstToAll (l+l)) (rs (l+l) $ lteToLt' $ lte108t39 l)
        step firstToAll (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))                         rs | ThreeTwo | Odd  | ThreeOne
          = (IsFirstLimited13 l . firstToAll (S ((l+l)+(l+l)))) (rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l)
        step firstToAll (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) rs | ThreeTwo | Odd  | ThreeTwo
          = (IsFirstLimited14 l . firstToAll (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))) (rs (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) $ lteToLt' $ lte108t111 l)

-- 十分条件
firstToAll :
  (z : Nat) -> ((FirstLimited . B.allDivSeq) z -> (AllLimited . B.allDivSeq) z)
firstToAll z first =
  let
    suff2_1 = IsFirstLimitedSuff2_1 z first
    suff2_2 = IsFirstLimitedSuff2_2 z first
    suff2_3 = IsFirstLimitedSuff2_3 z first
    suff2_4 = IsFirstLimitedSuff2_4 z first
    suff2_5 = IsFirstLimitedSuff2_5 z first
    suff2_6 = IsFirstLimitedSuff2_6 z first
    all2    = IsAllLimited02 z suff2_1 suff2_2 suff2_3 suff2_4 suff2_5 suff2_6
    suff3_1 = IsFirstLimitedSuff3_1 z first
    suff3_2 = IsFirstLimitedSuff3_2 z first
    suff3_3 = IsFirstLimitedSuff3_3 z first
    suff3_4 = IsFirstLimitedSuff3_4 z first
    suff3_5 = IsFirstLimitedSuff3_5 z first
    suff3_6 = IsFirstLimitedSuff3_6 z first
    all3    = IsAllLimited03 z suff3_1 suff3_2 suff3_3 suff3_4 suff3_5 suff3_6
    suff4_1 = IsFirstLimitedSuff4_1 z first
    suff4_2 = IsFirstLimitedSuff4_2 z first
    suff4_3 = IsFirstLimitedSuff4_3 z first
    suff4_4 = IsFirstLimitedSuff4_4 z first
    suff4_5 = IsFirstLimitedSuff4_5 z first
    all4    = IsAllLimited04 z suff4_1 suff4_2 suff4_3 suff4_4 suff4_5
    suff5_1 = IsFirstLimitedSuff5_1 z first
    suff5_2 = IsFirstLimitedSuff5_2 z first
    suff5_3 = IsFirstLimitedSuff5_3 z first
    suff5_4 = IsFirstLimitedSuff5_4 z first
    suff5_5 = IsFirstLimitedSuff5_5 z first
    suff5_6 = IsFirstLimitedSuff5_6 z first
    all5    = IsAllLimited05 z suff5_1 suff5_2 suff5_3 suff5_4 suff5_5 suff5_6
    suff6_1 = IsFirstLimitedSuff6_1 z first
    suff6_2 = IsFirstLimitedSuff6_2 z first
    suff6_3 = IsFirstLimitedSuff6_3 z first
    suff6_4 = IsFirstLimitedSuff6_4 z first
    suff6_5 = IsFirstLimitedSuff6_5 z first
    suff6_6 = IsFirstLimitedSuff6_6 z first
    all6    = IsAllLimited06 z suff6_1 suff6_2 suff6_3 suff6_4 suff6_5 suff6_6
    suff7_1 = IsFirstLimitedSuff7_1 z first
    suff7_2 = IsFirstLimitedSuff7_2 z first
    suff7_3 = IsFirstLimitedSuff7_3 z first
    suff7_4 = IsFirstLimitedSuff7_4 z first
    suff7_5 = IsFirstLimitedSuff7_5 z first
    suff7_6 = IsFirstLimitedSuff7_6 z first
    suff7_7 = IsFirstLimitedSuff7_7 z first
    all7    = IsAllLimited07 z suff7_1 suff7_2 suff7_3 suff7_4 suff7_5 suff7_6 suff7_7
    suff8_1 = IsFirstLimitedSuff8_1 z first
    suff8_2 = IsFirstLimitedSuff8_2 z first
    suff8_3 = IsFirstLimitedSuff8_3 z first
    suff8_4 = IsFirstLimitedSuff8_4 z first
    suff8_5 = IsFirstLimitedSuff8_5 z first
    suff8_6 = IsFirstLimitedSuff8_6 z first
    all8    = IsAllLimited08 z suff8_1 suff8_2 suff8_3 suff8_4 suff8_5 suff8_6
  in IsAllLimited01 z IsAllLimited00 all2 all3 all4 all5 all6 all7 all8

-- 最終的な定理
limitedDivSeq : (n : Nat) -> (FirstLimited . B.allDivSeq) n
limitedDivSeq = makeLimitedDivSeq firstToAll



