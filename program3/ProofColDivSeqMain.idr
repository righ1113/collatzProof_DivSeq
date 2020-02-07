{-
$ cd collatzProof_DivSeq/program3
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
makeLimitedDivSeq : (n : Nat)
  -> ((z : Nat) -> (FirstLimited $ allDivSeq z -> AllLimited $ allDivSeq z))
    -> FirstLimited $ allDivSeq n
makeLimitedDivSeq n firstToAll = wfInd {P=(\z=>FirstLimited $ allDivSeq z)} {rel=LT'} (step firstToAll) n where
  step : ((z : Nat) -> (FirstLimited $ allDivSeq z -> AllLimited $ allDivSeq z))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> FirstLimited $ allDivSeq y)
      -> FirstLimited $ allDivSeq x
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

-- 最終的な定理
limitedDivSeq : (n : Nat) -> FirstLimited $ allDivSeq n
{-
手での証明
  1.∀n.First$Seq n -> ∀n.All$Seq nと∀n.All$Seq n -> ∀n.First$Seq nより、∀n.First$Seq n <-> ∀n.All$Seq nが言える。
  2.外延的等価性により、∀n.First$Seq n <-> ∀n.All$Seq nからFirst$Seq <-> All$Seq...(1)が言える。
  3.makeLimitedDivSeqを(1)で書き換えて、∀z.(First$Seq z -> First$Seq z) -> ∀n.First$Seq n...(2)が言える。
  4.(2)に\_->idを渡して、最終的な定理∀n.First$Seq nを得る。
-}



