{-
cd collatzProof_DivSeq/program3
chcp 65001
idris
-}
module ProofColDivSeqMain

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import Sub09LTE18t15
import Sub11LTE36t21
import Sub12LTE108t39
import Sub13LTE108t75

%default total


makeFtoA :
  ((z : Nat) -> FirstLimited $ allDivSeq z)
    -> (n : Nat) -> (FirstLimited $ allDivSeq n -> AllLimited $ allDivSeq n)
makeFtoA prf n _ = ForallFtoForallA prf $ n

-- 示すのに、整礎帰納法を使っている
makeLimitedDivSeq : (n : Nat)
  -> ((z : Nat) -> (FirstLimited $ allDivSeq z -> AllLimited $ allDivSeq z))
    -> FirstLimited $ allDivSeq n
makeLimitedDivSeq n firstToAll = wfInd {P=(\z=>FirstLimited $ allDivSeq z)} {rel=LT'} (step firstToAll) n where
  step : ((z : Nat) -> (FirstLimited $ allDivSeq z -> AllLimited $ allDivSeq z))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> FirstLimited $ allDivSeq y)
      -> FirstLimited $ allDivSeq x
  step _          Z     _  = IsFirstLimited10                                     -- 6*<0>+3 = 3
  step firstToAll (S x) rs with (mod3 x)
    -- 0 mod 9
    step firstToAll (S (Z     + Z     + Z))     rs | ThreeZero = IsFirstLimited01 -- 6*<1>+3 = 9
    step firstToAll (S ((S j) + (S j) + (S j))) rs | ThreeZero = ?rhs2
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
        step firstToAll (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) rs | ThreeTwo | Odd  | ThreeTwo  = ?rhs6


mutual
  fToA : (d : Nat) -> (n : Nat)
    -> (FirstLimited $ allDivSeq n -> AllLimited $ allDivSeq n)

  -- 最終的な定理
  limitedDivSeq : (d : Nat) -> (n : Nat) -> FirstLimited $ allDivSeq n



