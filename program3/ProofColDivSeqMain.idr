{-
> cd collatzProof_DivSeq/program3
> chcp 65001
> idris
> :l ProofColDivSeqMain
-}
module ProofColDivSeqMain

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import Sub09LTE18t15
import Sub11LTE36t21
import Sub12LTE108t39
import Sub13LTE108t75

%default total


makeFtoA : (d, n : Nat)
  -> ((z : Nat) -> FirstLimited $ allDivSeq d z)
    -> (FirstLimited $ allDivSeq d n -> AllLimited $ allDivSeq d n)
{--}
makeFtoA _ n prf _ = ForallFtoForallA prf $ n
{--}

-- 示すのに、整礎帰納法を使っている
makeLimitedDivSeq : (d, n : Nat)
  -> ((z : Nat) -> (FirstLimited $ allDivSeq d z -> AllLimited $ allDivSeq d z))
    -> FirstLimited $ allDivSeq d n
{--}
makeLimitedDivSeq d n firstToAll = wfInd {P=(\z=>FirstLimited $ allDivSeq d z)} {rel=LT'} (step d firstToAll) n where
  step : (d : Nat) -> ((z : Nat) -> (FirstLimited $ allDivSeq d z -> AllLimited $ allDivSeq d z))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> FirstLimited $ allDivSeq d y)
      -> FirstLimited $ allDivSeq d x
  step Z     _          _     _  = IsFirstLimitedD0                                     -- 1x+1 problem
  step (S _) _          Z     _  = IsFirstLimited10                                     -- 6*<0>+3 = 3
  step (S _) firstToAll (S x) rs with (mod3 x)
    -- 0 mod 9
    step (S _) firstToAll (S (Z     + Z     + Z))     rs | ThreeZero = IsFirstLimited01 -- 6*<1>+3 = 9
    step (S _) firstToAll (S ((S j) + (S j) + (S j))) rs | ThreeZero = ?rhs2
    -- 6 mod 9
    step (S _) firstToAll (S (S (j + j + j)))     rs | ThreeOne
      = (IsFirstLimited09 j . firstToAll j) (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step (S _) firstToAll (S (S (S (j + j + j)))) rs | ThreeTwo with (parity j)
      step (S _) firstToAll (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeTwo | Even
        = (IsFirstLimited11 k . firstToAll k) (rs k $ lteToLt' $ lte36t21 k)
      step (S _) firstToAll (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeTwo | Odd  with (mod3 k)
        step (S _) firstToAll (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))                                                 rs | ThreeTwo | Odd  | ThreeZero
          = (IsFirstLimited12 l . firstToAll (l+l)) (rs (l+l) $ lteToLt' $ lte108t39 l)
        step (S _) firstToAll (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))                         rs | ThreeTwo | Odd  | ThreeOne
          = (IsFirstLimited13 l . firstToAll (S ((l+l)+(l+l)))) (rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l)
        step (S _) firstToAll (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) rs | ThreeTwo | Odd  | ThreeTwo  = ?rhs6
{--}

mutual
  fToA : (d, n : Nat) -> (FirstLimited $ allDivSeq (S d) n -> AllLimited $ allDivSeq (S d) n)
  -- fToA d n = makeFtoA d n $ limitedDivSeq d

  -- 最終的な定理
  limitedDivSeq : (d, n : Nat) -> FirstLimited $ allDivSeq (S d) n
  -- limitedDivSeq Z     _ = ?rhs1
  -- limitedDivSeq (S d) n = makeLimitedDivSeq d n $ fToA d


