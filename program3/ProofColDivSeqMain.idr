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

%default total


makeFtoA : (d : CoNat) -> (n : Nat)
  -> ((z : Nat) -> FirstLimited d $ allDivSeq z)
    -> (FirstLimited d $ allDivSeq n -> AllLimited d $ allDivSeq n)
makeFtoA d n prf _ = ForallFtoForallA prf $ n

-- 示すのに、整礎帰納法を使っている
makeLimitedDivSeq : (d : CoNat) -> (n : Nat)
  -> ((z : Nat) -> (FirstLimited d $ allDivSeq z -> AllLimited d $ allDivSeq z))
    -> FirstLimited (S d) $ allDivSeq n
makeLimitedDivSeq d n firstToAll = wfInd {P=(\z=>FirstLimited (S d) $ allDivSeq z)} {rel=LT'} (step firstToAll) n where
  step : ((z : Nat) -> (FirstLimited d $ allDivSeq z -> AllLimited d $ allDivSeq z))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> FirstLimited (S d) $ allDivSeq y)
      -> FirstLimited (S d) $ allDivSeq x
  step _          Z     _  = IsFirstLimited10                                     -- 6*<0>+3 = 3
  step firstToAll (S x) rs with (mod3 x)
    -- 0 mod 9
    step firstToAll (S (Z     + Z     + Z))     rs | ThreeZero = IsFirstLimited01 -- 6*<1>+3 = 9
    step firstToAll (S ((S j) + (S j) + (S j))) rs | ThreeZero = ?rhs2
    -- 6 mod 9
    step firstToAll (S (S (j + j + j)))     rs | ThreeOne
      = (IsFirstLimited09 j . firstToAll j . Ddown j) (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step firstToAll (S (S (S (j + j + j)))) rs | ThreeTwo with (parity j)
      step firstToAll (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeTwo | Even
        = (IsFirstLimited11 k . firstToAll k . Ddown k) (rs k $ lteToLt' $ lte36t21 k)
      step firstToAll (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeTwo | Odd  with (mod3 k)
        step firstToAll (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))                                                 rs | ThreeTwo | Odd  | ThreeZero
          = (IsFirstLimited12 l . firstToAll (l+l) . Ddown (l+l)) (rs (l+l) $ lteToLt' $ lte108t39 l)
        step firstToAll (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))                         rs | ThreeTwo | Odd  | ThreeOne  = ?rhs5
        step firstToAll (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) rs | ThreeTwo | Odd  | ThreeTwo  = ?rhs6

-- 下で使うコンストラクタの証明
proofConstructorLimited  : (d : CoNat) ->
  ((z : Nat) -> FirstLimited d $ allDivSeq z)
    -> (n : Nat) -> FirstLimited (S d) $ allDivSeq n
proofConstructorLimited d = \f, n => makeLimitedDivSeq d n $ \k => makeFtoA d k f



-- 最終的な定理
limitedDivSeq : (d : CoNat) -> (n : Nat) -> FirstLimited d $ allDivSeq n
-- limitedDivSeq (S d) = \n => makeLimitedDivSeq d n $ \k => makeFtoA d k $ \m => (limitedDivSeq d m)
--                               ↑これらの関数をコンストラクタ化する↑
limitedDivSeq (S d) = ConstructorLimited d $ \m => ConstructorId (limitedDivSeq d m)



