{-
cd collatzProof_DivSeq/program3
chcp 65001
idris
-}
module ProofColDivSeqMain

import ProofColDivSeqBase
import ProofColDivSeqPostulate
{-
import Sub01Apply18x3
import Sub02Apply54x12
import Sub03Apply54x30
import Sub04Apply54x48
import Sub05Apply9x6
import Sub06Apply36x9
import Sub07Apply108x27
import Sub08Apply108x63
import Sub09Apply108x99
import Sub10Apply108x18
import Sub11Apply108x54
import Sub12Apply108x90
import Sub13Apply108x36
import Sub14Apply108x72
import Sub15Apply108x108
-}
import Sub09LTE18t15
import Sub11LTE36t21

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
      = (IsFirstLimited09 j . firstToAll j . Ddown) (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step firstToAll (S (S (S (j + j + j)))) rs | ThreeTwo with (parity j)
      step firstToAll (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeTwo | Even
        = (IsFirstLimited11 k . firstToAll k . Ddown) (rs k $ lteToLt' $ lte36t21 k)
      step firstToAll (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeTwo | Odd  = ?rhs4



-- 最終的な定理
limitedDivSeq : (d : CoNat) -> (n : Nat) -> FirstLimited d $ allDivSeq n
-- limitedDivSeq (S d) = \n => makeLimitedDivSeq d n $ \k => makeFtoA d k $ \m => (limitedDivSeq d m)
--                       ↑上記をコンストラクタ化する
limitedDivSeq (S d) = ConstructorLimitedDivSeq (limitedDivSeq d m)



