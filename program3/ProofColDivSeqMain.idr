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

%default total


-- パースの法則の十分条件
unifiPeirce : (n : Nat)
  -> ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
    -> FirstLimited (allDivSeq n)
unifiPeirce n firstToAll = wfInd {rel=LT'} (step firstToAll) n where
  step : ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> FirstLimited (allDivSeq y))
      -> FirstLimited (allDivSeq x)
  step _          Z     _  = IsFirstLimited00
  step firstToAll (S x) rs with (mod3 x)
    -- 0 mod 9
    step firstToAll (S (j + j + j))         rs | ThreeZero = ?rhs1
    -- 6 mod 9
    step firstToAll (S (S (j + j + j)))     rs | ThreeOne  = (IsFirstLimited09 j . firstToAll j) (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step firstToAll (S (S (S (j + j + j)))) rs | ThreeTwo  = ?rhs3

lemPeirce : (n : Nat)
  -> Either ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
            (Not ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z))))
    -> FirstLimited (allDivSeq n)
lemPeirce n (Left  fToA)    = unifiPeirce n fToA
lemPeirce n (Right fToAnot) = peirce n fToAnot unifiPeirce


-- 最終的な定理
limitedDivSeq : (n : Nat) -> FirstLimited (allDivSeq n)
limitedDivSeq n = lemPeirce n lem2



