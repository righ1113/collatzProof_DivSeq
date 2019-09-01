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


record Cont (r : Type) (a : Type) where
  constructor CT
  runCont : (a -> r) -> r

implementation Functor (Cont r) where
implementation Applicative (Cont r) where
implementation Monad (Cont r) where

callCC : {a, b, r : Nat -> Type}
  -> (n : Nat) -> (((z1, z2 : Nat) -> a n -> Cont (r n) (b n)) -> ((k : Nat) -> Cont (r k) (a k))) -> Cont (r n) (a n)
callCC n f = CT $ \outerCont =>
  runCont ((f $ \z1, z2, aa => CT $ \_innerCont => outerCont aa) n) outerCont

unifiCallCC :
  ((z1, z2 : Nat) -> (FirstLimited (allDivSeq z1) -> Cont (FirstLimited (allDivSeq z2)) (AllLimited (allDivSeq z1))))
    -> ((n : Nat) -> Cont (FirstLimited (allDivSeq n)) (FirstLimited (allDivSeq n)))
unifiCallCC firstToAll n = wfInd {rel=LT'} (step firstToAll) n where
  step : ((z1, z2 : Nat) -> (FirstLimited (allDivSeq z1) -> Cont (FirstLimited (allDivSeq z2)) (AllLimited (allDivSeq z1))))
    -> (x : Nat) -> ((y : Nat) -> LT' y x -> Cont (FirstLimited (allDivSeq y)) (FirstLimited (allDivSeq y)))
      -> Cont (FirstLimited (allDivSeq x)) (FirstLimited (allDivSeq x))

--lastFunc :
--  (\z1 => (\z2 => FirstLimited (allDivSeq z1)) z2) z1 -> FirstLimited (allDivSeq z1)

-- 最終的な定理
--limitedDivSeq : (n : Nat) -> FirstLimited (allDivSeq n)
--limitedDivSeq n = runCont (callCC n unifiCallCC) $ ?rhs10


-- 示すのに、整礎帰納法を使っている
unifiPeirce :
  ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
    -> ((n : Nat) -> FirstLimited (allDivSeq n))
unifiPeirce firstToAll n = wfInd {P=(\z=>FirstLimited (allDivSeq z))} {rel=LT'} (step firstToAll) n where
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

allToVoid : (x : Nat) -> Not $ AllLimited (allDivSeq (S x))
allToVoid x prf impossible



