module Sub05Apply9x6

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(3x+2) --C[4,-4]--> 3x
b9x6To3x :
  (j:Nat) -> P (S (S (plus (plus j j) j))) 2 -> P j 2
b9x6To3x j prf =
  let prf2 = lvDown (S (S (plus (plus j j) j))) 2 prf in b9x6To3x' j prf2

export
apply9x6 : P (S (S (plus (plus j j) j))) 2
  -> (m : Nat ** (LTE (S m) (S (S (plus (plus j j) j))), P m 2))
apply9x6 {j} col = let col2 = b9x6To3x j col in (j ** (lte9x6 j, col2)) where
  lte9x6 : (j:Nat) -> LTE (S j) (S (S (plus (plus j j) j)))
  lte9x6 Z = (lteSuccRight . LTESucc) LTEZero
  lte9x6 (S j) = let lemma = lte9x6 j in
    rewrite (sym (plusSuccRightSucc j j)) in
    rewrite (sym (plusSuccRightSucc (plus j j) j)) in
      (lteSuccRight . lteSuccRight . LTESucc) lemma
-- ---------------------------




