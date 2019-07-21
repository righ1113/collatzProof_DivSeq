module Sub05Apply9x6

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(3x+2) --C[4,-4]--> 3x
export
apply9x6 : (Not . P) (S (S (plus (plus j j) j)))
  -> (m : Nat ** (LTE (S m) (S (S (plus (plus j j) j))), (Not . P) m))
apply9x6 {j} col = (j ** (lte9x6 j, c9x6To3x j col)) where
  lte9x6 : (j:Nat) -> LTE (S j) (S (S (plus (plus j j) j)))
  lte9x6 Z = (lteSuccRight . LTESucc) LTEZero
  lte9x6 (S j) = let lemma = lte9x6 j in
    rewrite (sym (plusSuccRightSucc j j)) in
    rewrite (sym (plusSuccRightSucc (plus j j) j)) in
      (lteSuccRight . lteSuccRight . LTESucc) lemma



