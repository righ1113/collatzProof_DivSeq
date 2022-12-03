module Sub09LTE18t15

import ProofColDivSeqPostulate

%default total


-- 6(3t+2)+3 --C[4,-4]--> 6t+3
export
lte18t15 : (j : Nat) -> LTE (S j) (S (S (plus (plus j j) j)))
lte18t15 Z     = (lteSuccRight . LTESucc) LTEZero
lte18t15 (S j) =
  let lemma = lte18t15 j in
  rewrite (sym (plusSuccRightSucc j j)) in
  rewrite (sym (plusSuccRightSucc (plus j j) j)) in
    (lteSuccRight . lteSuccRight . LTESucc) lemma



