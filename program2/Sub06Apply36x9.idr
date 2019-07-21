module Sub06Apply36x9

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(12x+3) --E[2,-4]--> 3x
export
apply36x9 : (Not . P) (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l))))))
  -> (m : Nat ** (LTE (S m) (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l)))))), (Not . P) m))
apply36x9 {l} col = (l ** (lte36x9 l, e36x9To3x l col)) where
  lte36x9 : (l:Nat) -> LTE (S l) (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l))))))
  lte36x9 Z = (lteSuccRight . lteSuccRight . LTESucc) LTEZero
  lte36x9 (S l) = let lemma = lte36x9 l in
    rewrite (sym (plusSuccRightSucc l l)) in
    rewrite (sym (plusSuccRightSucc (plus l l) (S (plus l l)))) in
    rewrite (sym (plusSuccRightSucc (plus l l) (plus l l))) in
    rewrite (sym (plusSuccRightSucc (plus (plus l l) (plus l l))  (S (S (S (plus (plus l l) (plus l l))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus l l) (plus l l))  (S (S (plus (plus l l) (plus l l)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus l l) (plus l l))  (S (plus (plus l l) (plus l l))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus l l) (plus l l))  (plus (plus l l) (plus l l)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))  (S (S (S (plus (plus l l) (plus l l))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))  (S (S (plus (plus l l) (plus l l)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))  (S (plus (plus l l) (plus l l))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))  (plus (plus l l) (plus l l)))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) lemma



