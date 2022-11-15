module Sub02LTE72t45

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(12t+7)+3 --E[2,-4]--> 6t+3
export
lte72t45 : (l : Nat) -> LTE (S l)
  (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))
lte72t45 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) LTEZero
lte72t45 (S l) =
  let lemma = lte72t45 l in
  rewrite (sym (plusSuccRightSucc l l)) in

  rewrite (sym (plusSuccRightSucc (plus l l) (S (S (plus l l))))) in
  rewrite (sym (plusSuccRightSucc (plus l l)    (S (plus l l)))) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) (S (plus l l))) 
                                  (S (S (S (S (plus (plus l l) (S (plus l l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) (S (plus l l))) 
                                     (S (S (S (plus (plus l l) (S (plus l l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) (S (plus l l))) 
                                        (S (S (plus (plus l l) (S (plus l l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) (S (plus l l))) 
                                           (S (plus (plus l l) (S (plus l l)))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (S (plus l l))) (S (plus (plus l l) (S (plus l l)))))
                                  (S (S (S (S (plus (plus l l) (S (plus l l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (S (plus l l))) (S (plus (plus l l) (S (plus l l)))))
                                     (S (S (S (plus (plus l l) (S (plus l l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (S (plus l l))) (S (plus (plus l l) (S (plus l l)))))
                                        (S (S (plus (plus l l) (S (plus l l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) (S (plus l l))) (S (plus (plus l l) (S (plus l l)))))
                                           (S (plus (plus l l) (S (plus l l)))))) in
    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) lemma



