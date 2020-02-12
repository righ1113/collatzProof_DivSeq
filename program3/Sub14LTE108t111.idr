module Sub13LTE108t111

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+18)+3 --FB[5,-1,-2]--> 6(8t+7)+3
export
lte108t111 : (l : Nat) -> LTE (S (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))))
  (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l)))))))))
lte108t111 Z     = (lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
lte108t111 (S l) =
  let lemma = lte108t111 l in
  rewrite (sym (plusSuccRightSucc l l)) in
  rewrite (sym (plusSuccRightSucc (plus l l) l)) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l) l)) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l) (S (S (S (plus (plus (plus l l) l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)    (S (S (plus (plus (plus l l) l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)       (S (plus (plus (plus l l) l) l)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)          (plus (plus (plus l l) l) l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l) (S (S (S (S (plus (plus l l) l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l) (S (S (S (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)    (S (S (plus (plus l l) l))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))) in
    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



