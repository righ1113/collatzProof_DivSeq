module Sub13LTE108t75

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+12)+3 --AB[6,-3,-2]--> 6(4t+1)+3
export
lte108t75 : (l : Nat) -> LTE (S (S (plus (plus l l) (plus l l)))) (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))
lte108t75 Z     = (lteSuccRight . LTESucc . LTESucc) LTEZero
lte108t75 (S l) =
  let lemma = lte108t75 l in
  rewrite (sym (plusSuccRightSucc l l)) in
  rewrite (sym (plusSuccRightSucc (plus l l) l)) in

  rewrite (sym (plusSuccRightSucc (plus l l) (S (plus l l)))) in
  rewrite (sym (plusSuccRightSucc (plus l l)    (plus l l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l) (S (S (S (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)    (S (S (plus (plus l l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)       (S (plus (plus l l) l)))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))    (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))       (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))          (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))             (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))                (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))) (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))    (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))       (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))          (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))             (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))                (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))) in
    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) lemma



