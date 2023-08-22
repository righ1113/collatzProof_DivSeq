module Sub12LTE108t39

import ProofColDivSeqPostulate

%default total


-- 6(18t+6)+3 --DB[3,-1,-2]--> 6(2t)+3
export
lte108t39 : (l : Nat) -> LTE (S (plus l l)) (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))
lte108t39 Z     = (lteSuccRight . LTESucc) LTEZero
lte108t39 (S l) =
  let lemma = lte108t39 l in
  rewrite (sym (plusSuccRightSucc l l)) in
  rewrite (sym (plusSuccRightSucc (plus l l) l)) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l) (S (S (plus (plus l l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)    (S (plus (plus l l) l)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)       (plus (plus l l) l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l)) (S (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))    (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))       (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))          (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))             (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))                (S (plus (plus (plus l l) l) (plus (plus l l) l))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l)) (S (plus (plus (plus l l) l) (plus (plus l l) l)))) (S (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l)) (S (plus (plus (plus l l) l) (plus (plus l l) l))))    (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l)) (S (plus (plus (plus l l) l) (plus (plus l l) l))))       (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l)) (S (plus (plus (plus l l) l) (plus (plus l l) l))))          (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l)) (S (plus (plus (plus l l) l) (plus (plus l l) l))))             (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l)) (S (plus (plus (plus l l) l) (plus (plus l l) l))))                (S (plus (plus (plus l l) l) (plus (plus l l) l))))) in
    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) lemma



