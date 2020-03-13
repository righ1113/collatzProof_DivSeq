module Sub06LTE108t27

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+4)+3 --CF[4,1,-2]--> 6(16t+3)+3
export
lte108t27 : (l : Nat) -> LTE (S (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))))
  (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))
lte108t27 Z     = (LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
lte108t27 (S l) =
  let lemma = lte108t27 l in

  rewrite (sym (plusSuccRightSucc l l)) in

  rewrite (sym (plusSuccRightSucc (plus l l) l)) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l) l)) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)
                                  (S (S (S (plus (plus (plus l l) l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)
                                     (S (S (plus (plus (plus l l) l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)
                                        (S (plus (plus (plus l l) l) l)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) l)
                                           (plus (plus (plus l l) l) l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                  (S (S (S (plus (plus (plus l l) l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                     (S (S (plus (plus (plus l l) l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                        (S (plus (plus (plus l l) l) l)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                           (plus (plus (plus l l) l) l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                                                       (plus (plus (plus l l) l) l))
                                  (S (S (S (plus (plus (plus l l) l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                                                       (plus (plus (plus l l) l) l))
                                     (S (S (plus (plus (plus l l) l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                                                       (plus (plus (plus l l) l) l))
                                        (S (plus (plus (plus l l) l) l)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus l l) l) l) (plus (plus (plus l l) l) l))
                                                                       (plus (plus (plus l l) l) l))
                                           (plus (plus (plus l l) l) l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                  (S (S (plus (plus l l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                     (S (plus (plus l l) l)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                        (plus (plus l l) l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))
                                  (S (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))
                                     (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))
                                        (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))
                                           (S (S (S (plus (plus (plus l l) l) (plus (plus l l) l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))
                                              (S (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (plus (plus l l) l))
                                                 (S (plus (plus (plus l l) l) (plus (plus l l) l))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                  (S (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l)
                                             l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                     (S (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l)
                                             l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                        (S (S (S (S (plus (plus (plus l l) l) (plus (plus l l)
                                             l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                           (S (S (S (plus (plus (plus l l) l) (plus (plus l l)
                                             l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                              (S (S (plus (plus (plus l l) l) (plus (plus l l)
                                             l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                                 (S (plus (plus (plus l l) l) (plus (plus l l)
                                             l))))) in

    (lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



