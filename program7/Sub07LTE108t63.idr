module Sub07LTE108t63

import ProofColDivSeqPostulate

%default total


-- 6(18t+10)+3 --BF[1,3,-2]--> 6(8t+4)+3
export
lte108t63 : (l : Nat) -> LTE (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))
  (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))
lte108t63 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
lte108t63 (S l) =
  let lemma = lte108t63 l in

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

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                  (S (S (S (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                     (S (S (plus (plus l l) l))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                        (S (plus (plus l l) l)))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                  (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                          l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                     (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                          l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                          l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                           (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                          l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                              (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                          l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                                 (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                          l))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                  (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                        l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                     (S (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                        l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                        (S (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                        l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                           (S (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                        l))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                              (S (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                        l)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                        (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                                 (S (S (plus (plus (plus l l) l) (S (plus (plus l l)
                                        l))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



