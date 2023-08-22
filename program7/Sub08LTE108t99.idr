module Sub08LTE108t99

import ProofColDivSeqPostulate

%default total


-- 6(18t+16)+3 --EF[2,1,-2]--> 6(8t+3)+3
export
lte108t99 : (l : Nat) -> LTE (S (S (S (S ((l+l)+(l+l))))))
  (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l)))))))
lte108t99 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
lte108t99 (S l) =
  let lemma = lte108t99 l in

  rewrite (sym (plusSuccRightSucc l l)) in

  rewrite (sym (plusSuccRightSucc (plus l l) l)) in

  rewrite (sym (plusSuccRightSucc (plus l l) (S (plus l l)))) in
  rewrite (sym (plusSuccRightSucc (plus l l)    (plus l l))) in

  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                  (S (S (S (S (plus (plus l l) l))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                     (S (S (S (plus (plus l l) l)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus l l) l)
                                        (S (S (plus (plus l l) l))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l)
                                           l)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                     (S (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l)
                                           l))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                        (S (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l)
                                           l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                           (S (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l)
                                           l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                              (S (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l)
                                           l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                                 (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l)
                                           l))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                        (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                  (S (S (S (S (S (S (S (S (plus (plus (plus l l) l)
                        (S (S (plus (plus l l) l)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                        (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                     (S (S (S (S (S (S (S (plus (plus (plus l l) l)
                        (S (S (plus (plus l l) l))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                        (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                        (S (S (S (S (S (S (plus (plus (plus l l) l)
                        (S (S (plus (plus l l) l)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                        (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                           (S (S (S (S (S (plus (plus (plus l l) l)
                        (S (S (plus (plus l l) l))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                        (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                              (S (S (S (S (plus (plus (plus l l) l)
                        (S (S (plus (plus l l) l)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                        (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                                 (S (S (S (plus (plus (plus l l) l)
                        (S (S (plus (plus l l) l))))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) lemma



