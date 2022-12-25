module Sub04LTE216t153

import ProofColDivSeqPostulate

%default total


-- 6(36t+25)+3 --AE[6,-2,-4]--> 6(4t+1)+3
export
lte216t153 : (m : Nat) -> LTE (S (S ((m+m)+(m+m))))
  (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))
lte216t153 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) LTEZero
lte216t153 (S m) =
  let lemma = lte216t153 m in

  rewrite (sym (plusSuccRightSucc m m)) in

  rewrite (sym (plusSuccRightSucc (plus m m) (S (plus m m)))) in
  rewrite (sym (plusSuccRightSucc (plus m m)    (plus m m))) in

  rewrite (sym (plusSuccRightSucc (plus m m) m)) in

  rewrite (sym (plusSuccRightSucc (plus (plus m m) m) (S (S (S (plus (plus m m) m)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)    (S (S (plus (plus m m) m))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)       (S (plus (plus m m) m)))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                        (S (S (S (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                           (S (S (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                              (S (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                                 (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                                    (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                                       (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                           (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m)))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                              (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                 (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                       (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                          (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                             (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                                (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                                   (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                                      (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))
                                                         (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (S (plus (plus (plus m m) m)
                                                                         (S (plus (plus m m)
                                                          m)))))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                   (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                      (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                         (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                            (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                               (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                                  (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                                     (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                                        (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                                           (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (S (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                               (S (plus (plus m m) m)))
                                                         (S (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m)))))))))))
                                              (S (S (S (plus (plus (plus (plus m m) m)
                                                                     (S (plus (plus m m) m)))
                                                    (S (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) lemma


export
lte216t153_2 : (m : Nat) -> LTE (S (S ((m+m)+(m+m))))
  (S (S (S (S (S (S (S (m+m+m)+S (m+m+m))+S (S (m+m+m)+S (m+m+m))) + S (S (S (m+m+m)+S (m+m+m))+S (S (m+m+m)+S (m+m+m))) + S (S (S (m+m+m)+S (m+m+m))+S (S (m+m+m)+S (m+m+m))))))))
lte216t153_2 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) LTEZero
lte216t153_2 (S m) =
  let lemma = lte216t153_2 m in

  rewrite (sym (plusSuccRightSucc m m)) in

  rewrite (sym (plusSuccRightSucc (plus m m) (S (plus m m)))) in
  rewrite (sym (plusSuccRightSucc (plus m m)    (plus m m))) in

  rewrite (sym (plusSuccRightSucc (plus m m) m)) in

  rewrite (sym (plusSuccRightSucc (plus (plus m m) m) (S (S (S (plus (plus m m) m)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)    (S (S (plus (plus m m) m))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)       (S (plus (plus m m) m)))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                        (S (S (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                            (S (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                              (S (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                                  (S (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                                    (S (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                                        (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m)))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                              (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                  (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                        (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                          (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                              (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                                (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                                    (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                                      (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (plus (plus m m) m)))
                    (S (S (plus (plus (plus m m) m) (S (plus (plus m m) m))))))
                                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                          (S (plus (plus m m)
                                                          m))))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                      (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                          (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                            (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                                (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                                  (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                                      (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                                        (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                                            (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                      (S (plus (plus m m) m)))
                                                (S (S (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m))))))
                                          (S (S (S (plus (plus (plus (plus m m) m)
                                                                (S (plus (plus m m) m)))
                                                          (S (S (plus (plus (plus m m) m)
                                                                        (S (plus (plus m m) m))))))))))
                                              (S (S (S (plus (plus (plus (plus m m) m)
                                                                      (S (plus (plus m m) m)))
                                                    (S (S (plus (plus (plus m m) m)
                                                          (S (plus (plus m m)
                              m))))))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) lemma



