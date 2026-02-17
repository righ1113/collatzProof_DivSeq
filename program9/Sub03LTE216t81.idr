module Sub03LTE216t81

import ProofColDivSeqPostulate

%default total


-- 6(36t+13)+3 --DE[3,0,-4]--> 6(2t)+3
export
lte216t81 : (m : Nat) -> LTE (S (m+m))
  (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))
lte216t81 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) LTEZero
lte216t81 (S m) =
  let lemma = lte216t81 m in

  rewrite (sym (plusSuccRightSucc m m)) in

  rewrite (sym (plusSuccRightSucc (plus m m) m)) in

  rewrite (sym (plusSuccRightSucc (plus (plus m m) m) (S (S (plus (plus m m) m))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)    (S (plus (plus m m) m)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)       (plus (plus m m) m))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                  (S (S (S (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                     (S (S (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                           (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                              (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                                 (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                     (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                           (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                              (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                 (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                    (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                       (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                          (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                             (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                                (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                                                   (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                               (S (S (plus (plus (plus m m) m)
                                                                                           (plus (plus m m) m))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                     (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                        (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                           (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                              (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                 (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                    (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                       (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                          (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                             (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                                (S (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m))))))))
                                                                   (S (S (plus (plus (plus (plus m m) m)
                                                                               (plus (plus m m) m))
                                                                                     (S (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) lemma


export
lte216t81_2 : (m : Nat) -> LTE (S (m+m))
  (S (S (S (S (S (S ((m+m+m)+(m+m+m))+S ((m+m+m)+(m+m+m))) + S (S ((m+m+m)+(m+m+m))+S ((m+m+m)+(m+m+m))) + S (S ((m+m+m)+(m+m+m))+S ((m+m+m)+(m+m+m))))))))
lte216t81_2 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) LTEZero
lte216t81_2 (S m) =
  let lemma = lte216t81_2 m in

  rewrite (sym (plusSuccRightSucc m m)) in

  rewrite (sym (plusSuccRightSucc (plus m m) m)) in

  rewrite (sym (plusSuccRightSucc (plus (plus m m) m) (S (S (plus (plus m m) m))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)    (S (plus (plus m m) m)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)       (plus (plus m m) m))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                  (S (S (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                      (S (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                            (S (S (S (plus (plus (plus m m) m) (plus (plus m m) m))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                              (S (S (plus (plus (plus m m) m) (plus (plus m m) m)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (plus (plus m m) m))
                                                  (S (plus (plus (plus m m) m) (plus (plus m m) m))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                      (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                            (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                              (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                  (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                    (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                        (S (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                          (S (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                              (S (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                                (S (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                        (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                                                    (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                                                (S (plus (plus (plus m m) m)
                                                                                            (plus (plus m m) m)))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                      (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                        (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                            (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                              (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                  (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                    (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                        (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                          (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                              (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                                (S (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                                    (plus (plus m m) m))
                                              (S (plus (plus (plus m m) m) (plus (plus m m) m))))
                                        (S (S (plus (plus (plus (plus m m) m) (plus (plus m m) m))
                                                    (S (plus (plus (plus m m) m)
                                                                (plus (plus m m) m)))))))
                                                                    (S (S (plus (plus (plus (plus m m) m)
                                                                                (plus (plus m m) m))
                                                                                      (S (plus (plus (plus m m) m)
                                                  (plus (plus m m) m)))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) lemma



