module Sub11Apply108x54

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(36x+18) --F[5,-2]->C[4,-4]--> 3(32x+15)
export
apply108x54 : (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                          (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                              (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                        (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                  (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))),
         (Not . P) m))
apply108x54 {o} col = ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                          (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))) ** (lte108x54 o, fc108x54To96x45 o col)) where
  lte108x54 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                                                      (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                                                      (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))))
          (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))
  lte108x54 Z = (lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x54 (S o) = let lemma = lte108x54 o in
    rewrite (sym (plusSuccRightSucc o o)) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (S (plus o o)))) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (plus o o))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (S (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (plus (plus o o) (plus o o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (plus (plus o o) (plus o o)))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (S (S (S (S (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (S (S (S (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (S (S (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (S (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (S (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                    (plus (plus (plus o o) (plus o o))
                                            (plus (plus o o) (plus o o))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) (plus o o))
                                                                                                    (plus (plus o o) (plus o o)))
                                                                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (plus (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o o)))
                                                                                                                                              (plus (plus (plus o o)
                                                                                                                                                          (plus o o))
                                                                                                                                                    (plus (plus o o)
                                                                                                                                                          (plus o
                                                                                                                                                                o)))))) in

    rewrite (sym (plusSuccRightSucc (plus o o)  o)) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (plus (plus o o) o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (plus (plus o o) o)))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                    (S (S (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                    (S (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                    (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                    (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                    (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                    (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                               (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o)
                                            (S (plus (plus o o) o))))))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                         (S (plus (plus o o) o)))
                                                                                                                   (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                                                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                                                         (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                             (S (plus (plus o o) o)))
                                                                                                                                                       (S (plus (plus (plus o o) o)
                                                                                                                                                                (S (plus (plus o o)
                                          o))))))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



