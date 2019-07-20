module Sub07Apply108x27

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(36x+9) --F[5,-2]->C[4,-4]--> 3(32x+7)
export
apply108x27 : (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                     (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                               (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))),
         (Not . P) m))
apply108x27 {o} col = ((S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                  (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))) ** (lte108x27 o, fc108x27To96x21 o col)) where
  lte108x27 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                        (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))
          (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))
  lte108x27 Z = (lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x27 (S o) = let lemma = lte108x27 o in
    rewrite (sym (plusSuccRightSucc o o)) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (S (plus o o)))) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (plus o o))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (S (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (plus (plus o o) (plus o o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (plus (plus o o) (plus o o)))) in
    rewrite (sym (plusSuccRightSucc (plus o o)  o)) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (plus (plus o o) o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (plus (plus o o) o)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (plus (plus o o) o))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (plus (plus (plus o o) o) (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (plus (plus (plus o o) o) (plus (plus o o) o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                    (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                                                 (S (plus (plus (plus o o) o)
                                                                                                                                                          (plus (plus o o) o))))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))) in

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
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



