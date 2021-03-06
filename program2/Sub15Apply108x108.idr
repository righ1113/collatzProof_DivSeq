module Sub15Apply108x108

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(36x+36) --F[5,-2]->C[4,-4]--> 3(32x+31)
export
apply108x108 : (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                            (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                                    (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                    (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                              (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                        (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                          (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))))),
         (Not . P) m))
apply108x108 {o} col = ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))))))))))))))))))
                        ** (lte108x108 o, fc108x108To96x93 o col)) where
  lte108x108 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o)
                                                                                                                                  (plus o o))
                                                                                                                            (plus (plus o o) (plus o o)))
                                                                                                                      (plus (plus (plus o o) (plus o o))
                                                                                                                            (plus (plus o o) (plus o o))))
                                                                                                                (plus (plus (plus (plus o o) (plus o o))
                                                                                                                            (plus (plus o o) (plus o o)))
                                                                                                                      (plus (plus (plus o o) (plus o o))
                                                                                                                            (plus (plus o o)
                                                                                                                                  (plus o o)))))))))))))))))))))))))))))))))))))
          (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                           (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                             (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                     (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                       (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))))
  lte108x108 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x108 (S o) = let lemma = lte108x108 o in

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

    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (S (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (plus (plus o o) o))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                    (S (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                    (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                    (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                    (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                    (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o))))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o)))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o)))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                     (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                o)))))))))))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o))))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o)))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o)))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                               (S (S (plus (plus o o) o))))
                                                                                                                         (S (S (S (plus (plus (plus o o) o)
                                                                                                                                        (S (S (plus (plus o o) o))))))))
                                                                                                                   (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o))))
                                                                                                                                     (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                    (S (S (plus (plus o o)
                                                                                                                                                                o)))))))))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o)
                                       o)))))))))))))) in

      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



