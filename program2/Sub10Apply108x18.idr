module Sub10Apply108x18

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(36x+6) --F[5,-2]->E[2,-4]--> 3(8x+1)
export
apply108x18 : (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))))))
    -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                     (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                               (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))),
         (Not . P) m))
apply108x18 {o} col = ((S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                           ** (lte108x18 o, fe108x18To24x3 o col)) where
  lte108x18 : (o:Nat) -> LTE (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))
          (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))))))
  lte108x18 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) LTEZero
  lte108x18 (S o) = let lemma = lte108x18 o in
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

    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (S (plus (plus (plus o o) o) (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (S (plus (plus (plus o o) o) (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (S (plus (plus (plus o o) o) (plus (plus o o) o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (plus (plus o o) o))  (plus (plus (plus o o) o) (plus (plus o o) o)))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                            (plus (plus (plus o o) o) (plus (plus o o) o)))
                                    (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o)
                                                                                                                         (plus (plus o o) o)))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                      (plus (plus o o) o))
                                                                                                                (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                                                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                                                                   (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                    (S (plus (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o) o))
                                                                                                                                                 (plus (plus (plus o o) o)
                                                                                                                                                       (plus (plus o o)
                                                      o)))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



