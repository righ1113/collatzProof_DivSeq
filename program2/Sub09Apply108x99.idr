module Sub09Apply108x99

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(36x+33) --F[5,-2]->E[2,-4]--> 3(8x+7)
export
apply108x99 : (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                            (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                    (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                              (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                           (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                          (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                     (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                    (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))),
         (Not . P) m))
apply108x99 {o} col = ((S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))
                                                           ** (lte108x99 o, fe108x99To24x21 o col)) where
  lte108x99 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))
          (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                              (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                       (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))
  lte108x99 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x99 (S o) = let lemma = lte108x99 o in
    rewrite (sym (plusSuccRightSucc o o)) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (S (plus o o)))) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (plus o o))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (S (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (plus (plus o o) (plus o o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (plus (plus o o) (plus o o)))) in

    rewrite (sym (plusSuccRightSucc (plus o o)  o)) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (S (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (plus (plus o o) o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))) in
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
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                    (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o)
                                                                                                                                              (S (S (plus (plus o o)
                                                                                                                                                          o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o)))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o)))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                    (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                                                   (S (S (plus (plus o o) o))))
                                                                                                                                                             (S (S (S (plus (plus (plus o o) o)
                                                                                                                                                                            (S (S (plus (plus o o)
                                                                                                                                                                                        o))))))))))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



