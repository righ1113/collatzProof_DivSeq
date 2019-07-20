module Sub08Apply108x63

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(36x+21) --F[5,-2]->B[1,-2]--> 3(16x+9)
export
apply108x63 : (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                              (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                  (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))),
         (Not . P) m))
apply108x63 {o} col = ((S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))
                                                           ** (lte108x63 o, fb108x63To48x27 o col)) where
  lte108x63 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                              (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))
          (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                           (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))
  lte108x63 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x63 (S o) = let lemma = lte108x63 o in
    rewrite (sym (plusSuccRightSucc o o)) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (S (plus o o)))) in
    rewrite (sym (plusSuccRightSucc (plus o o)  (plus o o))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (S (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (S (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (S (plus (plus o o) (plus o o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) (plus o o))  (plus (plus o o) (plus o o)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (S (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (S (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))  (plus (plus (plus o o) (plus o o))
                                                            (plus (plus o o) (plus o o))))) in

    rewrite (sym (plusSuccRightSucc (plus o o)  o)) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (plus (plus o o) o))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (plus (plus o o) o)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))  (S (S (S (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))  (S (S (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))  (S (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))  (S (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))  (S (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (plus (plus o o) o)))  (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                          (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                      (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                      (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (plus (plus (plus (plus o o) o)
                                                                                       (S (plus (plus o o) o)))
                                                                                 (S (S (plus (plus (plus o o) o)
                                                                                             (S (plus (plus o o)
                                                                                                      o)))))))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



