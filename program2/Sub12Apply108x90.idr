module Sub12Apply108x90

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(36x+30) --F[5,-2]->B[1,-2]--> 3(16x+13)
export
apply108x90 : (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                      (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                                (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))  (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                        (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                           (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                          (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                                     (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                    (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))),
         (Not . P) m))
apply108x90 {o} col = ((S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))
                                                           ** (lte108x90 o, fb108x90To48x39 o col)) where
  lte108x90 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))
          (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                              (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))                                  (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))
  lte108x90 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x90 (S o) = let lemma = lte108x90 o in
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

    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (S (plus (plus o o) o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (S (plus (plus o o) o)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus o o) o)  (S (S (plus (plus o o) o))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o)))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                                  (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                    (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o)
                                            o)))))))))))) in

    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o))))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o)))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus o o) o)
                                                                                                                            (S (S (plus (plus o o) o))))
                                                                                                                      (S (S (plus (plus (plus o o) o)
                                                                                                                                  (S (S (plus (plus o o) o)))))))
                                                                                                                (S (S (S (plus (plus (plus (plus o o) o)
                                                                                                                                     (S (S (plus (plus o o) o))))
                                                                                                                               (S (S (plus (plus (plus o o) o)
                                                                                                                                           (S (S (plus (plus o o) o)))))))))))
                                    (S (S (S (plus (plus (plus (plus o
                                                                                                                                                                               o) o)
                                                                                                                                                                   (S (S (plus (plus o o)
                                                                                                                                                                               o))))
                                                                                                                                                             (S (S (plus (plus (plus o o)
                                                                                                                                                                               o) (S (S (plus (plus o o)
    o)))))))))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



