module Sub10Apply108x18

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default partial
-- %language ElabReflection


-- 3(36x+6) --F[5,-2]->E[2,-4]--> 3(8x+1)
fe108x18To24x3 :
  (o:Nat) ->  P (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))) 2
    -> P (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))) 2
fe108x18To24x3 o prf =
  let prf2 = lvDown (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))) 2
                    prf in
    let prf3 = fe108x18To24x3' o prf2 in lvDown (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))) 3 prf3


export
apply108x18 : P (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))) 2
    -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                     (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                               (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))),
         P m 2))
apply108x18 {o} col = let col2 = fe108x18To24x3 o col in ((S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                           ** (lte108x18 o, col2)) where
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









