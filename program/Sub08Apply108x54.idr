module Sub08Apply108x54

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(36x+18) --F[5,-2]->C[4,-4]--> 3(32x+15)
fc108x54To96x45 :
  (o:Nat) -> P (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                           (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))) 2
    -> P (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))) 2
fc108x54To96x45 o prf =
  let prf2 = lvDown (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                           (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))) 2
                    prf in
    let prf3 = fc108x54To96x45' o prf2 in lvDown (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))) 3 prf3

export
apply108x54 : P (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                           (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))) 2
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                  (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))),
         P m 2))
apply108x54 {o} col = let col2 = fc108x54To96x45 o col in ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))
                                                           ** (lte108x54 o, col2)) where
  lte108x54 : (o:Nat) -> LTE (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                                                      (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))
                                                                      (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))))
                             (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))
  lte108x54 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte108x54 (S o) = let lemma = lte108x54 o in
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
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (S (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus o o)
                                                      (plus o o))
                                                (plus (plus o o) (plus o o)))
                                          (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (plus (plus (plus (plus o o)
                                                                                                   (plus o o))
                                                                                             (plus (plus o o) (plus o o)))
                                                                                       (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))) in
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
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma








