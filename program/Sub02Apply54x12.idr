module Sub02Apply54x12

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default partial
-- %language ElabReflection


-- 3(18x+4) --A[6,-4]->E[2,-4]--> 3(2x)
ae54x12To6x :
  (l:Nat) -> P (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                              (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                        (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) 2
    -> P (plus l l) 2
ae54x12To6x l prf =
  let prf2 = lvDown (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                              (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                        (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) 2
                    prf in
    let prf3 = ae54x12To6x' l prf2 in lvDown (plus l l) 3 prf3
export
apply54x12 : P (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                            (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                      (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) 2
  -> (m : Nat **
        (LTE (S m)
             (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                               (S (plus (plus (plus l l) l)
                                        (plus (plus l l) l))))
                         (S (plus (plus (plus l l) l) (plus (plus l l) l)))))),
         P m 2))
apply54x12 {l} col = let col2 = ae54x12To6x l col in ((plus l l) ** (lte54x12 l, col2)) where
  lte54x12 : (l:Nat) -> LTE (S (plus l l))
                            (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                  (S (plus (plus (plus l l) l)
                                           (plus (plus l l) l))))
                            (S (plus (plus (plus l l) l)
                                     (plus (plus l l) l))))))
  lte54x12 Z = LTESucc LTEZero
  lte54x12 (S k) = let lemma = lte54x12 k in rewrite (sym (plusSuccRightSucc k k)) in
    rewrite (sym (plusSuccRightSucc (plus k k) k)) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (S (plus (plus k k) k))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (plus (plus k k) k)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (plus (plus k k) k))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (plus (plus k k) k)) (S (S (S (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (plus (plus k k) k)) (S (S (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (plus (plus k k) k)) (S (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (plus (plus k k) k)) (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (plus (plus k k) k)) (S (S (plus (plus (plus k k) k) (plus (plus k k) k)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k)))) (S (S (S (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k)))) (S (S (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k)))) (S (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (plus (plus k k) k))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k)))) (S (S (plus (plus (plus k k) k) (plus (plus k k) k)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (plus (plus k k) k)) (S (plus (plus (plus k k) k) (plus (plus k k) k)))) (S (plus (plus (plus k k) k) (plus (plus k k) k))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc) lemma
-- ---------------------------
