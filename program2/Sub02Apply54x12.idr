module Sub02Apply54x12

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(18x+4) --A[6,-4]->E[2,-4]--> 3(2x)
export
apply54x12 : (Not . P) (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                            (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                      (S (plus (plus (plus l l) l) (plus (plus l l) l))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                               (S (plus (plus (plus l l) l)
                                        (plus (plus l l) l))))
                         (S (plus (plus (plus l l) l) (plus (plus l l) l)))))),
         (Not . P) m))
apply54x12 {l} col = ((plus l l) ** (lte54x12 l, ae54x12To6x l col)) where
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



