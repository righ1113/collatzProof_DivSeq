module Sub03Apply54x30

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(18x+10) --A[6,-4]->C[4,-4]--> 3(8x+3)
export
apply54x30 : (Not . P) (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                         (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                            (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))),
         (Not . P) m))
apply54x30 {l} col = ((S (S (S (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))))) ** (lte54x30 l, ac54x30To24x9 l col)) where
  lte54x30 : (l:Nat) -> LTE (S (S (S (S (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))))))
                            (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                           (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))
  lte54x30 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte54x30 (S k) = let lemma = lte54x30 k in
    rewrite (sym (plusSuccRightSucc k k)) in
    rewrite (sym (plusSuccRightSucc (plus k k) (S (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus k k) (plus k k))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (S (S (S (plus (plus k k) (plus k k))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (S (S (plus (plus k k) (plus k k)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (S (plus (plus k k) (plus k k))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (plus (plus k k) (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus k k) k)) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (S (S (plus (plus k k) k)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (S (plus (plus k k) k))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (plus (plus k k) k)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (S (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))  (S (S (S (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))  (S (S (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))  (S (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))  (S (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))  (S (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k)))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (plus (plus k k) k))) (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))  (S (S (plus (plus (plus k k) k) (S (plus (plus k k) k))))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



