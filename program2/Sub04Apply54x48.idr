module Sub04Apply54x48

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(18x+16) --A[6,-4]->B[1,-2]--> 3(4x+3)
export
apply54x48 : (Not . P) (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                            (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))))
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                               (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))),
         (Not . P) m))
apply54x48 {l} col = ((S (S (S (plus (plus l l) (plus l l))))) ** (lte54x48 l, ab54x30To12x9 l col)) where
  lte54x48 : (l:Nat) -> LTE (S (S (S (S (plus (plus l l) (plus l l))))))
                            (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                              (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))))
  lte54x48 Z = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
  lte54x48 (S k) = let lemma = lte54x48 k in
    rewrite (sym (plusSuccRightSucc k k)) in
    rewrite (sym (plusSuccRightSucc (plus k k) (S (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus k k) (plus k k))) in
    rewrite (sym (plusSuccRightSucc (plus k k) k)) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (S (S (S (plus (plus k k) k))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (S (S (plus (plus k k) k)))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) k) (S (S (plus (plus k k) k))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))  (S (S (S (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))  (S (S (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))  (S (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))  (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))  (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))  (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))  (S (S (S (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))  (S (S (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))  (S (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))  (S (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))  (S (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))))))))) in
    rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus k k) k) (S (S (plus (plus k k) k)))) (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))  (S (S (S (plus (plus (plus k k) k) (S (S (plus (plus k k) k))))))))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc) lemma



