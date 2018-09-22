module Sub04Apply54x48

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


-- 3(18x+16) --A[6,-4]->B[1,-2]--> 3(4x+3)
ab54x30To12x9 :
  (l:Nat) -> P (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                            (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) 2
    -> P (S (S (S (plus (plus l l) (plus l l))))) 2
ab54x30To12x9 l prf =
  let prf2 = lvDown (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                            (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) 2
                    prf in
    let prf3 = ab54x30To12x9' l prf2 in lvDown (S (S (S (plus (plus l l) (plus l l))))) 3 prf3

export
apply54x48 : P (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                            (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) 2
  -> (m : Nat **
        (LTE (S m)
             (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))) (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                               (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))),
         P m 2))
apply54x48 {l} col = let col2 = ab54x30To12x9 l col in ((S (S (S (plus (plus l l) (plus l l))))) ** (lte54x48 l, col2)) where
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









