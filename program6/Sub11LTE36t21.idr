module Sub11LTE36t21

import ProofColDivSeqPostulate

%default total


-- 6(6t+3)+3 --B[1,-2]--> 6t+3
export
lte36t21 : (k : Nat) -> LTE (S k) (S (S (S (plus (plus (plus k k) (plus k k)) (plus k k)))))
lte36t21 Z     = (lteSuccRight . LTESucc) LTEZero
lte36t21 (S k) =
  let lemma = lte36t21 k in
  rewrite (sym (plusSuccRightSucc k k)) in
  rewrite (sym (plusSuccRightSucc (plus k k) (S (plus k k)))) in
  rewrite (sym (plusSuccRightSucc (plus k k) (plus k k))) in
  rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (S (plus k k)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (plus k k))) in
    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) lemma



