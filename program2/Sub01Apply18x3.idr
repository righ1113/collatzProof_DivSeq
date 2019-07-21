module Sub01Apply18x3

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqPostuProof

%default total
-- %language ElabReflection


-- 3(6x+1) --B[1,-2]--> 3x
export
apply18x3 : (Not . P) (S (plus (plus (plus k k) (plus k k)) (plus k k)))
  -> (m : Nat **
      (LTE (S m) (S (plus (plus (plus k k) (plus k k)) (plus k k))), (Not . P) m))
apply18x3 {k} col = (k ** (lte18x3 k, b18x3To3x k col)) where
  lte18x3 : (k:Nat) -> LTE (S k) (S (plus (plus (plus k k) (plus k k)) (plus k k)))
  lte18x3 Z = LTESucc LTEZero
  lte18x3 (S k) = rewrite (sym (plusSuccRightSucc k k)) in
    rewrite (sym (plusSuccRightSucc (plus k k) (S (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus k k) (plus k k))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (S (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (plus k k))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) (lte18x3 k)



