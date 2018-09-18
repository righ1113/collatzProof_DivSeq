module Sub01Apply18x3

import ProofColDivSeqBase

%default total
-- %language ElabReflection


-- 3(6x+1) --B[1,-2]--> 3x
postulate b18x3To3x' :
  (k:Nat) -> P (S (plus (plus (plus k k) (plus k k)) (plus k k))) 1 -> P k 2
b18x3To3x :
  (k:Nat) -> P (S (plus (plus (plus k k) (plus k k)) (plus k k))) 2 -> P k 2
b18x3To3x k prf =
  let prf2 = lvDown (S (plus (plus (plus k k) (plus k k)) (plus k k))) 2 prf in
    b18x3To3x' k prf2
export
apply18x3 : P (S (plus (plus (plus k k) (plus k k)) (plus k k))) 2
  -> (m : Nat **
      (LTE (S m) (S (plus (plus (plus k k) (plus k k)) (plus k k))), P m 2))
apply18x3 {k} col = let col2 = b18x3To3x k col in (k ** (lte18x3 k, col2)) where
  lte18x3 : (k:Nat) -> LTE (S k) (S (plus (plus (plus k k) (plus k k)) (plus k k)))
  lte18x3 Z = LTESucc LTEZero
  lte18x3 (S k) = rewrite (sym (plusSuccRightSucc k k)) in
    rewrite (sym (plusSuccRightSucc (plus k k) (S (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus k k) (plus k k))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (S (plus k k)))) in
    rewrite (sym (plusSuccRightSucc (plus (plus k k) (plus k k)) (plus k k))) in
      (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc) (lte18x3 k)
-- ---------------------------
