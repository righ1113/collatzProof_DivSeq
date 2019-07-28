module ProofColDivSeqPostuProof

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection
%access export

%hide Language.Reflection.P

--            from ProofColDivSeqBase
-- ########################################
base0 : P Z
base0 = rewrite definiP Z in
        rewrite definiDivSeq0 in IsLimited00 (Z ** definiLimited0)
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- ########################################



--            from sub0xxxxx
-- ########################################
-- 01 3(6x+1) --B[1,-2]--> 3x
b18x3To3x : (k : Nat)
  -> (Not . P) (S (plus (plus (plus k k) (plus k k)) (plus k k))) -> (Not . P) k
b18x3To3x k = rewrite definiP (S (plus (plus (plus k k) (plus k k)) (plus k k))) in
              rewrite definiP k in \prfF, prf => (prfF . IsLimited01 k) prf

-- 02 3(18x+4) --A[6,-4]--> 3(24x+3) -->E[2,-4]--> 3(2x)
ae54x12To6x : (l : Nat)
  -> (Not . P) (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                 (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                           (S (plus (plus (plus l l) l) (plus (plus l l) l))))))
    -> (Not . P) (plus l l)
ae54x12To6x l = rewrite definiP (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                                                  (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                                            (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) in
                rewrite definiP (plus l l) in \prfF, prf => (prfF . IsLimited02 l) prf

-- 03 3(18x+10) --A[6,-4]->C[4,-4]--> 3(8x+3)
ac54x30To24x9 : (l : Nat)
  -> (Not . P) (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                    (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                              (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))
    -> (Not . P) (S (S (S (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))))))
ac54x30To24x9 l = rewrite definiP (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l)))
                                                       (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                                                 (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))) in
                  rewrite definiP (S (S (S (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))))) in \prfF, prf => (prfF . IsLimited03 l) prf

-- 04 3(18x+16) --A[6,-4]->B[1,-2]--> 3(4x+3)
ab54x30To12x9 : (l : Nat)
  -> (Not . P) (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                       (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                 (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))))
    -> (Not . P) (S (S (S (plus (plus l l) (plus l l)))))
ab54x30To12x9 l = rewrite definiP (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                                          (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                                                    (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) in
                  rewrite definiP (S (S (S (plus (plus l l) (plus l l))))) in \prfF, prf => (prfF . IsLimited04 l) prf

-- 05 3(3x+2) --C[4,-4]--> 3x
c9x6To3x : (j : Nat)
  -> (Not . P) (S (S (plus (plus j j) j))) -> (Not . P) j
c9x6To3x j = rewrite definiP (S (S (plus (plus j j) j))) in
             rewrite definiP j in \prfF, prf => (prfF . IsLimited05 j) prf

-- 06 3(12x+3) --E[2,-4]--> 3x
e36x9To3x : (l : Nat)
  -> (Not . P) (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l))))))
    -> (Not . P) l
e36x9To3x l = rewrite definiP (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l)))))) in
              rewrite definiP l in \prfF, prf => (prfF . IsLimited06 l) prf

-- 07 3(36x+9) --F[5,-2]->C[4,-4]--> 3(32x+7)
fc108x27To96x21 :
  (o:Nat) -> (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                     (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                               (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                         (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))
fc108x27To96x21 o =
  rewrite definiP (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                      (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                                (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))) in
  rewrite definiP (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))
  in \prfF, prf => (prfF . IsLimited07 o) prf

-- 08 3(36x+21) --F[5,-2]->B[1,-2]--> 3(16x+9)
fb108x63To48x27 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                        (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                                  (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                            (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))
fb108x63To48x27 o =
  rewrite definiP (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                   (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                             (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                       (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))) in
  rewrite definiP (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))
  in \prfF, prf => (prfF . IsLimited08 o) prf

-- 09 3(36x+33) --F[5,-2]->E[2,-4]--> 3(8x+7)
fe108x99To24x21 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))
fe108x99To24x21 o = rewrite definiP (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                                        (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                                  (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                                            (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))) in
                    rewrite definiP (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))
                    in \prfF, prf => (prfF . IsLimited09 o) prf

-- 10 3(36x+6) --F[5,-2]->E[2,-4]--> 3(8x+1)
fe108x18To24x3 :
  (o:Nat) ->  (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                        (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))))))
    -> (Not . P) (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
fe108x18To24x3 o = rewrite definiP (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                                 (plus (plus (plus o o) o) (plus (plus o o) o)))
                                                           (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                                                     (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))) in
                   rewrite definiP (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                   in \prfF, prf => (prfF . IsLimited10 o) prf

-- 11 3(36x+18) --F[5,-2]->C[4,-4]--> 3(32x+15)
fc108x54To96x45 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))
fc108x54To96x45 o = rewrite definiP (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                                     (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                                         (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))) in
                    rewrite definiP (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))
                    in \prfF, prf => (prfF . IsLimited11 o) prf

-- 12 3(36x+30) --F[5,-2]->B[1,-2]--> 3(16x+13)
fb108x90To48x39 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))
fb108x90To48x39 o = rewrite definiP (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))) in
                    rewrite definiP (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))
                    in \prfF, prf => (prfF . IsLimited12 o) prf

-- 13 3(36x+12) --F[5,-2]->B[1,-2]--> 3(16x+5)
fb108x36To48x15 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                          (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))
                                    (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))))
    -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))
fb108x36To48x15 o = rewrite definiP (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                          (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))
                                    (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))))) in
                    rewrite definiP (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))
                    in \prfF, prf => (prfF . IsLimited13 o) prf

-- 14 3(36x+24) --F[5,-2]->E[2,-4]--> 3(8x+5)
fe108x72To24x15 :
  (o:Nat) ->  (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                              (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))))
    -> (Not . P) (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))
fe108x72To24x15 o = rewrite definiP (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                              (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))))) in
                    rewrite definiP (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))
                    in \prfF, prf => (prfF . IsLimited14 o) prf

-- 15 3(36x+36) --F[5,-2]->C[4,-4]--> 3(32x+31)
fc108x108To96x93 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))))))))))))))))))
fc108x108To96x93 o = rewrite definiP (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))))) in
                     rewrite definiP (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))))))))))))))))))
                     in \prfF, prf => (prfF . IsLimited15 o) prf
-- ########################################



