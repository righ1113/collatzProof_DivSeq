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
        rewrite definiDivSeq0 in IsLimited (Z ** definiLimited0)
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- ########################################



--            from sub0xxxxx
-- ########################################
-- 07 3(36x+9) --F[5,-2]->C[4,-4]--> 3(32x+7)
fc108x27To96x21 :
  (o:Nat) -> (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                             (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                       (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                 (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))
fc108x27To96x21 o =
  rewrite mapFC o 0 (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                      (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))) in id

-- 08 3(36x+21) --F[5,-2]->B[1,-2]--> 3(16x+9)
fb108x63To48x27 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))
fb108x63To48x27 o =
  rewrite mapFB o 0 1 (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                      (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                      (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))) in id

-- 09 3(36x+33) --F[5,-2]->E[2,-4]--> 3(8x+7)
fe108x99To24x21 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))
fe108x99To24x21 o =
  rewrite mapFE o 2 2 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))) in id

-- 10 3(36x+6) --F[5,-2]->E[2,-4]--> 3(8x+1)
fe108x18To24x3 :
  (o:Nat) ->  (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                        (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))))))
    -> (Not . P) (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
fe108x18To24x3 o =
  rewrite mapFE o 0 0 (plus (plus (plus o o) o) (plus (plus o o) o))
                      (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))
                      (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))) in id

-- 11 3(36x+18) --F[5,-2]->C[4,-4]--> 3(32x+15)
fc108x54To96x45 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))
fc108x54To96x45 o =
  rewrite mapFC o 1 (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                      (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))) in id

-- 12 3(36x+30) --F[5,-2]->B[1,-2]--> 3(16x+13)
fb108x90To48x39 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))
fb108x90To48x39 o =
  rewrite mapFB o 1 2 (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))) in id

-- 13 3(36x+12) --F[5,-2]->B[1,-2]--> 3(16x+5)
fb108x36To48x15 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                          (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))
                                    (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))))
    -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))
fb108x36To48x15 o =
  rewrite mapFB o 0 0 (S (plus (plus (plus o o) o) (plus (plus o o) o)))
                      (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                      (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))) in id

-- 14 3(36x+24) --F[5,-2]->E[2,-4]--> 3(8x+5)
fe108x72To24x15 :
  (o:Nat) ->  (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                              (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))))
    -> (Not . P) (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))
fe108x72To24x15 o =
  rewrite mapFE o 2 1 (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))) in id

-- 15 3(36x+36) --F[5,-2]->C[4,-4]--> 3(32x+31)
fc108x108To96x93 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))))))))))))))))))
fc108x108To96x93 o =
  rewrite mapFC o 3 (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))) in id
-- ########################################



