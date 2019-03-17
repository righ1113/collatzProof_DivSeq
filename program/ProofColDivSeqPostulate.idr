module ProofColDivSeqPostulate

import ProofColDivSeqBase

%default total
-- %language ElabReflection
%access export


--            from ProofColDivSeqBase
-- ########################################
-- 無限降下法（の変形） Isabelleで証明した
postulate infiniteDescent :
  ((n:Nat) -> P (S n) 2 -> (m ** (LTE (S m) (S n), P m 2)))
    -> All Limited $ allDivSeq Z 2
      -> All Limited $ allDivSeq (n+n+n) 2

-- BaseLog0.txtより、保証される
postulate base0 : All Limited $ allDivSeq Z 2
-- ########################################



--            from ProofColDivSeqLvDown
-- ########################################
-- 前提 Isabelleで証明した
postulate any1 : (pp : a -> Type) -> (xs, ys : List a)
  -> Any pp (xs ++ ys) = Either (Any pp xs) (Any pp ys)

-- 前方を削っているのは、（有限or無限を判定する）末尾に影響を与えないから
postulate changeA : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqA n lv))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ ((x+7)*3) 4 SIsNotZ) lv))
postulate changeA0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqA n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ ((x+7)*3) 4 SIsNotZ))])
postulate changeB : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqB n lv))
  -> (Any (Not . Limited) (allDivSeq (x*6+3) lv))
postulate changeB0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqB n 0))
  -> (Any (Not . Limited) [Just (divSeq (x*6+3))])
postulate changeC : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqC n lv))
  -> (Any (Not . Limited) (allDivSeq (x*3+6) lv))
postulate changeC0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqC n 0))
  -> (Any (Not . Limited) [Just (divSeq (x*3+6))])
postulate changeD : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqD n lv))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ ((x+1)*3) 2 SIsNotZ) lv))
postulate changeD0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqD n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ ((x+1)*3) 2 SIsNotZ))])
postulate changeE : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqE n lv))
  -> (Any (Not . Limited) (allDivSeq (x*12+9) lv))
postulate changeE0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqE n 0))
  -> (Any (Not . Limited) [Just (divSeq (x*12+9))])
postulate changeF : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqF n lv))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ ((x+3)*3) 8 SIsNotZ) lv))
postulate changeF0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqF n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ ((x+3)*3) 8 SIsNotZ))])
postulate changeG : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqG n lv))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ (x `minus` 21) 64 SIsNotZ) lv))
postulate changeG0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqG n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ (x `minus` 21) 64 SIsNotZ))])

postulate unfold3 : (x, lv:Nat) -> (Any (Not . Limited) $ allDivSeq x lv) =
  Either (Any (Not . Limited) $ allDivSeq x (pred lv))
    (Either (Any (Not . Limited) $ allDivSeq (divNatNZ ((x+7)*3) 4 SIsNotZ) (pred lv))
      (Either (Any (Not . Limited) $ allDivSeq (x*6+3) (pred lv))
        (Either (Any (Not . Limited) $ allDivSeq (x*3+6) (pred lv))
          (Either (Any (Not . Limited) $ allDivSeq (divNatNZ ((x+1)*3) 2 SIsNotZ) (pred lv))
            (Either (Any (Not . Limited) $ allDivSeq (x*12+9) (pred lv))
              (Either (Any (Not . Limited) $ allDivSeq (divNatNZ ((x+3)*3) 8 SIsNotZ) (pred lv))
                      (Any (Not . Limited) $ allDivSeq (divNatNZ (x `minus` 21) 64 SIsNotZ) (pred lv))))))))
postulate unfold0 : (x:Nat) -> (Any (Not . Limited) $ allDivSeq x 0) =
  Either (Any (Not . Limited) $ [Just (divSeq x)])
    (Either (Any (Not . Limited) $ [Just (divSeq (divNatNZ ((x+7)*3) 4 SIsNotZ))])
      (Either (Any (Not . Limited) $ [Just (divSeq (x*6+3))])
        (Either (Any (Not . Limited) $ [Just (divSeq (x*3+6))])
          (Either (Any (Not . Limited) $ [Just (divSeq (divNatNZ ((x+1)*3) 2 SIsNotZ))])
            (Either (Any (Not . Limited) $ [Just (divSeq (x*12+9))])
              (Either (Any (Not . Limited) $ [Just (divSeq (divNatNZ ((x+3)*3) 8 SIsNotZ))])
                      (Any (Not . Limited) $ [Just (divSeq (divNatNZ (x `minus` 21) 64 SIsNotZ))])))))))

-- ProofColDivSeqLvDown.idrでlvDown'を証明したからOK
postulate lvDown : (n, lv:Nat) -> P n lv -> P n (pred lv)
-- ########################################



--            from sub0xxxxx
-- ########################################
-- 01 3(6x+1) --B[1,-2]--> 3x
postulate b18x3To3x' :
  (k:Nat) -> P (S (plus (plus (plus k k) (plus k k)) (plus k k))) 1 -> P k 2

-- 02 3(18x+4) --A[6,-4]->E[2,-4]--> 3(2x)
postulate ae54x12To6x' :
  (l:Nat) -> P (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                              (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                        (S (plus (plus (plus l l) l) (plus (plus l l) l)))))) 1
    -> P (plus l l) 3

-- 03 3(18x+10) --A[6,-4]->C[4,-4]--> 3(8x+3)
postulate ac54x30To24x9' :
  (l:Nat) -> P (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                         (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))))) 1
    -> P (S (S (S (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l)))))) 3

-- 04 3(18x+16) --A[6,-4]->B[1,-2]--> 3(4x+3)
postulate ab54x30To12x9' :
  (l:Nat) -> P (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                            (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l)))))))))))) 1
    -> P (S (S (S (plus (plus l l) (plus l l))))) 3

-- 05 3(3x+2) --C[4,-4]--> 3x
postulate c9x6To3x' :
  (j:Nat) -> P (S (S (plus (plus j j) j))) 1 -> P j 2

-- 06 3(12x+3) --E[2,-4]--> 3x
postulate e36x9To3x' :
  (l:Nat) -> P (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l)))))) 1 -> P l 2

-- 07 3(36x+9) --F[5,-2]->C[4,-4]--> 3(32x+7)
postulate fc108x27To96x21' :
  (o:Nat) -> P (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))) 1
    -> P (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))) 3

-- 08 3(36x+21) --F[5,-2]->B[1,-2]--> 3(16x+9)
postulate fb108x63To48x27' :
  (o:Nat) -> P (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                           (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))) 1
    -> P (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))) 3

-- 09 3(36x+33) --F[5,-2]->E[2,-4]--> 3(8x+7)
postulate fe108x99To24x21' :
  (o:Nat) -> P (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                              (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                       (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))) 1
    -> P (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))) 3

-- 10 3(36x+6) --F[5,-2]->E[2,-4]--> 3(8x+1)
postulate fe108x18To24x3' :
  (o:Nat) ->  P (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))) 1
    -> P (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))) 3

-- 11 3(36x+18) --F[5,-2]->C[4,-4]--> 3(32x+15)
postulate fc108x54To96x45' :
  (o:Nat) -> P (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                           (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                     (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                               (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))) 1
    -> P (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))))) 3

-- 12 3(36x+30) --F[5,-2]->B[1,-2]--> 3(16x+13)
postulate fb108x90To48x39' :
  (o:Nat) -> P (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                              (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))  (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))) 1
    -> P (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))) 3

-- 13 3(36x+12) --F[5,-2]->B[1,-2]--> 3(16x+5)
postulate fb108x36To48x15' :
  (o:Nat) -> P (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                     (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))
                               (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))))))) 1
    -> P (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))) 3

-- 14 3(36x+24) --F[5,-2]->E[2,-4]--> 3(8x+5)
postulate fe108x72To24x15' :
  (o:Nat) ->  P (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                              (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))))) 1
    -> P (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))) 3

-- 15 3(36x+36) --F[5,-2]->C[4,-4]--> 3(32x+31)
postulate fc108x108To96x93' :
  (o:Nat) -> P (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                           (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                             (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                     (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                       (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))))) 1
    -> P (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o)
            (plus o o)))))))))))))))))))))))))))))))))))) 3
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- anyがFalseなら、全ての要素がFalseなので
postulate aDSFalse : (x, lv:Nat)
  -> All Limited (allDivSeq x lv
              ++ allDivSeqA x lv
              ++ allDivSeqB x lv
              ++ allDivSeqC x lv
              ++ allDivSeqD x lv
              ++ allDivSeqE x lv
              ++ allDivSeqF x lv
              ++ allDivSeqG x lv)
    -> All Limited (allDivSeq x lv)
-- ########################################



