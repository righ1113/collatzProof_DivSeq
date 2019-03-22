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
any2Sub : {pp : a -> Type} -> (x : a) -> (xs, ys : List a)
  -> Either (Any pp xs) (Any pp ys) -> Either (Any pp (x :: xs)) (Any pp ys)
any2Sub x []       ys (Left anL)  = absurd anL
any2Sub x (x2::xs) ys (Left anL)  = Left (There anL)
any2Sub x xs       ys (Right anR) = Right anR

-- これが肝
any2 : {pp : a -> Type} -> (xs, ys : List a)
  -> Any pp (xs ++ ys) -> Either (Any pp xs) (Any pp ys)
any2 []      ys an         = Right an
any2 (x::xs) ys (Here he)  = Left (Here he)
any2 (x::xs) ys (There th) =
  let foo = any2 xs ys th in any2Sub x xs ys foo

any3 : {pp : a -> Type} -> (xs1, xs2, xs3 : List a)
  -> Either (Any pp xs1) (Any pp (xs2++xs3))
    -> Either (Any pp xs1) (Either (Any pp xs2) (Any pp xs3))
any3 xs1 xs2 xs3 (Left prfL)  = Left prfL
any3 xs1 xs2 xs3 (Right prfR) = Right (any2 xs2 xs3 prfR)

any4 : {pp : a -> Type} -> (xs1, xs2, xs3, xs4 : List a)
  -> Either (Any pp xs1) (Either (Any pp xs2) (Any pp (xs3++xs4)))
    -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Any pp xs4)))
any4 xs1 xs2 xs3 xs4 (Left prfL)           = Left prfL
any4 xs1 xs2 xs3 xs4 (Right (Left prfRL))  = Right (Left prfRL)
any4 xs1 xs2 xs3 xs4 (Right (Right prfRR)) = Right (Right (any2 xs3 xs4 prfRR))

any5 : {pp : a -> Type} -> (xs1, xs2, xs3, xs4, xs5 : List a)
  -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Any pp (xs4++xs5))))
    -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Any pp xs5))))
any5 xs1 xs2 xs3 xs4 xs5 (Left prfL)                    = Left prfL
any5 xs1 xs2 xs3 xs4 xs5 (Right (Left prfRL))           = Right (Left prfRL)
any5 xs1 xs2 xs3 xs4 xs5 (Right (Right (Left prfRRL)))  = Right (Right (Left prfRRL))
any5 xs1 xs2 xs3 xs4 xs5 (Right (Right (Right prfRRR))) = Right (Right (Right (any2 xs4 xs5 prfRRR)))

any6 : {pp : a -> Type} -> (xs1, xs2, xs3, xs4, xs5, xs6 : List a)
  -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Any pp (xs5++xs6)))))
    -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Either (Any pp xs5) (Any pp xs6)))))
any6 xs1 xs2 xs3 xs4 xs5 xs6 (Left prfL)                             = Left prfL
any6 xs1 xs2 xs3 xs4 xs5 xs6 (Right (Left prfRL))                    = Right (Left prfRL)
any6 xs1 xs2 xs3 xs4 xs5 xs6 (Right (Right (Left prfRRL)))           = Right (Right (Left prfRRL))
any6 xs1 xs2 xs3 xs4 xs5 xs6 (Right (Right (Right (Left prfRRRL))))  = Right (Right (Right (Left prfRRRL)))
any6 xs1 xs2 xs3 xs4 xs5 xs6 (Right (Right (Right (Right prfRRRR)))) = Right (Right (Right (Right (any2 xs5 xs6 prfRRRR))))

any7 : {pp : a -> Type} -> (xs1, xs2, xs3, xs4, xs5, xs6, xs7 : List a)
  -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Either (Any pp xs5) (Any pp (xs6++xs7))))))
    -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Either (Any pp xs5) (Either (Any pp xs6) (Any pp xs7))))))
any7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 (Left prfL)                                      = Left prfL
any7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 (Right (Left prfRL))                             = Right (Left prfRL)
any7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 (Right (Right (Left prfRRL)))                    = Right (Right (Left prfRRL))
any7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 (Right (Right (Right (Left prfRRRL))))           = Right (Right (Right (Left prfRRRL)))
any7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 (Right (Right (Right (Right (Left prfRRRRL)))))  = Right (Right (Right (Right (Left prfRRRRL))))
any7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 (Right (Right (Right (Right (Right prfRRRRR))))) = Right (Right (Right (Right (Right (any2 xs6 xs7 prfRRRRR)))))

any8 : {pp : a -> Type} -> (xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8 : List a)
  -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Either (Any pp xs5) (Either (Any pp xs6) (Any pp (xs7++xs8)))))))
    -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Either (Any pp xs5) (Either (Any pp xs6) (Either (Any pp xs7) (Any pp xs8)))))))
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Left prfL)                                               = Left prfL
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Right (Left prfRL))                                      = Right (Left prfRL)
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Right (Right (Left prfRRL)))                             = Right (Right (Left prfRRL))
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Right (Right (Right (Left prfRRRL))))                    = Right (Right (Right (Left prfRRRL)))
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Right (Right (Right (Right (Left prfRRRRL)))))           = Right (Right (Right (Right (Left prfRRRRL))))
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Right (Right (Right (Right (Right (Left prfRRRRRL))))))  = Right (Right (Right (Right (Right (Left prfRRRRRL)))))
any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Right (Right (Right (Right (Right (Right prfRRRRRR)))))) = Right (Right (Right (Right (Right (Right (any2 xs7 xs8 prfRRRRRR))))))

anyFinal : {pp : a -> Type} -> (xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8 : List a)
  -> Any pp (xs1 ++ xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6 ++ xs7 ++ xs8)
    -> Either (Any pp xs1) (Either (Any pp xs2) (Either (Any pp xs3) (Either (Any pp xs4) (Either (Any pp xs5) (Either (Any pp xs6) (Either (Any pp xs7) (Any pp xs8)))))))
anyFinal xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 prf =
  let prf2 = any2 xs1 (xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6 ++ xs7 ++ xs8) prf in
  let prf3 = any3 xs1 xs2 (xs3 ++ xs4 ++ xs5 ++ xs6 ++ xs7 ++ xs8) prf2 in
  let prf4 = any4 xs1 xs2 xs3 (xs4 ++ xs5 ++ xs6 ++ xs7 ++ xs8) prf3 in
  let prf5 = any5 xs1 xs2 xs3 xs4 (xs5 ++ xs6 ++ xs7 ++ xs8) prf4 in
  let prf6 = any6 xs1 xs2 xs3 xs4 xs5 (xs6 ++ xs7 ++ xs8) prf5 in
  let prf7 = any7 xs1 xs2 xs3 xs4 xs5 xs6 (xs7 ++ xs8) prf6 in
  let prf8 = any8 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 prf7 in prf8

-- 前方を削っているのは、（有限or無限を判定する）末尾に影響を与えないから
postulate changeA : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqA n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ ((x+7)*3) 4 SIsNotZ) (S lv)))
postulate changeA0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqA n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ ((x+7)*3) 4 SIsNotZ))])
postulate changeB : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqB n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (x*6+3) (S lv)))
postulate changeB0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqB n 0))
  -> (Any (Not . Limited) [Just (divSeq (x*6+3))])
postulate changeC : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqC n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (x*3+6) (S lv)))
postulate changeC0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqC n 0))
  -> (Any (Not . Limited) [Just (divSeq (x*3+6))])
postulate changeD : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqD n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ ((x+1)*3) 2 SIsNotZ) (S lv)))
postulate changeD0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqD n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ ((x+1)*3) 2 SIsNotZ))])
postulate changeE : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqE n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (x*12+9) (S lv)))
postulate changeE0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqE n 0))
  -> (Any (Not . Limited) [Just (divSeq (x*12+9))])
postulate changeF : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqF n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ ((x+3)*3) 8 SIsNotZ) (S lv)))
postulate changeF0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqF n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ ((x+3)*3) 8 SIsNotZ))])
postulate changeG : (x, lv:Nat) -> (Any (Not . Limited) (allDivSeqG n (S lv)))
  -> (Any (Not . Limited) (allDivSeq (divNatNZ (x `minus` 21) 64 SIsNotZ) (S lv)))
postulate changeG0 : (x:Nat) -> (Any (Not . Limited) (allDivSeqG n 0))
  -> (Any (Not . Limited) [Just (divSeq (divNatNZ (x `minus` 21) 64 SIsNotZ))])

postulate unfold3 : (x, lv:Nat) -> (Any (Not . Limited) $ allDivSeq x (S lv)) =
  Either (Any (Not . Limited) $ allDivSeq x lv)
    (Either (Any (Not . Limited) $ allDivSeq (divNatNZ ((x+7)*3) 4 SIsNotZ) lv)
      (Either (Any (Not . Limited) $ allDivSeq (x*6+3) lv)
        (Either (Any (Not . Limited) $ allDivSeq (x*3+6) lv)
          (Either (Any (Not . Limited) $ allDivSeq (divNatNZ ((x+1)*3) 2 SIsNotZ) lv)
            (Either (Any (Not . Limited) $ allDivSeq (x*12+9) lv)
              (Either (Any (Not . Limited) $ allDivSeq (divNatNZ ((x+3)*3) 8 SIsNotZ) lv)
                      (Any (Not . Limited) $ allDivSeq (divNatNZ (x `minus` 21) 64 SIsNotZ) lv)))))))
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
all2Sub : {pp : a -> Type} -> (xs, ys : List a)
  -> All pp ((x::xs) ++ ys) -> (pp x, All pp (xs ++ ys))
all2Sub xs ys (Cons p ps) = (p, ps)

-- これが肝
all2 : {pp : a -> Type} -> (xs, ys : List a)
  -> All pp (xs ++ ys) -> All pp xs
all2 []      ys _   = NilA
all2 (x::xs) ys prf = let (prf2, prf3) = all2Sub xs ys prf in
  Cons prf2 (all2 xs ys prf3)
-- ########################################



