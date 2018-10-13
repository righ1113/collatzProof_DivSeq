module ProofColDivSeqPostulate

import ProofColDivSeqBase

%default total
-- %language ElabReflection
%access export


--            from ProofColDivSeqBase
-- ########################################
-- 無限降下法（の変形）　Isabelleで証明した
postulate infiniteDescent :
  ((n:Nat) -> P (S n) 2 -> (m ** (LTE (S m) (S n), P m 2)))
    -> any unLimited $ allDivSeq Z 2 = False
      -> any unLimited $ allDivSeq (n+n+n) 2 = False

-- mainの結果より、保証される
postulate base0 : any unLimited $ allDivSeq Z 2 = False
-- ########################################



--            from ProofColDivSeqLvDown
-- ########################################
-- 前提　Isabelleで証明した
postulate any1 : (pp:a->Bool) -> (xs, ys:List a)
  -> myAny pp (xs ++ ys) = myAny pp xs || myAny pp ys
-- any1 pp [] ys = Refl
-- any1 pp (x :: xs) ys ?= cong {f=(\t => pp x || t)} (any1 pp xs ys)

-- 前方を削っているのは、（有限or無限を判定する）末尾に影響を与えないから
postulate changeA : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqA n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq ((x+7)*3 `myDiv` 4) lv) = True)
postulate changeA0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqA n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq ((x+7)*3 `myDiv` 4))] = True)
postulate changeB : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqB n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq (x*6+3) lv) = True)
postulate changeB0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqB n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq (x*6+3))] = True)
postulate changeC : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqC n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq (x*3+6) lv) = True)
postulate changeC0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqC n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq (x*3+6))] = True)
postulate changeD : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqD n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq ((x+1)*3 `myDiv` 2) lv) = True)
postulate changeD0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqD n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq ((x+1)*3 `myDiv` 2))] = True)
postulate changeE : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqE n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq (x*12+9) lv) = True)
postulate changeE0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqE n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq (x*12+9))] = True)
postulate changeF : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqF n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq ((x+3)*3 `myDiv` 8) lv) = True)
postulate changeF0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqF n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq ((x+3)*3 `myDiv` 8))] = True)
postulate changeG : (x, lv:Nat) -> (myAny (\t => not (limited t)) (allDivSeqG n lv) = True)
  -> (myAny (\t => not (limited t)) (allDivSeq ((x `minus` 21) `myDiv` 64) lv) = True)
postulate changeG0 : (x:Nat) -> (myAny (\t => not (limited t)) (allDivSeqG n 0) = True)
  -> (myAny (\t => not (limited t)) [Just (divSeq ((x `minus` 21) `myDiv` 64))] = True)

postulate unfold3 : (x, lv:Nat) -> (myAny (\t => not (limited t)) $ allDivSeq x lv = True) =
  Either (myAny (\t => not (limited t)) $ allDivSeq x (pred lv) = True)
    (Either (myAny (\t => not (limited t)) $ allDivSeq ((x+7)*3 `myDiv` 4) (pred lv) = True)
      (Either (myAny (\t => not (limited t)) $ allDivSeq (x*6+3) (pred lv) = True)
        (Either (myAny (\t => not (limited t)) $ allDivSeq (x*3+6) (pred lv) = True)
          (Either (myAny (\t => not (limited t)) $ allDivSeq ((x+1)*3 `myDiv` 2) (pred lv) = True)
            (Either (myAny (\t => not (limited t)) $ allDivSeq (x*12+9) (pred lv) = True)
              (Either (myAny (\t => not (limited t)) $ allDivSeq ((x+3)*3 `myDiv` 8) (pred lv) = True)
                      (myAny (\t => not (limited t)) $ allDivSeq ((x `minus` 21) `myDiv` 64) (pred lv) = True)))))))
postulate unfold0 : (x:Nat) -> (myAny (\t => not (limited t)) $ allDivSeq x 0 = True) =
  Either (myAny (\t => not (limited t)) $ [Just (divSeq x)] = True)
    (Either (myAny (\t => not (limited t)) $ [Just (divSeq ((x+7)*3 `myDiv` 4))] = True)
      (Either (myAny (\t => not (limited t)) $ [Just (divSeq (x*6+3))] = True)
        (Either (myAny (\t => not (limited t)) $ [Just (divSeq (x*3+6))] = True)
          (Either (myAny (\t => not (limited t)) $ [Just (divSeq ((x+1)*3 `myDiv` 2))] = True)
            (Either (myAny (\t => not (limited t)) $ [Just (divSeq (x*12+9))] = True)
              (Either (myAny (\t => not (limited t)) $ [Just (divSeq ((x+3)*3 `myDiv` 8))] = True)
                      (myAny (\t => not (limited t)) $ [Just (divSeq ((x `minus` 21) `myDiv` 64))] = True)))))))

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

{--
-- 10 3(36x+9) --F[5,-2]->C[4,-4]--> 3(32x+7)
postulate fc108x27To96x21' :
  (o:Nat) ->  P (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))))))) 1
    -> P (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))) 3
--}

-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- anyがFalseなら、全ての要素がFalseなので
postulate aDSFalse : (x, lv:Nat)
  -> any unLimited (allDivSeq x lv
                ++ allDivSeqA x lv
                ++ allDivSeqB x lv
                ++ allDivSeqC x lv
                ++ allDivSeqD x lv
                ++ allDivSeqE x lv
                ++ allDivSeqF x lv
                ++ allDivSeqG x lv) = False
    -> any unLimited (allDivSeq x lv) = False
-- ########################################



