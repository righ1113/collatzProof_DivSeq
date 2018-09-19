module ProofColDivSeqLvDown

import ProofColDivSeqBase

%default total
-- %language ElabReflection


myAny : (a->Bool) -> List a -> Bool
myAny pp [] = False
myAny pp (x :: xs) = (pp x) || myAny pp xs
-- 前提　Isabelleで証明した
postulate any1 : (pp:a->Bool) -> (xs, ys:List a)
  -> myAny pp (xs ++ ys) = myAny pp xs || myAny pp ys
-- any1 pp [] ys = Refl
-- any1 pp (x :: xs) ys ?= cong {f=(\t => pp x || t)} (any1 pp xs ys)
orToEither : (b1, b2, b3, b4, b5, b6, b7, b8:Bool)
  -> (b1 || b2 || b3 || b4 || b5 || b6 || b7 || b8 = True)
    -> Either (b1=True) (Either (b2=True) (Either (b3=True) (Either (b4=True) (Either (b5=True) (Either (b6=True) (Either (b7=True) (b8=True)))))))
orToEither False False False False False False False False prf = (void . uninhabited) prf
orToEither False False False False False False False True  prf = Right (Right (Right (Right (Right (Right (Right Refl))))))
orToEither False False False False False False True  _     prf = Right (Right (Right (Right (Right (Right (Left Refl))))))
orToEither False False False False False True  _     _     prf = Right (Right (Right (Right (Right (Left Refl)))))
orToEither False False False False True  _     _     _     prf = Right (Right (Right (Right (Left Refl))))
orToEither False False False True  _     _     _     _     prf = Right (Right (Right (Left Refl)))
orToEither False False True  _     _     _     _     _     prf = Right (Right (Left Refl))
orToEither False True  _     _     _     _     _     _     prf = Right (Left Refl)
orToEither True  _     _     _     _     _     _     _     prf = Left Refl

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

mutual
  lvDown''' : (n, lv:Nat) -> myAny (\t => not (limited t)) $ allDivSeq n (S lv) = True
    -> Either (myAny (\t => not (limited t)) $ allDivSeq n lv = True)
        (Either (myAny (\t => not (limited t)) (allDivSeqA n lv) = True)
          (Either (myAny (\t => not (limited t)) (allDivSeqB n lv) = True)
            (Either (myAny (\t => not (limited t)) (allDivSeqC n lv) = True)
              (Either (myAny (\t => not (limited t)) (allDivSeqD n lv) = True)
                (Either (myAny (\t => not (limited t)) (allDivSeqE n lv) = True)
                  (Either (myAny (\t => not (limited t)) (allDivSeqF n lv) = True)
                          (myAny (\t => not (limited t)) (allDivSeqG n lv) = True)))))))
  lvDown''' n lv = rewrite unfold n lv in
                    rewrite any1 (\t => not (limited t)) (allDivSeq n lv) (
                      allDivSeqA n lv
                      ++ allDivSeqB n lv
                      ++ allDivSeqC n lv
                      ++ allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 (\t => not (limited t)) (allDivSeqA n lv) (
                      allDivSeqB n lv
                      ++ allDivSeqC n lv
                      ++ allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 (\t => not (limited t)) (allDivSeqB n lv) (
                      allDivSeqC n lv
                      ++ allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 (\t => not (limited t)) (allDivSeqC n lv) (
                      allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 (\t => not (limited t)) (allDivSeqD n lv) (
                      allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 (\t => not (limited t)) (allDivSeqE n lv) (
                      allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 (\t => not (limited t)) (allDivSeqF n lv) (
                      allDivSeqG n lv) in
                      \y => orToEither  (myAny (\t => not (limited t)) (allDivSeq n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqA n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqB n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqC n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqD n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqE n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqF n lv))
                                        (myAny (\t => not (limited t)) (allDivSeqG n lv))
                                        y

  lvDown'' : (n,lv:Nat)
    -> Either (myAny (\t => not (limited t)) $ allDivSeq n lv = True)
        (Either (myAny (\t => not (limited t)) (allDivSeqA n lv) = True)
          (Either (myAny (\t => not (limited t)) (allDivSeqB n lv) = True)
            (Either (myAny (\t => not (limited t)) (allDivSeqC n lv) = True)
              (Either (myAny (\t => not (limited t)) (allDivSeqD n lv) = True)
                (Either (myAny (\t => not (limited t)) (allDivSeqE n lv) = True)
                  (Either (myAny (\t => not (limited t)) (allDivSeqF n lv) = True)
                          (myAny (\t => not (limited t)) (allDivSeqG n lv) = True)))))))
      -> myAny (\t => not (limited t)) $ allDivSeq n lv = True
  lvDown'' n Z (Left l) = l
  lvDown'' n Z (Right (Left l)) = let prf = changeA0 n l in
    rewrite unfold0 n in Right (Left prf)
  lvDown'' n Z (Right (Right (Left l))) = let prf = changeB0 n l in
    rewrite unfold0 n in (Right (Right (Left prf)))
  lvDown'' n Z (Right (Right (Right (Left l)))) = let prf = changeC0 n l in
    rewrite unfold0 n in (Right (Right (Right (Left prf))))
  lvDown'' n Z (Right (Right (Right (Right (Left l))))) = let prf = changeD0 n l in
    rewrite unfold0 n in (Right (Right (Right (Right (Left prf)))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Left l)))))) = let prf = changeE0 n l in
    rewrite unfold0 n in (Right (Right (Right (Right (Right (Left prf))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Right (Left l))))))) = let prf = changeF0 n l in
    rewrite unfold0 n in (Right (Right (Right (Right (Right (Right (Left prf)))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Right (Right r))))))) = let prf = changeG0 n r in
    rewrite unfold0 n in (Right (Right (Right (Right (Right (Right (Right prf)))))))
  lvDown'' n (S lv) (Left l)  = l
  lvDown'' n (S lv) (Right (Left l)) = let prf = changeA n (S lv) l in
    rewrite unfold3 n (S lv) in Right (Left (lvDown' ((n+7)*3 `myDiv` 4) (S lv) prf))
  lvDown'' n (S lv) (Right (Right (Left l))) = let prf = changeB n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Left (lvDown' (n*6+3) (S lv) prf))))
  lvDown'' n (S lv) (Right (Right (Right (Left l)))) = let prf = changeC n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Left (lvDown' (n*3+6) (S lv) prf)))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Left l))))) = let prf = changeD n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Left (lvDown' ((n+1)*3 `myDiv` 2) (S lv) prf))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Left l)))))) = let prf = changeE n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Right (Left (lvDown' (n*12+9) (S lv) prf)))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Left l))))))) = let prf = changeF n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Right (Right (Left (lvDown' ((n+3)*3 `myDiv` 8) (S lv) prf))))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Right r))))))) = let prf = changeG n (S lv) r in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Right (Right (Right (lvDown' ((n `minus` 21) `myDiv` 64) (S lv) prf))))))))

  -- レベルを下げる事ができる
  lvDown' : (n, lv:Nat) -> myAny (\t => not (limited t)) $ allDivSeq n lv = True
                        -> myAny (\t => not (limited t)) $ allDivSeq n (pred lv) = True
  lvDown' n Z      prf = prf
  lvDown' n (S lv) prf = lvDown'' n lv $ lvDown''' n lv prf
-- ---------------------------------



