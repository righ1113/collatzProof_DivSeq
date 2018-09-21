module ProofColDivSeqLvDown

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


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



