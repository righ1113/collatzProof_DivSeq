module ProofColDivSeqLvDown

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


orToEither : (b1, b2, b3, b4, b5, b6, b7, b8:Bool)
  -> (b1 || b2 || b3 || b4 || b5 || b6 || b7 || b8 = True)
    -> Either (b1=True) (Either (b2=True) (Either (b3=True) (Either (b4=True) (Either (b5=True) (Either (b6=True) (Either (b7=True) (b8=True)))))))
orToEither False False False False False False False False prf = absurd prf
orToEither False False False False False False False True  prf = Right (Right (Right (Right (Right (Right (Right Refl))))))
orToEither False False False False False False True  _     prf = Right (Right (Right (Right (Right (Right (Left Refl))))))
orToEither False False False False False True  _     _     prf = Right (Right (Right (Right (Right (Left Refl)))))
orToEither False False False False True  _     _     _     prf = Right (Right (Right (Right (Left Refl))))
orToEither False False False True  _     _     _     _     prf = Right (Right (Right (Left Refl)))
orToEither False False True  _     _     _     _     _     prf = Right (Right (Left Refl))
orToEither False True  _     _     _     _     _     _     prf = Right (Left Refl)
orToEither True  _     _     _     _     _     _     _     prf = Left Refl


mutual
  lvDown''' : (n, lv:Nat) -> myAny p.unLimited $ allDivSeq n (S lv) = True
    -> Either (myAny p.unLimited $ allDivSeq n lv = True)
        (Either (myAny p.unLimited (allDivSeqA n lv) = True)
          (Either (myAny p.unLimited (allDivSeqB n lv) = True)
            (Either (myAny p.unLimited (allDivSeqC n lv) = True)
              (Either (myAny p.unLimited (allDivSeqD n lv) = True)
                (Either (myAny p.unLimited (allDivSeqE n lv) = True)
                  (Either (myAny p.unLimited (allDivSeqF n lv) = True)
                          (myAny p.unLimited (allDivSeqG n lv) = True)))))))
  lvDown''' n lv = rewrite unfold n lv in
                    rewrite any1 p.unLimited (allDivSeq n lv) (
                      allDivSeqA n lv
                      ++ allDivSeqB n lv
                      ++ allDivSeqC n lv
                      ++ allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 p.unLimited (allDivSeqA n lv) (
                      allDivSeqB n lv
                      ++ allDivSeqC n lv
                      ++ allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 p.unLimited (allDivSeqB n lv) (
                      allDivSeqC n lv
                      ++ allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 p.unLimited (allDivSeqC n lv) (
                      allDivSeqD n lv
                      ++ allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 p.unLimited (allDivSeqD n lv) (
                      allDivSeqE n lv
                      ++ allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 p.unLimited (allDivSeqE n lv) (
                      allDivSeqF n lv
                      ++ allDivSeqG n lv) in
                    rewrite any1 p.unLimited (allDivSeqF n lv) (
                      allDivSeqG n lv) in
                      \y => orToEither  (myAny p.unLimited (allDivSeq n lv))
                                        (myAny p.unLimited (allDivSeqA n lv))
                                        (myAny p.unLimited (allDivSeqB n lv))
                                        (myAny p.unLimited (allDivSeqC n lv))
                                        (myAny p.unLimited (allDivSeqD n lv))
                                        (myAny p.unLimited (allDivSeqE n lv))
                                        (myAny p.unLimited (allDivSeqF n lv))
                                        (myAny p.unLimited (allDivSeqG n lv))
                                        y

  lvDown'' : (n,lv:Nat)
    -> Either (myAny p.unLimited $ allDivSeq n lv = True)
        (Either (myAny p.unLimited (allDivSeqA n lv) = True)
          (Either (myAny p.unLimited (allDivSeqB n lv) = True)
            (Either (myAny p.unLimited (allDivSeqC n lv) = True)
              (Either (myAny p.unLimited (allDivSeqD n lv) = True)
                (Either (myAny p.unLimited (allDivSeqE n lv) = True)
                  (Either (myAny p.unLimited (allDivSeqF n lv) = True)
                          (myAny p.unLimited (allDivSeqG n lv) = True)))))))
      -> myAny p.unLimited $ allDivSeq n lv = True
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
  lvDown'' n (S lv) (Left l) = l
  lvDown'' n (S lv) (Right (Left l)) = let prf = changeA n (S lv) l in
    rewrite unfold3 n (S lv) in Right (Left (lvDown' (divNatNZ ((n+7)*3) 4 SIsNotZ) (S lv) prf))
  lvDown'' n (S lv) (Right (Right (Left l))) = let prf = changeB n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Left (lvDown' (n*6+3) (S lv) prf))))
  lvDown'' n (S lv) (Right (Right (Right (Left l)))) = let prf = changeC n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Left (lvDown' (n*3+6) (S lv) prf)))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Left l))))) = let prf = changeD n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Left (lvDown' (divNatNZ ((n+1)*3) 2 SIsNotZ) (S lv) prf))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Left l)))))) = let prf = changeE n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Right (Left (lvDown' (n*12+9) (S lv) prf)))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Left l))))))) = let prf = changeF n (S lv) l in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Right (Right (Left (lvDown' (divNatNZ ((n+3)*3) 8 SIsNotZ) (S lv) prf))))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Right r))))))) = let prf = changeG n (S lv) r in
    rewrite unfold3 n (S lv) in (Right (Right (Right (Right (Right (Right (Right (lvDown' (divNatNZ (n `minus` 21) 64 SIsNotZ) (S lv) prf))))))))

  -- レベルを下げる事ができる
  lvDown' : (n, lv:Nat) -> myAny p.unLimited $ allDivSeq n lv = True
                        -> myAny p.unLimited $ allDivSeq n (pred lv) = True
  lvDown' n Z      prf = prf
  lvDown' n (S lv) prf = lvDown'' n lv $ lvDown''' n lv prf
-- ---------------------------------



