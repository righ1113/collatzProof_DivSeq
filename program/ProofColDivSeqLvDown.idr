module ProofColDivSeqLvDown

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total
-- %language ElabReflection


mutual
  lvDown''' : (n, lv:Nat) -> Any (Not . Limited) (allDivSeq n (S lv))
    -> Either (Any (Not . Limited) (allDivSeq n lv))
        (Either (Any (Not . Limited) (allDivSeqA n lv))
          (Either (Any (Not . Limited) (allDivSeqB n lv))
            (Either (Any (Not . Limited) (allDivSeqC n lv))
              (Either (Any (Not . Limited) (allDivSeqD n lv))
                (Either (Any (Not . Limited) (allDivSeqE n lv))
                  (Either (Any (Not . Limited) (allDivSeqF n lv))
                          (Any (Not . Limited) (allDivSeqG n lv)) ))))))
  lvDown''' n lv = rewrite defini n lv in
    \prf => anyFinal (allDivSeq n lv)
                     (allDivSeqA n lv)
                     (allDivSeqB n lv)
                     (allDivSeqC n lv)
                     (allDivSeqD n lv)
                     (allDivSeqE n lv)
                     (allDivSeqF n lv)
                     (allDivSeqG n lv) prf

  lvDown'' : (n,lv:Nat)
    -> Either (Any (Not . Limited) (allDivSeq n lv))
        (Either (Any (Not . Limited) (allDivSeqA n lv))
          (Either (Any (Not . Limited) (allDivSeqB n lv))
            (Either (Any (Not . Limited) (allDivSeqC n lv))
              (Either (Any (Not . Limited) (allDivSeqD n lv))
                (Either (Any (Not . Limited) (allDivSeqE n lv))
                  (Either (Any (Not . Limited) (allDivSeqF n lv))
                          (Any (Not . Limited) (allDivSeqG n lv)) ))))))
      -> Any (Not . Limited) (allDivSeq n lv)
  lvDown'' n Z (Left l) = l
  lvDown'' n Z (Right (Left l)) = let prf = changeA0 n l in
    rewrite defini0 n in Right (Left prf)
  lvDown'' n Z (Right (Right (Left l))) = let prf = changeB0 n l in
    rewrite defini0 n in (Right (Right (Left prf)))
  lvDown'' n Z (Right (Right (Right (Left l)))) = let prf = changeC0 n l in
    rewrite defini0 n in (Right (Right (Right (Left prf))))
  lvDown'' n Z (Right (Right (Right (Right (Left l))))) = let prf = changeD0 n l in
    rewrite defini0 n in (Right (Right (Right (Right (Left prf)))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Left l)))))) = let prf = changeE0 n l in
    rewrite defini0 n in (Right (Right (Right (Right (Right (Left prf))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Right (Left l))))))) = let prf = changeF0 n l in
    rewrite defini0 n in (Right (Right (Right (Right (Right (Right (Left prf)))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Right (Right r))))))) = let prf = changeG0 n r in
    rewrite defini0 n in (Right (Right (Right (Right (Right (Right (Right prf)))))))
  lvDown'' n (S lv) (Left l) = l
  lvDown'' n (S lv) (Right (Left l)) = let prf = changeA n lv l in
    rewrite defini3 n lv in Right (Left (lvDown' (divNatNZ ((n+7)*3) 4 SIsNotZ) (S lv) prf))
  lvDown'' n (S lv) (Right (Right (Left l))) = let prf = changeB n lv l in
    rewrite defini3 n lv in (Right (Right (Left (lvDown' (n*6+3) (S lv) prf))))
  lvDown'' n (S lv) (Right (Right (Right (Left l)))) = let prf = changeC n lv l in
    rewrite defini3 n lv in (Right (Right (Right (Left (lvDown' (n*3+6) (S lv) prf)))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Left l))))) = let prf = changeD n lv l in
    rewrite defini3 n lv in (Right (Right (Right (Right (Left (lvDown' (divNatNZ ((n+1)*3) 2 SIsNotZ) (S lv) prf))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Left l)))))) = let prf = changeE n lv l in
    rewrite defini3 n lv in (Right (Right (Right (Right (Right (Left (lvDown' (n*12+9) (S lv) prf)))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Left l))))))) = let prf = changeF n lv l in
    rewrite defini3 n lv in (Right (Right (Right (Right (Right (Right (Left (lvDown' (divNatNZ ((n+3)*3) 8 SIsNotZ) (S lv) prf))))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Right r))))))) = let prf = changeG n lv r in
    rewrite defini3 n lv in (Right (Right (Right (Right (Right (Right (Right (lvDown' (divNatNZ (n `minus` 21) 64 SIsNotZ) (S lv) prf))))))))

  -- レベルを下げる事ができる
  lvDown' : (n, lv:Nat) -> Any (Not . Limited) $ allDivSeq n lv
                        -> Any (Not . Limited) $ allDivSeq n (pred lv)
  lvDown' n Z      prf = prf
  lvDown' n (S lv) prf = lvDown'' n lv $ lvDown''' n lv prf
-- ---------------------------------



