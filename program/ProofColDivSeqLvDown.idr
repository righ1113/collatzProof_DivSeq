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
  lvDown'' n Z (Left l)                                                  = l
  lvDown'' n Z (Right (Left l))                                          = defini0 n $ Right (Left (changeA0 n l))
  lvDown'' n Z (Right (Right (Left l)))                                  = defini0 n $ (Right (Right (Left (changeB0 n l))))
  lvDown'' n Z (Right (Right (Right (Left l))))                          = defini0 n $ (Right (Right (Right (Left (changeC0 n l)))))
  lvDown'' n Z (Right (Right (Right (Right (Left l)))))                  = defini0 n $ (Right (Right (Right (Right (Left (changeD0 n l))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Left l))))))          = defini0 n $ (Right (Right (Right (Right (Right (Left (changeE0 n l)))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Right (Left l)))))))  = defini0 n $ (Right (Right (Right (Right (Right (Right (Left (changeF0 n l))))))))
  lvDown'' n Z (Right (Right (Right (Right (Right (Right (Right r))))))) = defini0 n $ (Right (Right (Right (Right (Right (Right (Right (changeG0 n r))))))))
  lvDown'' n (S lv) (Left l)                                                  = l
  lvDown'' n (S lv) (Right (Left l))                                          = defini3 n lv $ Right (Left (lvDown' (divNatNZ ((n+7)*3) 4 SIsNotZ) (S lv) (changeA n lv l)))
  lvDown'' n (S lv) (Right (Right (Left l)))                                  = defini3 n lv $ (Right (Right (Left (lvDown' (n*6+3) (S lv) (changeB n lv l)))))
  lvDown'' n (S lv) (Right (Right (Right (Left l))))                          = defini3 n lv $ (Right (Right (Right (Left (lvDown' (n*3+6) (S lv) (changeC n lv l))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Left l)))))                  = defini3 n lv $ (Right (Right (Right (Right (Left (lvDown' (divNatNZ ((n+1)*3) 2 SIsNotZ) (S lv) (changeD n lv l)))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Left l))))))          = defini3 n lv $ (Right (Right (Right (Right (Right (Left (lvDown' (n*12+9) (S lv) (changeE n lv l))))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Left l)))))))  = defini3 n lv $ (Right (Right (Right (Right (Right (Right (Left (lvDown' (divNatNZ ((n+3)*3) 8 SIsNotZ) (S lv) (changeF n lv l)))))))))
  lvDown'' n (S lv) (Right (Right (Right (Right (Right (Right (Right r))))))) = defini3 n lv $ (Right (Right (Right (Right (Right (Right (Right (lvDown' (divNatNZ (n `minus` 21) 64 SIsNotZ) (S lv) (changeG n lv r)))))))))

  -- レベルを下げる事ができる
  lvDown' : (n, lv:Nat) -> Any (Not . Limited) $ allDivSeq n lv
                        -> Any (Not . Limited) $ allDivSeq n (pred lv)
  lvDown' n Z      prf = prf
  lvDown' n (S lv) prf = lvDown'' n lv $ lvDown''' n lv prf
-- ---------------------------------



