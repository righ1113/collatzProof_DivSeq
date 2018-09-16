module ProofColDivSeqLvDown

import ProofColDivSeqBase

%default total
-- %language ElabReflection
%access export


-- レベルを下げる関数
myAny : (a->Bool) -> List a -> Bool
myAny pp [] = False
myAny pp (x :: xs) = (pp x) || myAny pp xs
-- 前提　Isabelleで証明した
postulate any1 : (pp:a->Bool) -> (xs, ys:List a)
  -> myAny pp (xs ++ ys) = myAny pp xs || myAny pp ys
-- any1 pp [] ys = Refl
-- any1 pp (x :: xs) ys ?= cong {f=(\t => pp x || t)} (any1 pp xs ys)
any3 : (b1, b2, b3:Bool) -> (b1 || b2 || b3 = True) -> Either (b1=True) (Either (b2=True) (b3=True))
any3 False False False prf = (void . uninhabited) prf
any3 False False True prf  = Right (Right Refl)
any3 False True _ prf      = Right (Left Refl)
any3 True _ _ prf          = Left Refl

-- allDivSeqの定義そのものだからOK
postulate unfold : (x, lv:Nat) -> allDivSeq x (S lv) = allDivSeq x lv
                                                            ++ (allDivSeqA x lv
                                                            ++ allDivSeqB x lv
                                                            ++ allDivSeqC x lv
                                                            ++ allDivSeqD x lv
                                                            ++ allDivSeqE x lv
                                                            ++ allDivSeqF x lv
                                                            ++ allDivSeqG x lv)
-- 前方を削っているのは、（有限or無限を判定する）末尾に影響を与えないから
postulate changeA : (x, lv:Nat) -> (myAny (\x => not (limited x)) (allDivSeqA n lv) = True)
  -> (myAny (\x => not (limited x)) (allDivSeq ((x+7)*3 `div` 4) lv) = True)
-- 前方を削っているのは、（有限or無限を判定する）末尾に影響を与えないから
postulate changeA0 : (x:Nat) -> (myAny (\x => not (limited x)) (allDivSeqA n 0) = True)
  -> (myAny (\x => not (limited x)) [Just (divSeq $ toIntegerNat ((x+7)*3 `div` 4))] = True)
postulate unfold2 : (x, lv:Nat) -> myAny (\x => not (limited x)) $ allDivSeq x lv = True
                      = Either (myAny (\x => not (limited x)) $ allDivSeq x (pred lv) = True)
                          (Either (myAny (\x => not (limited x)) $ allDivSeq ((x+7)*3 `div` 4) (pred lv) = True)
                                  (myAny (\x => not (limited x)) (allDivSeqB x (pred lv)
                                            ++ allDivSeqC x (pred lv)
                                            ++ allDivSeqD x (pred lv)
                                            ++ allDivSeqE x (pred lv)
                                            ++ allDivSeqF x (pred lv)
                                            ++ allDivSeqG x (pred lv)) = True))
postulate unfold0 : (x:Nat) -> myAny (\x => not (limited x)) $ allDivSeq x 0 = True
                      = Either (myAny (\x => not (limited x)) $ [Just (divSeq $ toIntegerNat x)] = True)
                          (Either (myAny (\x => not (limited x)) $ [Just (divSeq $ toIntegerNat ((x+7)*3 `div` 4))] = True)
                                  (myAny (\x => not (limited x)) ([Just (divSeq $ toIntegerNat (x*6+3))]
                                            ++ [Just (divSeq $ toIntegerNat (x*3+6))]
                                            ++ [Just (divSeq $ toIntegerNat ((x+1)*3 `div` 2))]
                                            ++ [Just (divSeq $ toIntegerNat (x*12+9))]
                                            ++ [Just (divSeq $ toIntegerNat ((x+3)*3 `div` 8))]
                                            ++ [Just (divSeq $ toIntegerNat ((x `minus` 21) `div` 64))]) = True))

mutual
  partial
  lvDown''' : (n, lv:Nat) -> myAny (\x => not (limited x)) $ allDivSeq n (S lv) = True
    -> Either (myAny (\x => not (limited x)) $ allDivSeq n lv = True)
              (Either (myAny (\x => not (limited x)) (allDivSeqA n lv) = True)
                      (myAny (\x => not (limited x)) (allDivSeqB n lv
                                ++ allDivSeqC n lv
                                ++ allDivSeqD n lv
                                ++ allDivSeqE n lv
                                ++ allDivSeqF n lv
                                ++ allDivSeqG n lv) = True))
  lvDown''' n lv = rewrite unfold n lv in
                  rewrite any1 (\x => not (limited x)) (allDivSeq n lv) (allDivSeqA n lv
                    ++ allDivSeqB n lv
                    ++ allDivSeqC n lv
                    ++ allDivSeqD n lv
                    ++ allDivSeqE n lv
                    ++ allDivSeqF n lv
                    ++ allDivSeqG n lv) in
                  rewrite any1 (\x => not (limited x)) (allDivSeqA n lv) (
                    allDivSeqB n lv
                    ++ allDivSeqC n lv
                    ++ allDivSeqD n lv
                    ++ allDivSeqE n lv
                    ++ allDivSeqF n lv
                    ++ allDivSeqG n lv) in
                      \y => any3 (myAny (\x => not (limited x)) (allDivSeq n lv))
                                  (myAny (\x => not (limited x)) (allDivSeqA n lv))
                                  (myAny (\x => not (limited x))
                                        (allDivSeqB n lv ++
                                          allDivSeqC n lv ++
                                          allDivSeqD n lv ++
                                          allDivSeqE n lv ++
                                          allDivSeqF n lv ++
                                          allDivSeqG n lv)) y

  partial
  lvDown'' : (n,lv:Nat) -> Either (myAny (\x => not (limited x)) $ allDivSeq n lv = True)
              (Either (myAny (\x => not (limited x)) (allDivSeqA n lv) = True)
                      (myAny (\x => not (limited x)) (allDivSeqB n lv
                                ++ allDivSeqC n lv
                                ++ allDivSeqD n lv
                                ++ allDivSeqE n lv
                                ++ allDivSeqF n lv
                                ++ allDivSeqG n lv) = True))
              -> myAny (\x => not (limited x)) $ allDivSeq n lv = True
  lvDown'' n Z (Left l) = l
  lvDown'' n Z (Right (Left l)) = let prf = changeA0 n l in
    rewrite unfold0 n in Right (Left prf)
  lvDown'' n Z (Right (Right r)) = ?lvDown_rhs_5
  lvDown'' n (S lv) (Left l)  = l
  lvDown'' n (S lv) (Right (Left l)) = let prf = changeA n (S lv) l in
    rewrite unfold2 n (S lv) in Right (Left (lvDown' ((n+7)*3 `div` 4) (S lv) prf))
  lvDown'' n (S lv) (Right (Right r)) = ?lvDown_rhs_3

  partial
  lvDown' : (n, lv:Nat) -> myAny (\x => not (limited x)) $ allDivSeq n lv = True
                        -> myAny (\x => not (limited x)) $ allDivSeq n (pred lv) = True
  lvDown' n Z prf = prf
  lvDown' n (S lv) prf = lvDown'' n lv $ lvDown''' n lv prf
-- ---------------------------------



