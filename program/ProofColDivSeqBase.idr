module ProofColDivSeqBase
-- module Main -- ビルドするときはこっち　> idris ProofColDivSeqBase.idr -o run

%default total
-- %language ElabReflection
%access export


-- mod2
public export
data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd  : Parity (S (n + n))
helpEven : (j : Nat) -> Parity (S j + S j) -> Parity (S (S (plus j j)))
helpEven j p = rewrite plusSuccRightSucc j j in p
helpOdd : (j : Nat) -> Parity (S (S (j + S j))) -> Parity (S (S (S (j + j))))
helpOdd j p = rewrite plusSuccRightSucc j j in p
parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even = helpEven j (Even {n = S j})
  parity (S (S (S (j + j)))) | Odd  = helpOdd j (Odd {n = S j})

-- mod3
public export
data Mod3 : Nat -> Type where
  ThreeZero : Mod3 (n + n + n)
  ThreeOne  : Mod3 (S (n + n + n))
  ThreeTwo  : Mod3 (S (S (n + n + n)))
helpThreeZero : (j:Nat) -> (plus (plus (S j) (S j)) (S j)) = S (S (S (plus (plus j j) j)))
helpThreeZero j = rewrite sym $ plusSuccRightSucc j j in
                  rewrite sym $ plusSuccRightSucc (plus j j) j in Refl
helpThreeOne : (j:Nat) -> S (plus (plus (S j) (S j)) (S j)) = S (S (S (S (plus (plus j j) j))))
helpThreeOne j = cong {f=S} $ helpThreeZero j
helpThreeTwo : (j:Nat) -> S (S (plus (plus (S j) (S j)) (S j))) = S (S (S (S (S (plus (plus j j) j)))))
helpThreeTwo j = cong {f=S} $ helpThreeOne j
mod3 : (n:Nat) -> Mod3 n
mod3 Z         = ThreeZero {n=Z}
mod3 (S Z)     = ThreeOne {n=Z}
mod3 (S (S Z)) = ThreeTwo {n=Z}
mod3 (S (S (S k))) with (mod3 k)
  mod3 (S (S (S (j + j + j))))         | ThreeZero =
    rewrite sym $ helpThreeZero j in ThreeZero {n=S j}
  mod3 (S (S (S (S (j + j + j)))))     | ThreeOne =
    rewrite sym $ helpThreeOne j in ThreeOne {n=S j}
  mod3 (S (S (S (S (S (j + j + j)))))) | ThreeTwo =
    rewrite sym $ helpThreeTwo j in ThreeTwo {n=S j}
-- ---------------------------------


-- allDivSeqの実装に必要な関数
dsp : List Integer -> Maybe (List Integer) -> Maybe (List Integer)
dsp xs                 Nothing          = Nothing
dsp xs                 (Just [])        = Nothing
dsp []                 (Just (y :: ys)) = Nothing
dsp (x :: [])          (Just (y :: ys)) = Nothing
dsp (x1 :: (x2 :: xs)) (Just (y :: ys)) = Just (x1 :: (x2+y) :: ys)

dsp2 : List Integer -> Maybe (List Integer) -> Maybe (List Integer)
dsp2 xs        Nothing          = Nothing
dsp2 xs        (Just [])        = Nothing
dsp2 []        (Just (y :: ys)) = Nothing
dsp2 (x :: xs) (Just (y :: ys)) = Just ((x+y)::ys)

partial
takeWhileSt : (a -> Bool) -> Stream a -> List a
takeWhileSt p (x :: xs) = if p x then x :: takeWhileSt p xs else []
partial
collatz : Integer -> Integer
collatz 0 = 0
collatz 1 = 1
collatz n = if n `mod` 2 == 0 then n `div` 2 else 3 * n + 1
partial
col : Integer -> List Integer
col n = takeWhileSt (>1) (iterate collatz n) ++ [1]
myTail : List Integer -> List Integer -> List Integer
myTail xs []        = xs
myTail xs (x :: ys) = ys
partial
divSeq' : List Integer -> List Integer -> List Integer
divSeq' [1] acc = acc
divSeq' coll acc = let even = \x=> mod x 2 == 0 in
                   let coll1 = toIntegerNat $ length $ takeWhile even $ myTail [] coll in
                   let coll2 = dropWhile even $ myTail [] coll in
  divSeq' coll2 (acc ++ [coll1])
-- odd only!
partial
divSeq : Integer -> List Integer
divSeq x = divSeq' (col x) []
-- ---------------------------------


-- allDivSeqの実装
mutual
  partial
  allDivSeq : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeq x Z = if x `mod` 2 == 0 then [Nothing]
                    else [Just (divSeq $ toIntegerNat x)]
                      ++ [Just (divSeq $ toIntegerNat ((x+7)*3 `div` 4))]
                      ++ [Just (divSeq $ toIntegerNat (x*6+3))]
                      ++ [Just (divSeq $ toIntegerNat (x*3+6))]
                      ++ [Just (divSeq $ toIntegerNat ((x+1)*3 `div` 2))]
                      ++ [Just (divSeq $ toIntegerNat (x*12+9))]
                      ++ [Just (divSeq $ toIntegerNat ((x+3)*3 `div` 8))]
                      ++ [Just (divSeq $ toIntegerNat ((x `minus` 21) `div` 64))]
  allDivSeq x (S lv) = allDivSeq x lv
                ++ (allDivSeqA x lv
                ++ allDivSeqB x lv
                ++ allDivSeqC x lv
                ++ allDivSeqD x lv
                ++ allDivSeqE x lv
                ++ allDivSeqF x lv
                ++ allDivSeqG x lv)
  partial
  allDivSeqA : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqA x Z =
    if (x+7) `mod` 4 == 0
      then [[6,-4] `dsp` (Just (divSeq $ toIntegerNat ((x+7)*3 `div` 4)))]
      else []
  allDivSeqA x (S lv) =
    if (x+7) `mod` 4 == 0
      then map ([6,-4] `dsp`) $ allDivSeq ((x+7)*3 `div` 4) (S lv)
      else []
  partial
  allDivSeqB : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqB x lv =
      map ([1,-2] `dsp`) $ allDivSeq (x*6+3) lv
  partial
  allDivSeqC : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqC x lv =
      map ([4,-4] `dsp`) $ allDivSeq (x*3+6) lv
  partial
  allDivSeqD : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqD x lv =
    if (x+1) `mod` 2 == 0
      then map ([3,-2] `dsp`) $ allDivSeq ((x+1)*3 `div` 2) lv
      else []
  partial
  allDivSeqE : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqE x lv =
      map ([2,-4] `dsp`) $ allDivSeq (x*12+9) lv
  partial
  allDivSeqF : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqF x lv =
    if (x+3) `mod` 8 == 0
      then map ([5,-2] `dsp`) $ allDivSeq ((x+3)*3 `div` 8) lv
      else []
  partial
  allDivSeqG : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqG x lv =
    if (x `minus` 21) `mod` 64 == 0 && x > 21
      then map ([6] `dsp2`) $ allDivSeq ((x `minus` 21) `div` 64) lv
      else []
-- ---------------------------------


-- 無限降下法
limited : Maybe (List Integer) -> Bool
limited Nothing          = True
limited (Just [])        = True
limited (Just (x :: xs)) = let l = last (x::xs) in True
unLimited : Maybe (List Integer) -> Bool
unLimited = not . limited

partial
P : Nat -> Nat -> Type
P n lv = any unLimited $ allDivSeq n lv = True

-- 無限降下法（の変形）　Isabelleで証明した
postulate infiniteDescent : ((n:Nat) -> P (S n) 2 -> (m ** (LTE (S m) (S n), P m 2)))
            -> any unLimited $ allDivSeq Z 2 = False
              -> any unLimited $ allDivSeq n 2 = False

-- mainの結果より、保証される
postulate base0 : any unLimited $ allDivSeq 0 2 = False

-- ProofColDivSeqLvDown.idrでlvDown'を証明したからOK
postulate lvDown : (n, lv:Nat) -> P n lv -> P n (pred lv)
-- ---------------------------------










-- allDivSeq 0 2が有限項である事を示すため、mainを使う（ビルドして）
partial
main : IO ()
main = print $ allDivSeq 0 2
