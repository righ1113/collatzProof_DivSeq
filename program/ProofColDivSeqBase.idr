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

takeWhileSt : (a -> Bool) -> Nat -> Stream a -> List a
takeWhileSt p Z       (x :: xs) = []
takeWhileSt p (S cnt) (x :: xs) = if p x then x :: takeWhileSt p cnt xs else []

collatz : Nat -> Nat
collatz Z = Z
collatz (S Z) = (S Z)
collatz (S (S k)) = let n = (S (S k)) in
  if (modNatNZ n 2 SIsNotZ) == 0 then divNatNZ n 2 SIsNotZ else 3 * n + 1

col : Nat -> List Nat
col n = takeWhileSt (>1) 150 (iterate collatz n) ++ [1]

divSeq' : List Nat -> Nat -> List Nat -> List Nat
divSeq' _       Z       acc = acc
divSeq' []      (S cnt) acc = acc
divSeq' [S Z]   (S cnt) acc = acc
divSeq' (x::xs) (S cnt) acc = let even = \x=> (modNatNZ x 2 SIsNotZ) == 0 in
                              let coll1 = length $ takeWhile even xs in
                              let coll2 = dropWhile even xs in
  divSeq' coll2 cnt (acc ++ [coll1])

-- odd only!
divSeq : Nat -> List Integer
divSeq x = let xs = col x in
  map toIntegerNat $ divSeq' xs (length xs) []
-- ---------------------------------


-- allDivSeqの実装
mutual
  allDivSeq : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeq x Z = if (modNatNZ x 2 SIsNotZ) == 0 then [Nothing]
    else [Just (divSeq x)]
      ++ (if (modNatNZ (x+7) 4 SIsNotZ) == 0 && (modNatNZ (modNatNZ (x+7) 4 SIsNotZ) 2 SIsNotZ) == 1 then [[6,-4] `dsp` (Just (divSeq (divNatNZ ((x+7)*3) 4 SIsNotZ)))] else [])
      ++ (if (modNatNZ (x*6+3) 2 SIsNotZ) == 1 then [[1,-2] `dsp` (Just (divSeq (x*6+3)))] else [])
      ++ (if (modNatNZ (x*3+6) 2 SIsNotZ) == 1 then [[4,-4] `dsp` (Just (divSeq (x*3+6)))] else [])
      ++ (if (modNatNZ (x+1) 2 SIsNotZ) == 0 && (modNatNZ (modNatNZ (x+1) 2 SIsNotZ) 2 SIsNotZ) == 1 then [[3,-2] `dsp` (Just (divSeq (divNatNZ ((x+1)*3) 2 SIsNotZ)))] else [])
      ++ (if (modNatNZ (x*12+9) 2 SIsNotZ) == 1 then [[2,-4] `dsp` (Just (divSeq (x*12+9)))] else [])
      ++ (if (modNatNZ (x+3) 8 SIsNotZ) == 0 && (modNatNZ (modNatNZ (x+3) 8 SIsNotZ) 2 SIsNotZ) == 1 then [[5,-2] `dsp` (Just (divSeq (divNatNZ ((x+3)*3) 8 SIsNotZ)))] else [])
      ++ (if (modNatNZ (x `minus` 21) 64 SIsNotZ) == 0 && x > 21 && (modNatNZ (modNatNZ (x `minus` 21) 64 SIsNotZ) 2 SIsNotZ) == 1 then [[6] `dsp2` (Just (divSeq (divNatNZ (x `minus` 21) 64 SIsNotZ)))] else [])
  allDivSeq x (S lv) = allDivSeq x lv
                    ++ allDivSeqA x lv
                    ++ allDivSeqB x lv
                    ++ allDivSeqC x lv
                    ++ allDivSeqD x lv
                    ++ allDivSeqE x lv
                    ++ allDivSeqF x lv
                    ++ allDivSeqG x lv

  allDivSeqA : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqA x Z =
    if (modNatNZ (x+7) 4 SIsNotZ) == 0 && (modNatNZ (modNatNZ (x+7) 4 SIsNotZ) 2 SIsNotZ) == 1
      then [[6,-4] `dsp` (Just (divSeq (divNatNZ ((x+7)*3) 4 SIsNotZ)))]
      else []
  allDivSeqA x (S lv) =
    if (modNatNZ (x+7) 4 SIsNotZ) == 0
      then map ([6,-4] `dsp`) $ allDivSeq (divNatNZ ((x+7)*3) 4 SIsNotZ) (S lv)
      else []

  allDivSeqB : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqB x Z =
    if (modNatNZ (x*6+3) 2 SIsNotZ) == 1
      then [[1,-2] `dsp` (Just (divSeq (x*6+3)))]
      else []
  allDivSeqB x (S lv) =
      map ([1,-2] `dsp`) $ allDivSeq (x*6+3) (S lv)

  allDivSeqC : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqC x Z =
    if (modNatNZ (x*3+6) 2 SIsNotZ) == 1
      then [[4,-4] `dsp` (Just (divSeq (x*3+6)))]
      else []
  allDivSeqC x (S lv) =
      map ([4,-4] `dsp`) $ allDivSeq (x*3+6) (S lv)

  allDivSeqD : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqD x Z =
    if (modNatNZ (x+1) 2 SIsNotZ) == 0 && (modNatNZ (modNatNZ (x+1) 2 SIsNotZ) 2 SIsNotZ) == 1
      then [[3,-2] `dsp` (Just (divSeq (divNatNZ ((x+1)*3) 2 SIsNotZ)))]
      else []
  allDivSeqD x (S lv) =
    if (modNatNZ (x+1) 2 SIsNotZ) == 0
      then map ([3,-2] `dsp`) $ allDivSeq (divNatNZ ((x+1)*3) 2 SIsNotZ) (S lv)
      else []

  allDivSeqE : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqE x Z =
    if (modNatNZ (x*12+9) 2 SIsNotZ) == 1
      then [[2,-4] `dsp` (Just (divSeq (x*12+9)))]
      else []
  allDivSeqE x (S lv) =
      map ([2,-4] `dsp`) $ allDivSeq (x*12+9) (S lv)

  allDivSeqF : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqF x Z =
    if (modNatNZ (x+3) 8 SIsNotZ) == 0 && (modNatNZ (modNatNZ (x+3) 8 SIsNotZ) 2 SIsNotZ) == 1
      then [[5,-2] `dsp` (Just (divSeq (divNatNZ ((x+3)*3) 8 SIsNotZ)))]
      else []
  allDivSeqF x (S lv) =
    if (modNatNZ (x+3) 8 SIsNotZ) == 0
      then map ([5,-2] `dsp`) $ allDivSeq (divNatNZ ((x+3)*3) 8 SIsNotZ) (S lv)
      else []

  allDivSeqG : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqG x Z =
    if (modNatNZ (x `minus` 21) 64 SIsNotZ) == 0 && x > 21 && (modNatNZ (modNatNZ (x `minus` 21) 64 SIsNotZ) 2 SIsNotZ) == 1
      then [[6] `dsp2` (Just (divSeq (divNatNZ (x `minus` 21) 64 SIsNotZ)))]
      else []
  allDivSeqG x (S lv) =
    if (modNatNZ (x `minus` 21) 64 SIsNotZ) == 0 && x > 21
      then map ([6] `dsp2`) $ allDivSeq (divNatNZ (x `minus` 21) 64 SIsNotZ) (S lv)
      else []
-- ---------------------------------


-- その他関数
limited : Maybe (List Integer) -> Bool
limited Nothing          = True
limited (Just [])        = True
limited (Just (x :: xs)) = let l = last (x::xs) in True
unLimited : Maybe (List Integer) -> Bool
unLimited = not . limited

P : Nat -> Nat -> Type
P n lv = any unLimited $ allDivSeq (n+n+n) lv = True

unfold : (x, lv:Nat) -> allDivSeq x (S lv) = allDivSeq x lv
                                          ++ allDivSeqA x lv
                                          ++ allDivSeqB x lv
                                          ++ allDivSeqC x lv
                                          ++ allDivSeqD x lv
                                          ++ allDivSeqE x lv
                                          ++ allDivSeqF x lv
                                          ++ allDivSeqG x lv
unfold x lv = Refl

myAny : (a->Bool) -> List a -> Bool
myAny pp [] = False
myAny pp (x :: xs) = (pp x) || myAny pp xs
-- ---------------------------------










-- allDivSeq 0 2が有限項である事を示すため、mainを使う（ビルドして）
main : IO ()
main = traverse_ (putStrLn . show) $ allDivSeq 0 2

