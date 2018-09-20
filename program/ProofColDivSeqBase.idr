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

divHelp : Nat -> Nat -> Nat -> Nat
divHelp Z     Z     c = 1
divHelp Z     (S y) c = 0
divHelp (S x) Z     c = 1 + divHelp x c c
divHelp (S x) (S y) c = divHelp x y c
myDiv : Nat -> Nat -> Nat
myDiv _     Z     = 0
myDiv Z     (S y) = 0
myDiv (S x) (S y) = divHelp (S x) (S y) y
myMod : Nat -> Nat -> Nat
myMod x y =
  if x < y then x else x `minus` (y * (myDiv x y))

collatz : Nat -> Nat
collatz Z = Z
collatz (S Z) = (S Z)
collatz (S (S k)) = let n = (S (S k)) in
  if (n `myMod` 2) == 0 then n `myDiv` 2 else 3 * n + 1

col : Nat -> List Nat
col n = takeWhileSt (>1) 150 (iterate collatz n) ++ [1]

divSeq' : List Nat -> Nat -> List Nat -> List Nat
divSeq' _       Z       acc = acc
divSeq' []      (S cnt) acc = acc
divSeq' [S Z]   (S cnt) acc = acc
divSeq' (x::xs) (S cnt) acc = let even = \x=> (myMod x 2) == 0 in
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
  allDivSeq x Z = if (x `myMod` 2) == 0 then [Nothing]
    else [Just (divSeq x)]
      ++ (if ((x+7) `myMod` 4) == 0 && (((x+7) `myMod` 4) `myMod` 2) == 1 then [[6,-4] `dsp` (Just (divSeq ((x+7)*3 `myDiv` 4)))] else [])
      ++ (if ((x*6+3) `myMod` 2) == 1 then [[1,-2] `dsp` (Just (divSeq (x*6+3)))] else [])
      ++ (if ((x*3+6) `myMod` 2) == 1 then [[4,-4] `dsp` (Just (divSeq (x*3+6)))] else [])
      ++ (if ((x+1) `myMod` 2) == 0 && (((x+1) `myMod` 2) `myMod` 2) == 1 then [[3,-2] `dsp` (Just (divSeq ((x+1)*3 `myDiv` 2)))] else [])
      ++ (if ((x*12+9) `myMod` 2) == 1 then [[2,-4] `dsp` (Just (divSeq (x*12+9)))] else [])
      ++ (if ((x+3) `myMod` 8) == 0 && (((x+3) `myMod` 8) `myMod` 2) == 1 then [[5,-2] `dsp` (Just (divSeq ((x+3)*3 `myDiv` 8)))] else [])
      ++ (if ((x `minus` 21) `myMod` 64) == 0 && x > 21 && (((x `minus` 21) `myMod` 64) `myMod` 2) == 1 then [[6] `dsp2` (Just (divSeq ((x `minus` 21) `myDiv` 64)))] else [])
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
    if ((x+7) `myMod` 4) == 0 && (((x+7) `myMod` 4) `myMod` 2) == 1
      then [[6,-4] `dsp` (Just (divSeq ((x+7)*3 `myDiv` 4)))]
      else []
  allDivSeqA x (S lv) =
    if ((x+7) `myMod` 4) == 0
      then map ([6,-4] `dsp`) $ allDivSeq ((x+7)*3 `myDiv` 4) (S lv)
      else []

  allDivSeqB : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqB x Z =
    if ((x*6+3) `myMod` 2) == 1
      then [[1,-2] `dsp` (Just (divSeq (x*6+3)))]
      else []
  allDivSeqB x (S lv) =
      map ([1,-2] `dsp`) $ allDivSeq (x*6+3) (S lv)

  allDivSeqC : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqC x Z =
    if ((x*3+6) `myMod` 2) == 1
      then [[4,-4] `dsp` (Just (divSeq (x*3+6)))]
      else []
  allDivSeqC x (S lv) =
      map ([4,-4] `dsp`) $ allDivSeq (x*3+6) (S lv)

  allDivSeqD : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqD x Z =
    if ((x+1) `myMod` 2) == 0 && (((x+1) `myMod` 2) `myMod` 2) == 1
      then [[3,-2] `dsp` (Just (divSeq ((x+1)*3 `myDiv` 2)))]
      else []
  allDivSeqD x (S lv) =
    if ((x+1) `myMod` 2) == 0
      then map ([3,-2] `dsp`) $ allDivSeq ((x+1)*3 `myDiv` 2) (S lv)
      else []

  allDivSeqE : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqE x Z =
    if ((x*12+9) `myMod` 2) == 1
      then [[2,-4] `dsp` (Just (divSeq (x*12+9)))]
      else []
  allDivSeqE x (S lv) =
      map ([2,-4] `dsp`) $ allDivSeq (x*12+9) (S lv)

  allDivSeqF : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqF x Z =
    if ((x+3) `myMod` 8) == 0 && (((x+3) `myMod` 8) `myMod` 2) == 1
      then [[5,-2] `dsp` (Just (divSeq ((x+3)*3 `myDiv` 8)))]
      else []
  allDivSeqF x (S lv) =
    if ((x+3) `myMod` 8) == 0
      then map ([5,-2] `dsp`) $ allDivSeq ((x+3)*3 `myDiv` 8) (S lv)
      else []

  allDivSeqG : Nat -> Nat -> List (Maybe (List Integer))
  allDivSeqG x Z =
    if ((x `minus` 21) `myMod` 64) == 0 && x > 21 && (((x `minus` 21) `myMod` 64) `myMod` 2) == 1
      then [[6] `dsp2` (Just (divSeq ((x `minus` 21) `myDiv` 64)))]
      else []
  allDivSeqG x (S lv) =
    if ((x `minus` 21) `myMod` 64) == 0 && x > 21
      then map ([6] `dsp2`) $ allDivSeq ((x `minus` 21) `myDiv` 64) (S lv)
      else []
-- ---------------------------------


-- 無限降下法
limited : Maybe (List Integer) -> Bool
limited Nothing          = True
limited (Just [])        = True
limited (Just (x :: xs)) = let l = last (x::xs) in True
unLimited : Maybe (List Integer) -> Bool
unLimited = not . limited

P : Nat -> Nat -> Type
P n lv = any unLimited $ allDivSeq (n+n+n) lv = True

-- 無限降下法（の変形）　Isabelleで証明した
postulate infiniteDescent : ((n:Nat) -> P (S n) 2 -> (m ** (LTE (S m) (S n), P m 2)))
            -> any unLimited $ allDivSeq Z 2 = False
              -> any unLimited $ allDivSeq n 2 = False

-- mainの結果より、保証される
postulate base0 : any unLimited $ allDivSeq 0 2 = False

unfold : (x, lv:Nat) -> allDivSeq x (S lv) = allDivSeq x lv
                                          ++ allDivSeqA x lv
                                          ++ allDivSeqB x lv
                                          ++ allDivSeqC x lv
                                          ++ allDivSeqD x lv
                                          ++ allDivSeqE x lv
                                          ++ allDivSeqF x lv
                                          ++ allDivSeqG x lv
unfold x lv = Refl

-- ProofColDivSeqLvDown.idrでlvDown'を証明したからOK
postulate lvDown : (n, lv:Nat) -> P n lv -> P n (pred lv)
-- ---------------------------------










-- allDivSeq 0 2が有限項である事を示すため、mainを使う（ビルドして）
main : IO ()
main = traverse_ (putStrLn . show) $ allDivSeq 0 2

