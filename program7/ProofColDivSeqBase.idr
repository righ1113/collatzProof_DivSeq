module ProofColDivSeqBase

%default total
%access export


-- ----- from libs/contrib/Data/CoList.idr -----
public export
codata CoList : Type -> Type where
  Nil  : CoList a
  (::) : a -> CoList a -> CoList a

implementation Functor CoList where
  map f []        = []
  map f (x :: xs) = f x :: map f xs

implementation Show a => Show (CoList a) where
  show xs = "[" ++ show' "" 20 xs ++ "]" where
    show' : String -> (n : Nat) -> (xs : CoList a) -> String
    show' acc Z     _         = acc ++ "..."
    show' acc (S n) []        = acc
    show' acc (S n) [x]       = acc ++ show x
    show' acc (S n) (x :: xs) = show' (acc ++ (show x) ++ ", ") n xs

unfoldr : (a -> Maybe (b, a)) -> a -> CoList b
unfoldr f x =
  case f x of
    Just (y, new_x) => y :: (unfoldr f new_x)
    _               => []
-- ----- from libs/contrib/Data/CoList.idr -----


-- ----- from libs/contrib/Data/Nat/DivMod/IteratedSubtraction.idr -----
public export
data LT' : (n, m : Nat) -> Type where
  ||| n < 1 + n
  LTSucc : LT' n (S n)
  ||| n < m implies that n < m + 1
  LTStep : LT' n m -> LT' n (S m)

||| Nothing is strictly less than zero
implementation Uninhabited (LT' n 0) where
  uninhabited LTSucc impossible

||| Zero is less than any non-zero number.
LTZeroLeast : LT' Z (S n)
LTZeroLeast {n = Z}   = LTSucc
LTZeroLeast {n = S n} = LTStep LTZeroLeast

||| If n < m, then 1 + n < 1 + m
ltSuccSucc : LT' n m -> LT' (S n) (S m)
ltSuccSucc LTSucc      = LTSucc
ltSuccSucc (LTStep lt) = LTStep $ ltSuccSucc lt

||| If n + 1 < m, then n < m
lteToLt' : LTE (S n) m -> LT' n m
lteToLt' {n = Z}   (LTESucc x) = LTZeroLeast
lteToLt' {n = S k} (LTESucc x) = ltSuccSucc $ lteToLt' x

implementation WellFounded LT' where
  wellFounded x = Access (acc x)
    where
      ||| Show accessibility by induction on the structure of the LT' witness
      acc : (x, y : Nat) -> LT' y x -> Accessible LT' y
      -- Zero is vacuously accessible: there's nothing smaller to check
      acc Z     y lt = absurd lt
      -- If the element being accessed is one smaller, we're done
      acc (S y) y LTSucc = Access (acc y)
      -- If the element is more than one smaller, we need to go further
      acc (S k) y (LTStep smaller) = acc k y smaller
-- ----- from libs/contrib/Data/Nat/DivMod/IteratedSubtraction.idr -----


-- ---------------------------------
-- mod2
public export
data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd  : Parity (S (n + n))
helpEven : (j : Nat) -> Parity (S j + S j) -> Parity (S (S (plus j j)))
helpEven j p = rewrite plusSuccRightSucc j j in p
helpOdd : (j : Nat) -> Parity (S (S (j + S j))) -> Parity (S (S (S (j + j))))
helpOdd j p = rewrite plusSuccRightSucc j j in p
parity : (n : Nat) -> Parity n
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
helpThreeZero : (j : Nat) -> (plus (plus (S j) (S j)) (S j)) = S (S (S (plus (plus j j) j)))
helpThreeZero j = rewrite sym $ plusSuccRightSucc j j in
                  rewrite sym $ plusSuccRightSucc (plus j j) j in Refl
helpThreeOne : (j : Nat) -> S (plus (plus (S j) (S j)) (S j)) = S (S (S (S (plus (plus j j) j))))
helpThreeOne j = cong {f=S} $ helpThreeZero j
helpThreeTwo : (j : Nat) -> S (S (plus (plus (S j) (S j)) (S j))) = S (S (S (S (S (plus (plus j j) j)))))
helpThreeTwo j = cong {f=S} $ helpThreeOne j
mod3 : (n : Nat) -> Mod3 n
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


-- ---------------------------------
dsp : List Integer -> CoList Integer -> CoList Integer
dsp _                      []        = []
dsp []                    (y :: ys) = y  :: ys
dsp (x :: [])             (y :: ys) = y  :: ys
dsp (x1 :: x2 :: [])      (y :: ys) = x1 :: (x2 + y) :: ys
dsp (x1 :: x2 :: x3 :: _) (y :: ys) = x1 :: x2       :: (x3 + y) :: ys

countEven : Nat -> Nat -> Nat -> (Nat, Nat)
countEven n Z      acc = (acc, n)
countEven n (S nn) acc =
  if (modNatNZ n 2 SIsNotZ) == 1
    then (acc, n)
    else countEven (divNatNZ n 2 SIsNotZ) nn (acc+1)

-- divSeqの実装
divSeq : Nat -> CoList Integer
divSeq n = divSeq' (S (S (S (n+n+n+n+n+n)))) (S (S (S (n+n+n+n+n+n)))) where
  divSeq' : Nat -> Nat -> CoList Integer
  divSeq' n     Z     = []
  divSeq' Z     (S k) = []
  divSeq' (S n) (S k) with (parity n)
    divSeq' (S (S (j + j))) (S k) | Odd  = divSeq' (S j) k --実際はここへは来ない
    divSeq' (S (j + j))     (S k) | Even =
      map toIntegerNat
        (unfoldr (\b => if b <= 1 then Nothing
                                  else Just (countEven (b*3+1) (b*3+1) 0) ) (S (j + j)))

{-
72t+45  E[2,-4] y=x/12-3/4  6t+3        12x+7
*8.                    <---------------------
108t+99=6(18t+16)+3 EF[2,1,-2] y=2x/9-1 24t+21=6(4t+3)+3         4x+4+2t
*6.
108t+27=6(18t+4)+3  CF[4,1,-2] y=8x/9-3  96t+21=6(16t+3)+3       x+1+2t
*5.
216t+225=6(36t+37)+3  FE[5,0,-4] y=2x/9-5  48t+45=6(8t+7)+3      4x+9+4t
*14.
108t+111=6(18t+18)+3  FB[5,-1,-2] y=4x/9-13/3  48t+45=6(8t+7)+3  2x+11+2t

0
1+w
  1+2v
    1+2(2u)             2. 9. 11.  4. 13.
    1+2(1+2u)
      3+4(2t)
        3+8(2s)         2. 9. 11.  8.  6.
        3+8(1+2s)       2. 9. 11.  8.
      3+4(1+2t)         2. 9. 11.  5. 14.
  1+1+2v
    1+1+2(2u)           2. 9. 11.  3. 12.
    1+1+2(1+2u)
      4+4(2t)           2. 9. 11.  3. 12.  7.
      4+4(1+2t)         2. 9. 11.  3. 12.
-}
-- この部分の実装は、コンストラクタIsFirstLimited01~14の正当性を補強している
allDivSeq : Nat -> List (CoList Integer)
allDivSeq Z     = [[1, 4], [2, -4] `dsp` [3,2,3,4], [3, 0, -4] `dsp` [2,3,1,1,5,4], [4, -4] `dsp` [1,1,1,5,4], [1, -2] `dsp` [6], [3, -1, -2] `dsp` [1,1,2,1,4,1,3,1,2,3,4]] -- 6*<0>+3 = 3
allDivSeq (S w) with (parity w)
  allDivSeq (S (v + v))     | Even with (parity v)
    allDivSeq (S ((u + u) + (u + u)))         | Even | Even
      = let x = (S ((u + u) + (u + u)))
        in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [6, -2, -4] `dsp` divSeq (9*x+16), [6, -3, -2] `dsp` divSeq (4*x+2*u+8)]
    allDivSeq (S ((S (u + u)) + (S (u + u)))) | Even | Odd  with (parity u)
      allDivSeq (S ((S ((t + t) + (t + t))) + (S ((t + t) + (t + t)))))                 | Even | Odd  | Even with (parity t)
        allDivSeq (S ((S (((s + s) + (s + s)) + ((s + s) + (s + s)))) + (S (((s + s) + (s + s)) + ((s + s) + (s + s))))))                                 | Even | Odd  | Even | Even
          = let x = (S ((S (((s + s) + (s + s)) + ((s + s) + (s + s)))) + (S (((s + s) + (s + s)) + ((s + s) + (s + s))))))
            in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [2, 1, -2] `dsp` divSeq (4*x+8*s+4), [4, 1, -2] `dsp` divSeq (x+2*s+1)]
        allDivSeq (S ((S (((S (s + s)) + (S (s + s))) + ((S (s + s)) + (S (s + s))))) + (S (((S (s + s)) + (S (s + s))) + ((S (s + s)) + (S (s + s))))))) | Even | Odd  | Even | Odd
          = let x = (S ((S (((S (s + s)) + (S (s + s))) + ((S (s + s)) + (S (s + s))))) + (S (((S (s + s)) + (S (s + s))) + ((S (s + s)) + (S (s + s)))))))
            in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [2, 1, -2] `dsp` divSeq (4*x+8*s+4)]
      allDivSeq (S ((S ((S (t + t)) + (S (t + t)))) + (S ((S (t + t)) + (S (t + t)))))) | Even | Odd  | Odd
        = let x = (S ((S ((S (t + t)) + (S (t + t)))) + (S ((S (t + t)) + (S (t + t))))))
          in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [5, 0, -4] `dsp` divSeq (4*x+4*t+9), [5, -1, -2] `dsp` divSeq (2*x+2*t+11)]
  allDivSeq (S (S (v + v))) | Odd  with (parity v)
    allDivSeq (S (S ((u + u) + (u + u))))         | Odd  | Even
      = let x = (S (S ((u + u) + (u + u))))
        in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [3, 0, -4] `dsp` divSeq (18*x+13), [3, -1, -2] `dsp` divSeq (9*x+6)]
    allDivSeq (S (S ((S (u + u)) + (S (u + u))))) | Odd  | Odd with (parity u)
      allDivSeq (S (S ((S ((t + t) + (t + t))) + (S ((t + t) + (t + t))))))                 | Odd  | Odd | Even
        = let x = (S (S ((S ((t + t) + (t + t))) + (S ((t + t) + (t + t))))))
          in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [3, 0, -4] `dsp` divSeq (18*x+13), [3, -1, -2] `dsp` divSeq (9*x+6), [1, 3, -2] `dsp` divSeq (2*x+2*t+2)]
      allDivSeq (S (S ((S ((S (t + t)) + (S (t + t)))) + (S ((S (t + t)) + (S (t + t))))))) | Odd  | Odd | Odd
        = let x = (S (S ((S ((S (t + t)) + (S (t + t)))) + (S ((S (t + t)) + (S (t + t)))))))
          in [divSeq x, [2, -4] `dsp` divSeq (12*x+7), [4, -4] `dsp` divSeq (3*x+2), [1, -2] `dsp` divSeq (6*x+3), [3, 0, -4] `dsp` divSeq (18*x+13), [3, -1, -2] `dsp` divSeq (9*x+6)]
-- ---------------------------------


limitedNStep : CoList a -> Nat -> Bool
limitedNStep []        _     = True
limitedNStep (_ :: _)  Z     = False
limitedNStep (_ :: xs) (S n) = limitedNStep xs n
data Limited : CoList a -> Type where
  IsLimited : (n : Nat ** limitedNStep xs n = True) -> Limited xs
-- ---------------------------------
mutual
  public export
  data FirstLimited : Nat -> Type where
    -- 先頭の割数列が有限長なら FirstLimited
    MakeFirstLimited : (n : Nat) -> Limited ((the (List (CoList Integer) -> CoList Integer) head) (ProofColDivSeqBase.allDivSeq n))
      -> FirstLimited n
    IsFirstLimited01    : FirstLimited 1 -- 6*<1>+3 = 9
    IsFirstLimited02    : (l : Nat)
      -> AllLimited l
        -> FirstLimited (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))
    IsFirstLimited02_2    : (l : Nat)
      -> AllLimited l
        -> FirstLimited (S (S (S (S (((l+l)+(l+l)) + ((l+l)+(l+l)) + ((l+l)+(l+l)))))))
    IsFirstLimited03    : (m : Nat)
      -> AllLimited (m+m)
        -> FirstLimited (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))
    IsFirstLimited04    : (m : Nat)
      -> AllLimited (S ((m+m)+(m+m)))
        -> FirstLimited (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))
    IsFirstLimited05    : (m : Nat)
      -> AllLimited (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))
        -> FirstLimited (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m)))))))))
    IsFirstLimited06    : (l : Nat)
      -> AllLimited (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))
        -> FirstLimited (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))
    IsFirstLimited07    : (l : Nat)
      -> AllLimited (S (S (S (S (l+l+l+l)+(l+l+l+l)))))
        -> FirstLimited (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))
    IsFirstLimited08    : (l : Nat)
      -> AllLimited (S (S (S ((l+l)+(l+l)))))
        -> FirstLimited (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l)))))))
    IsFirstLimited09    : (j : Nat)
      -> AllLimited j
        -> FirstLimited (S (S (plus (plus j j) j)))
    IsFirstLimited10    : FirstLimited 0 -- 6*<0>+3 = 3
    IsFirstLimited11    : (k : Nat)
      -> AllLimited k
        -> FirstLimited (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))
    IsFirstLimited12    : (l : Nat)
      -> AllLimited (l+l)
        -> FirstLimited (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))
    IsFirstLimited13    : (l : Nat)
      -> AllLimited (S ((l+l)+(l+l)))
        -> FirstLimited (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))
    IsFirstLimited14    : (l : Nat)
      -> AllLimited (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))
        -> FirstLimited (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l)))))))))


  public export
  data AllLimited : Nat -> Type where
    -- 割数列が全て有限長なら AllLimited
    MakeAllLimited : (n : Nat) -> (the (List Type -> Type) head) (map Limited (ProofColDivSeqBase.allDivSeq n))
      -> AllLimited n
    -- このコンストラクタの正当性は、拙作 "divseq2" より保証される
    IsFtoA : (z : Nat) -> FirstLimited z -> AllLimited z
  --Uninhabited (AllLimited xs) where --使わなかった
  --  uninhabited a impossible
  --allToVoid : (x : Nat) -> Not $ AllLimited (allDivSeq (S x))
  --allToVoid x prf impossible
-- ---------------------------------



