{-
cd collatzProof_DivSeq/program2
chcp 65001
idris
-}
module ProofColDivSeqBase

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


-- divSeqの実装に必要な関数
    -- ----- from libs/contrib/Data/CoList.idr -----
public export
codata CoList : Type -> Type where
  Nil : CoList a
  (::) : a -> CoList a -> CoList a

implementation Functor CoList where
  map f []      = []
  map f (x::xs) = f x :: map f xs

implementation Show a => Show (CoList a) where
  show xs = "[" ++ show' "" 20 xs ++ "]" where
    show' : String -> (n : Nat) -> (xs : CoList a) -> String
    show' acc Z _             = acc ++ "..."
    show' acc (S n) []        = acc
    show' acc (S n) [x]       = acc ++ show x
    show' acc (S n) (x :: xs) = show' (acc ++ (show x) ++ ", ") n xs

unfoldr : (a -> Maybe (b, a)) -> a -> CoList b
unfoldr f x =
  case f x of
    Just (y, new_x) => y :: (unfoldr f new_x)
    _               => []
    -- ----- from libs/contrib/Data/CoList.idr -----

countEven : Nat -> Nat -> Nat -> (Nat, Nat)
countEven n Z      acc = (acc, n)
countEven n (S nn) acc =
  if (modNatNZ n 2 SIsNotZ) == 1
    then (acc, n)
    else countEven (divNatNZ n 2 SIsNotZ) nn (acc+1)

-- divSeqの実装
divSeq : Nat -> CoList Integer
divSeq n = divSeq' n n
  where
    divSeq' : Nat -> Nat -> CoList Integer
    divSeq' n     Z     = []
    divSeq' Z     (S k) = []
    divSeq' (S n) (S k) with (parity n)
      divSeq' (S (S (j + j))) (S k) | Odd  = divSeq' (S j) k
      divSeq' (S (j + j)    ) (S k) | Even =
        map toIntegerNat
          (unfoldr (\b => if b <= 1 then Nothing
                                    else Just (countEven (b*3+1) (b*3+1) 0) ) (S (j + j)))
definiDivSeq0 : divSeq Z = []
definiDivSeq0 = Refl
-- ---------------------------------


-- その他関数
limitedNStep : CoList Integer -> Nat -> Bool
limitedNStep []        _     = True
limitedNStep (_ :: _)  Z     = False
limitedNStep (_ :: xs) (S n) = limitedNStep xs n
definiLimited0 : limitedNStep [] Z = True
definiLimited0 = Refl
-- ---------------------------------



