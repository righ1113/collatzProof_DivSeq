module ProofColDivSeqPostulate

import ProofColDivSeqBase

%default total
-- %language ElabReflection
%access export

%hide Language.Reflection.P

--            from ProofColDivSeqBase
-- ########################################
-- 無限降下法（の変形） Isabelleで証明した
postulate infiniteDescent0 :
  ((n:Nat) -> (Not . P) (S n) -> (m ** (LTE (S m) (S n), (Not . P) m)))
    -> P Z
      -> P n

base0 : P Z
base0 = rewrite definiP Z in
        rewrite definiDivSeq0 in IsLimited (Z ** definiLimited0)
-- ########################################



--            from ProofColDivSeqLvDown
-- ########################################
any2Sub : {pp : a -> Type} -> (x : a) -> (xs, ys : List a)
  -> Either (Any pp xs) (Any pp ys) -> Either (Any pp (x :: xs)) (Any pp ys)
any2Sub x []       ys (Left anL)  = absurd anL
any2Sub x (x2::xs) ys (Left anL)  = Left (There anL)
any2Sub x xs       ys (Right anR) = Right anR
-- これが肝
any2 : {pp : a -> Type} -> (xs, ys : List a)
  -> Any pp (xs ++ ys) -> Either (Any pp xs) (Any pp ys)
any2 []      ys an         = Right an
any2 (x::xs) ys (Here he)  = Left (Here he)
any2 (x::xs) ys (There th) =
  let foo = any2 xs ys th in any2Sub x xs ys foo
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
all2Sub : {pp : a -> Type} -> (xs, ys : List a)
  -> All pp ((x::xs) ++ ys) -> (pp x, All pp (xs ++ ys))
all2Sub xs ys (Cons p ps) = (p, ps)

-- これが肝
all2 : {pp : a -> Type} -> (xs, ys : List a)
  -> All pp (xs ++ ys) -> All pp xs
all2 []      ys _   = NilA
all2 (x::xs) ys prf =
  let (prf2, prf3) = all2Sub xs ys prf
  in Cons prf2 (all2 xs ys prf3)
postulate all3 : {pp : a -> Type} -> (xs, ys : List a)
  -> All pp (xs ++ ys) -> All pp ys
-- ########################################



--            from sub0xxxxx
-- ########################################
namespace s
  BoxFC : List Nat
  BoxFC = [7, 15, 0, 31]
  BoxFB : List Nat
  BoxFB = [5, 9, 13]
  BoxFE : List Nat
  BoxFE = [1, 5, 7]
postulate mapFC : (t, y, x : Nat) ->
  (Not . P) (y + (S (S (S (S x))))) = (Not . P) ((fromMaybe 0 (index' y s.BoxFC)) + (plus (plus (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t))) (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t))))
                                                                                          (plus (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t))) (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t))))))
postulate mapFB : (t, x, y, z, w, u : Nat) ->
  (Not . P) (x + (S (S (S (S (S (plus (plus (plus (plus (plus (plus t t) t) (y + (plus (plus t t) t)))
                                                  z)
                                            w)
                                      u))))))) = (Not . P) ((fromMaybe 0 (index' y s.BoxFB)) + (plus (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t))) (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t)))))
postulate mapFE : (t, x, y, z, w, u : Nat) ->
  (Not . P) (x + (S (S (S (S (plus (plus (plus (plus (plus (plus t t) t) (y + (plus (plus t t) t)))
                                               z)
                                         w)
                                   u)))))) = (Not . P) ((fromMaybe 0 (index' y s.BoxFE)) + (plus (plus (plus t t) (plus t t)) (plus (plus t t) (plus t t))))


-- 01 3(6x+1) --B[1,-2]--> 3x
postulate b18x3To3x :
  (k:Nat) -> (Not . P) (S (plus (plus (plus k k) (plus k k)) (plus k k))) -> (Not . P) k

-- 02 3(18x+4) --A[6,-4]--> 3(24x+3) -->E[2,-4]--> 3(2x)
postulate ae54x12To6x :
  (l:Nat) -> (Not . P) (S (S (plus (plus (plus (plus (plus l l) l) (plus (plus l l) l))
                              (S (plus (plus (plus l l) l) (plus (plus l l) l))))
                        (S (plus (plus (plus l l) l) (plus (plus l l) l))))))
    -> (Not . P) (plus l l)

-- 03 3(18x+10) --A[6,-4]->C[4,-4]--> 3(8x+3)
postulate ac54x30To24x9 :
  (l:Nat) -> (Not . P) (S (S (S (plus (plus (plus (plus (plus l l) l) (S (plus (plus l l) l))) (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l))))))
                         (S (S (plus (plus (plus l l) l) (S (plus (plus l l) l)))))))))
    -> (Not . P) (S (S (S (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))))))

-- 04 3(18x+16) --A[6,-4]->B[1,-2]--> 3(4x+3)
postulate ab54x30To12x9 :
  (l:Nat) -> (Not . P) (S (S (S (S (plus (plus (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))
                                  (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))
                            (S (S (S (plus (plus (plus l l) l) (S (S (plus (plus l l) l))))))))))))
    -> (Not . P) (S (S (S (plus (plus l l) (plus l l)))))

-- 05 3(3x+2) --C[4,-4]--> 3x
postulate c9x6To3x :
  (j:Nat) -> (Not . P) (S (S (plus (plus j j) j))) -> (Not . P) j

-- 06 3(12x+3) --E[2,-4]--> 3x
postulate e36x9To3x :
  (l:Nat) -> (Not . P) (S (S (S (plus (plus (plus (plus l l) (plus l l)) (plus (plus l l) (plus l l))) (plus (plus l l) (plus l l))))))
    -> (Not . P) l

-- 07 3(36x+9) --F[5,-2]->C[4,-4]--> 3(32x+7)
fc108x27To96x21 :
  (o:Nat) -> (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                             (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                       (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                                 (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                    (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))
fc108x27To96x21 o =
  rewrite mapFC o 0 (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                      (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                          (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))) in id

-- 08 3(36x+21) --F[5,-2]->B[1,-2]--> 3(16x+9)
fb108x63To48x27 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))
fb108x63To48x27 o =
  rewrite mapFB o 0 1 (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                      (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                      (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))) in id

-- 09 3(36x+33) --F[5,-2]->E[2,-4]--> 3(8x+7)
fe108x99To24x21 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))
fe108x99To24x21 o =
  rewrite mapFE o 2 2 (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))) in id

-- 10 3(36x+6) --F[5,-2]->E[2,-4]--> 3(8x+1)
fe108x18To24x3 :
  (o:Nat) ->  (Not . P) (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                        (plus (plus (plus o o) o) (plus (plus o o) o)))
                                  (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))
                            (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))))))))
    -> (Not . P) (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
fe108x18To24x3 o =
  rewrite mapFE o 0 0 (plus (plus (plus o o) o) (plus (plus o o) o))
                      (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o))))
                      (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (plus (plus (plus o o) o) (plus (plus o o) o)))) in id

-- 11 3(36x+18) --F[5,-2]->C[4,-4]--> 3(32x+15)
fc108x54To96x45 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                                (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                                    (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))
fc108x54To96x45 o =
  rewrite mapFC o 1 (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                      (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                                (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))
                          (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))) in id

-- 12 3(36x+30) --F[5,-2]->B[1,-2]--> 3(16x+13)
fb108x90To48x39 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                   (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))
                                             (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))
                                       (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))))))))))
fb108x90To48x39 o =
  rewrite mapFB o 1 2 (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))) in id

-- 13 3(36x+12) --F[5,-2]->B[1,-2]--> 3(16x+5)
fb108x36To48x15 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (plus (plus o o) o))
                                                (S (plus (plus (plus o o) o) (plus (plus o o) o))))
                                          (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))))
                                    (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))))))))
    -> (Not . P) (S (S (S (S (S (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o)))))))))
fb108x36To48x15 o =
  rewrite mapFB o 0 0 (S (plus (plus (plus o o) o) (plus (plus o o) o)))
                      (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o))))))
                      (S (S (plus (plus (plus (plus o o) o) (plus (plus o o) o)) (S (plus (plus (plus o o) o) (plus (plus o o) o)))))) in id

-- 14 3(36x+24) --F[5,-2]->E[2,-4]--> 3(8x+5)
fe108x72To24x15 :
  (o:Nat) ->  (Not . P) (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (plus (plus o o) o)))
                                              (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))
                                        (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))
                                  (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))))))))))
    -> (Not . P) (S (S (S (S (S (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))
fe108x72To24x15 o =
  rewrite mapFE o 2 1 (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o)))))))))
                      (S (S (S (plus (plus (plus (plus o o) o) (S (plus (plus o o) o))) (S (S (plus (plus (plus o o) o) (S (plus (plus o o) o))))))))) in id

-- 15 3(36x+36) --F[5,-2]->C[4,-4]--> 3(32x+31)
fc108x108To96x93 :
  (o:Nat) -> (Not . P) (S (S (S (S (S (S (S (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                                (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))))))))))
    -> (Not . P) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))
                                                                                                            (plus (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))) (plus (plus (plus o o) (plus o o)) (plus (plus o o) (plus o o))))))))))))))))))))))))))))))))))))
fc108x108To96x93 o =
  rewrite mapFC o 3 (plus (plus (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))
                                      (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))
                                (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))))))))))))
                          (S (S (S (S (plus (plus (plus (plus o o) o) (S (S (plus (plus o o) o)))) (S (S (S (plus (plus (plus o o) o) (S (S (plus (plus o o) o))))))))))))) in id
-- ########################################



