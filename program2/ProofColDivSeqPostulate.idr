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
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- ########################################



--            from sub0xxxxx
-- ########################################
namespace s
  public export
  BoxFC : List Nat
  BoxFC = [7, 15, 0, 31]
  public export
  BoxFB : List Nat
  BoxFB = [5, 9, 13]
  public export
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
-- ########################################



