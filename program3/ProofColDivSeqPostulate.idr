module ProofColDivSeqPostulate

import ProofColDivSeqBase

%default total
%access export


--            from ProofColDivSeqBase
-- ########################################
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- 排中律
--postulate lem : {P : Nat -> Type} -> (x : Nat) -> Either (P x) (Not (P x))
postulate lem2 : Either ((z : Nat) -> (FirstLimited (allDivSeq z xs) -> AllLimited (allDivSeq z xs)))
                        (Not ((z : Nat) -> (FirstLimited (allDivSeq z xs) -> AllLimited (allDivSeq z xs))))

-- パースの法則の変形
{-
postulate peirce : {P, Q : Nat -> Type} -> (x : Nat)
  -> Not ((z : Nat) -> (P z -> Q z))
    -> ((n : Nat) -> ((z : Nat) -> (P z -> Q z)) -> P n)
      -> P x
-}
postulate peirce2 : (x : Nat) -> (xs : CoList Integer)
  -> Not ((z : Nat) -> (FirstLimited (allDivSeq z xs) -> AllLimited (allDivSeq z xs)))
    -> ((n : Nat) -> (xs : CoList Integer)
          -> ((z : Nat) -> (FirstLimited (allDivSeq z xs) -> AllLimited (allDivSeq z xs)))
            -> FirstLimited (allDivSeq n xs))
      -> FirstLimited (allDivSeq n xs)
-- ########################################



--            from sub0xxxxx
-- ########################################
-- ########################################



