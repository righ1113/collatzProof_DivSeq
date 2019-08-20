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
--postulate lem : {P : Nat -> Type} -> Either ((z : Nat) -> P z) (Not ((z : Nat) -> P z))
postulate lem2 : Either ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
                        (Not ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z))))

-- パースの法則の変形
{--}
postulate peirce : {P, Q : Nat -> Type} -> (x : Nat)
  -> Not ((z : Nat) -> (P z -> Q z))
    -> (((z : Nat) -> (P z -> Q z)) -> ((n : Nat) -> P n))
      -> P x
{--}
postulate peirce2 : (x : Nat)
  -> Not ((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
    -> (((z : Nat) -> (FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z)))
          -> ((n : Nat) -> FirstLimited (allDivSeq n)))
      -> FirstLimited (allDivSeq n)
-- ########################################



--            from sub0xxxxx
-- ########################################
-- ########################################



