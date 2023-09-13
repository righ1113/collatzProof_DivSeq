module ProofColDivSeqPostulate

import ProofColDivSeqBase

%default total
%access export


--            from ProofColDivSeqBase
-- ########################################
-- 割数列が全て有限長なら Cont AllLimited
postulate makeAllL : (n : Nat) -> All Limited (ProofColDivSeqBase.allDivSeq n)
  -> Cont (AllL n) (FirstL n)
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
-- ########################################



--            from sub0xxxxx
-- ########################################
-- ########################################



