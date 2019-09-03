module ProofColDivSeqPostulate

import ProofColDivSeqBase

%default total
%access export


--            from ProofColDivSeqBase
-- ########################################
-- ########################################



--            from ProofColDivSeqMain
-- ########################################
--コラッツが真ならば、First z -> All z も真
postulate fTOA : FirstLimited (allDivSeq n)
  -> ((z : Nat) -> FirstLimited (allDivSeq z) -> AllLimited (allDivSeq z))
-- ########################################



--            from sub0xxxxx
-- ########################################
-- ########################################



