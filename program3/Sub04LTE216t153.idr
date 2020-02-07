module Sub04LTE216t153

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(36t+25)+3 --AE[6,-2,-4]--> 6(4t+1)+3
export
lte216t153 : (m : Nat) -> LTE (S (S ((m+m)+(m+m))))
  (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))



