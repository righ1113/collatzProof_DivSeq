module Sub02LTE72t45

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(12t+7)+3 --E[2,-4]--> 6t+3
export
lte72t45 : (l : Nat) -> LTE (S l)
  (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))



