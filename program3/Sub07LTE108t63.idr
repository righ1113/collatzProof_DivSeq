module Sub07LTE108t63

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+10)+3 --BF[1,3,-2]--> 6(8t+4)+3
export
lte108t63 : (l : Nat) -> LTE (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))
  (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))



