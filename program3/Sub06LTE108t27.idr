module Sub06LTE108t27

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+4)+3 --CF[4,1,-2]--> 6(16t+3)+3
export
lte108t27 : (l : Nat) -> LTE (S (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))))
  (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))



