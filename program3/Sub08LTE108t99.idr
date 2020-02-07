module Sub08LTE108t99

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+16)+3 --EF[2,1,-2]--> 6(8t+3)+3
export
lte108t99 : (l : Nat) -> LTE (S (S (S (S ((l+l)+(l+l))))))
  (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l)))))))



