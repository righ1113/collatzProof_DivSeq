module Sub13LTE108t111

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(18t+18)+3 --FB[5,-1,-2]--> 6(8t+7)+3
export
lte108t111 : (l : Nat) -> LTE (S (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))))
  (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l)))))))))



