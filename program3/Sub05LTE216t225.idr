module Sub05LTE216t225

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(36t+37)+3 --FE[5,0,-4]--> 6(8t+7)+3
export
lte216t225 : (m : Nat) -> LTE (S (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))))
  (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m)))))))))



