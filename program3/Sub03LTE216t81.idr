module Sub03LTE216t81

import ProofColDivSeqBase
import ProofColDivSeqPostulate

%default total


-- 6(36t+13)+3 --DE[3,0,-4]--> 6(2t)+3
export
lte216t81 : (m : Nat) -> LTE (S (m+m))
  (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))



