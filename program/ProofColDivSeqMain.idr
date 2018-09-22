module ProofColDivSeqMain

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import ProofColDivSeqLvDown
import Sub01Apply18x3
import Sub02Apply54x12
import Sub03Apply54x30
import Sub05Apply9x6

%default total
-- %language ElabReflection


-- 無限降下法の十分条件
unifi : (n:Nat) -> P (S n) 2 -> (m ** (LTE (S m) (S n), P m 2))
unifi n prf with (mod3 n)
  unifi (j + j + j)         prf | ThreeZero with (parity j)
    unifi ((k+k) + (k+k) + (k+k))       prf | ThreeZero | Even = apply18x3 prf
    unifi (S (k+k) + S (k+k) + S (k+k)) prf | ThreeZero | Odd with (mod3 k)
      unifi (S ((l+l+l)+(l+l+l)) + S ((l+l+l)+(l+l+l)) + S ((l+l+l)+(l+l+l))) prf | ThreeZero | Odd | ThreeZero = apply54x12 prf
      unifi (S ((S (l+l+l))+(S (l+l+l))) + S ((S (l+l+l))+(S (l+l+l))) + S ((S (l+l+l))+(S (l+l+l)))) prf | ThreeZero | Odd | ThreeOne = apply54x30 prf
      unifi (S ((S (S (l+l+l)))+(S (S (l+l+l)))) + S ((S (S (l+l+l)))+(S (S (l+l+l)))) + S ((S (S (l+l+l)))+(S (S (l+l+l))))) prf | ThreeZero | Odd | ThreeTwo = ?rhs7
  unifi (S (j + j + j))     prf | ThreeOne = apply9x6 prf
  unifi (S (S (j + j + j))) prf | ThreeTwo = ?rhs3

allDivSeqInfFalse' : any unLimited (allDivSeq (n+n+n) 2) = False
allDivSeqInfFalse' = infiniteDescent unifi base0

-- レベルを下げる関数2
lvDown2 : (n, lv:Nat)
  -> any unLimited (allDivSeq (n+n+n) lv) = False
    -> any unLimited (allDivSeq (n+n+n) (pred lv)) = False
lvDown2 n Z = \y => y
lvDown2 n (S lv) = rewrite unfold (n+n+n) lv in \y => aDSFalse (n+n+n) lv y


-- 最終的な定理
allDivSeqInfFalse : (n:Nat)
  -> any unLimited (allDivSeq (n+n+n) 0) = False
allDivSeqInfFalse n = lvDown2 n 1 $ lvDown2 n 2 allDivSeqInfFalse'




