{-
$ cd collatzProof_DivSeq/program5
$ chcp 65001
$ idris
> :l ProofColDivSeqMain
-}
module ProofColDivSeqMain

import ProofColDivSeqBase as B
import ProofColDivSeqPostulate

%default total


makeLimitedDivSeq : (q : Stream Unit) -> (n : Nat) -> Limited First q (B.allDivSeq n) n
makeLimitedDivSeq (()::qs) Z     = IsFirstLimited10 qs                                                                      -- 6*<0>+3 = 3
makeLimitedDivSeq (()::qs) (S x) with (mod3 x)
  -- 0 mod 9
  makeLimitedDivSeq (()::qs) (S (j + j + j)) | ThreeZero with (parity j)
    makeLimitedDivSeq (()::qs) (S ((Z+Z) + (Z+Z) + (Z+Z)))                         | ThreeZero | Even = IsFirstLimited01 qs -- 6*<1>+3 = 9
    makeLimitedDivSeq (()::qs) (S (((S k)+(S k)) + ((S k)+(S k)) + ((S k)+(S k)))) | ThreeZero | Even with (parity k)

      makeLimitedDivSeq (()::qs) no02_12t07 | ThreeZero | Even | Even
        = IsFirstLimited02 qs l $ IsFtoA qs (makeLimitedDivSeq qs) l
      makeLimitedDivSeq (()::qs) noxx_12t13 | ThreeZero | Even | Odd  with (mod3 l)
        makeLimitedDivSeq (()::qs) no03_36t13 | ThreeZero | Even | Odd | ThreeZero
          = IsFirstLimited03 qs m $ IsFtoA qs (makeLimitedDivSeq qs) (m+m)
        makeLimitedDivSeq (()::qs) no04_36t25 | ThreeZero | Even | Odd | ThreeOne
          = IsFirstLimited04 qs m $ IsFtoA qs (makeLimitedDivSeq qs) (S ((m+m)+(m+m)))
        makeLimitedDivSeq (()::qs) no05_36t37 | ThreeZero | Even | Odd | ThreeTwo
          = IsFirstLimited05 qs m $ IsFtoA qs (makeLimitedDivSeq qs) (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))

    makeLimitedDivSeq (()::qs) (S ((S (k+k)) + (S (k+k)) + (S (k+k)))) | ThreeZero | Odd with (mod3 k)
      makeLimitedDivSeq (()::qs) no06_18t04 | ThreeZero | Odd | ThreeZero
        = IsFirstLimited06 qs l $ IsFtoA qs (makeLimitedDivSeq qs) (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))
      makeLimitedDivSeq (()::qs) no07_18t10 | ThreeZero | Odd | ThreeOne
        = IsFirstLimited07 qs l $ IsFtoA qs (makeLimitedDivSeq qs) (S (S (S (S (l+l+l+l)+(l+l+l+l)))))
      makeLimitedDivSeq (()::qs) no08_18t16 | ThreeZero | Odd | ThreeTwo
        = IsFirstLimited08 qs l $ IsFtoA qs (makeLimitedDivSeq qs) (S (S (S ((l+l)+(l+l)))))
  -- 6 mod 9
  makeLimitedDivSeq (()::qs) (S (S (j + j + j)))     | ThreeOne
    = IsFirstLimited09 qs j $ IsFtoA qs (makeLimitedDivSeq qs) j
  -- 3 mod 9
  makeLimitedDivSeq (()::qs) (S (S (S (j + j + j)))) | ThreeTwo with (parity j)

    makeLimitedDivSeq (()::qs) (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  | ThreeTwo | Even
      = IsFirstLimited11 qs k $ IsFtoA qs (makeLimitedDivSeq qs) k
    makeLimitedDivSeq (()::qs) (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) | ThreeTwo | Odd  with (mod3 k)
      makeLimitedDivSeq (()::qs) no12_18t06 | ThreeTwo | Odd  | ThreeZero
        = IsFirstLimited12 qs l $ IsFtoA qs (makeLimitedDivSeq qs) (l+l)
      makeLimitedDivSeq (()::qs) no13_18t12 | ThreeTwo | Odd  | ThreeOne
        = IsFirstLimited13 qs l $ IsFtoA qs (makeLimitedDivSeq qs) (S ((l+l)+(l+l)))
      makeLimitedDivSeq (()::qs) no14_18t18 | ThreeTwo | Odd  | ThreeTwo
        = IsFirstLimited14 qs l $ IsFtoA qs (makeLimitedDivSeq qs) (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))


namespace S
  u : Stream Unit
  u = repeat ()

-- 最終的な定理
limitedDivSeq : (n : Nat) -> Limited First S.u (B.allDivSeq n) n
limitedDivSeq = makeLimitedDivSeq S.u



