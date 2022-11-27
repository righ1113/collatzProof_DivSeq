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
makeLimitedDivSeq (()::xs) n with (norm n)
  makeLimitedDivSeq (()::xs) Z     | Za       = IsFirstLimited10 xs                                                                -- 6*<0>+3 = 3
  makeLimitedDivSeq (()::xs) (S x) | Sa {n=x} with (mod3 x)
    -- 0 mod 9
    makeLimitedDivSeq (()::xs) (S (j + j + j)) | Sa | ThreeZero with (parity j)
      makeLimitedDivSeq (()::xs) (S ((Z+Z) + (Z+Z) + (Z+Z)))                         | Sa | ThreeZero | Even = IsFirstLimited01 xs -- 6*<1>+3 = 9
      makeLimitedDivSeq (()::xs) (S (((S k)+(S k)) + ((S k)+(S k)) + ((S k)+(S k)))) | Sa | ThreeZero | Even with (parity k)

        makeLimitedDivSeq (()::xs) no02_12t07 | Sa | ThreeZero | Even | Even
          = IsFirstLimited02 xs l $ IsFtoA xs (makeLimitedDivSeq xs) l
        makeLimitedDivSeq (()::xs) noxx_12t13 | Sa | ThreeZero | Even | Odd  with (mod3 l)
          makeLimitedDivSeq (()::xs) no03_36t13 | Sa | ThreeZero | Even | Odd | ThreeZero
            = IsFirstLimited03 xs m $ IsFtoA xs (makeLimitedDivSeq xs) (m+m)
          makeLimitedDivSeq (()::xs) no04_36t25 | Sa | ThreeZero | Even | Odd | ThreeOne
            = IsFirstLimited04 xs m $ IsFtoA xs (makeLimitedDivSeq xs) (S ((m+m)+(m+m)))
          makeLimitedDivSeq (()::xs) no05_36t37 | Sa | ThreeZero | Even | Odd | ThreeTwo
            = IsFirstLimited05 xs m $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))

      makeLimitedDivSeq (()::xs) (S ((S (k+k)) + (S (k+k)) + (S (k+k)))) | Sa | ThreeZero | Odd with (mod3 k)
        makeLimitedDivSeq (()::xs) no06_18t04 | Sa | ThreeZero | Odd | ThreeZero
          = IsFirstLimited06 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))
        makeLimitedDivSeq (()::xs) no07_18t10 | Sa | ThreeZero | Odd | ThreeOne
          = IsFirstLimited07 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S (S (l+l+l+l)+(l+l+l+l)))))
        makeLimitedDivSeq (()::xs) no08_18t16 | Sa | ThreeZero | Odd | ThreeTwo
          = IsFirstLimited08 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S ((l+l)+(l+l)))))
    -- 6 mod 9
    makeLimitedDivSeq (()::xs) (S (S (j + j + j)))     | Sa | ThreeOne
      = IsFirstLimited09 xs j $ IsFtoA xs (makeLimitedDivSeq xs) j
    -- 3 mod 9
    makeLimitedDivSeq (()::xs) (S (S (S (j + j + j)))) | Sa | ThreeTwo with (parity j)

      makeLimitedDivSeq (()::xs) (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  | Sa | ThreeTwo | Even
        = IsFirstLimited11 xs k $ IsFtoA xs (makeLimitedDivSeq xs) k
      makeLimitedDivSeq (()::xs) (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) | Sa | ThreeTwo | Odd  with (mod3 k)
        makeLimitedDivSeq (()::xs) no12_18t06 | Sa | ThreeTwo | Odd  | ThreeZero
          = IsFirstLimited12 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (l+l)
        makeLimitedDivSeq (()::xs) no13_18t12 | Sa | ThreeTwo | Odd  | ThreeOne
          = IsFirstLimited13 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S ((l+l)+(l+l)))
        makeLimitedDivSeq (()::xs) no14_18t18 | Sa | ThreeTwo | Odd  | ThreeTwo
          = IsFirstLimited14 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))


namespace S
  u : Stream Unit
  u = repeat ()

-- 最終的な定理
limitedDivSeq : (n : Nat) -> Limited First S.u (B.allDivSeq n) n
limitedDivSeq = makeLimitedDivSeq S.u



