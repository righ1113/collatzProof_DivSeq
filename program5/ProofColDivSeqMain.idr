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
      makeLimitedDivSeq (()::xs) (S (((S k)+(S k)) + ((S k)+(S k)) + ((S k)+(S k)))) | Sa | ThreeZero | Even = ?rhs01 --with (parity k)
{-
      step q (S (((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l))) + ((S (l+l))+(S (l+l)))))                         | ThreeZero | Even | Even
        = IsFirstLimited02 q l (firstToAll q l) --(rs l $ lteToLt' $ lte72t45 l)
      step q (S (((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))) + ((S (S (l+l)))+(S (S (l+l)))))) | ThreeZero | Even | Odd  with (mod3 l)
        step q (S (((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m))))) + ((S (S ((m+m+m)+(m+m+m))))+(S (S ((m+m+m)+(m+m+m)))))))                                                                                                 | ThreeZero | Even | Odd | ThreeZero
          = IsFirstLimited03 q m (firstToAll q (m+m)) --(rs (m+m) $ lteToLt' $ lte216t81 m)
        step q (S (((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m)))))) + ((S (S ((S (m+m+m))+(S (m+m+m)))))+(S (S ((S (m+m+m))+(S (m+m+m))))))))                                                 | ThreeZero | Even | Odd | ThreeOne
          = IsFirstLimited04 q m (firstToAll q (S ((m+m)+(m+m)))) --(rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153 m)
        step q (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))))) | ThreeZero | Even | Odd | ThreeTwo
          = IsFirstLimited05 q m (firstToAll q (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m))))))))) --(rs (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) $ lteToLt' $ lte216t225 m)
-}
      makeLimitedDivSeq (()::xs) (S ((S (k+k)) + (S (k+k)) + (S (k+k)))) | Sa | ThreeZero | Odd with (mod3 k)
        makeLimitedDivSeq (()::xs) (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))                                                 | Sa | ThreeZero | Odd | ThreeZero
          = IsFirstLimited06 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l))))
        makeLimitedDivSeq (()::xs) (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))                         | Sa | ThreeZero | Odd | ThreeOne
          = IsFirstLimited07 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S (S (l+l+l+l)+(l+l+l+l)))))
        makeLimitedDivSeq (()::xs) (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))) | Sa | ThreeZero | Odd | ThreeTwo
          = IsFirstLimited08 xs l $ IsFtoA xs (makeLimitedDivSeq xs) (S (S (S ((l+l)+(l+l)))))
    -- 6 mod 9
    makeLimitedDivSeq (()::xs) (S (S (j + j + j)))     | Sa | ThreeOne
      = IsFirstLimited09 xs j $ IsFtoA xs (makeLimitedDivSeq xs) j
    -- 3 mod 9
    makeLimitedDivSeq (()::xs) (S (S (S (j + j + j)))) | Sa | ThreeTwo = ?rhs02 --with (parity j)
{-
    step q (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  | ThreeTwo | Even
      = IsFirstLimited11 q k (firstToAll q k) --(rs k $ lteToLt' $ lte36t21 k)
    step q (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) | ThreeTwo | Odd  with (mod3 k)
      step q (S (S (S ((S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l))) + (S ((l+l+l)+(l+l+l)))))))                                                 | ThreeTwo | Odd  | ThreeZero
        = IsFirstLimited12 q l (firstToAll q (l+l)) --(rs (l+l) $ lteToLt' $ lte108t39 l)
      step q (S (S (S ((S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l)))) + (S ((S (l+l+l))+(S (l+l+l))))))))                         | ThreeTwo | Odd  | ThreeOne
        = IsFirstLimited13 q l (firstToAll q (S ((l+l)+(l+l)))) --(rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l)
      step q (S (S (S ((S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))) + (S ((S (S (l+l+l)))+(S (S (l+l+l))))))))) | ThreeTwo | Odd  | ThreeTwo
        = IsFirstLimited14 q l (firstToAll q (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l))))))))) --(rs (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) $ lteToLt' $ lte108t111 l)
-}

namespace S
  u : Stream Unit
  u = repeat ()

-- 最終的な定理
limitedDivSeq : (n : Nat) -> Limited First S.u (B.allDivSeq n) n
limitedDivSeq = makeLimitedDivSeq S.u



