{-
Docker 起動
.bashrc に alias idris1='docker run -it --rm -v $(pwd):/src -w /src nixos/nix:latest nix-shell -p idris'
$ source ~/.bashrc
$ cd collatzProof_DivSeq/program9
$ idris1
$ idris
> :l ProofColDivSeqMain
-}
module ProofColDivSeqMain

import ProofColDivSeqBase
import ProofColDivSeqPostulate
import Sub02LTE72t45
import Sub03LTE216t81
import Sub04LTE216t153
import Sub05LTE216t225
import Sub06LTE108t27
import Sub07LTE108t63
import Sub08LTE108t99
import Sub09LTE18t15
import Sub11LTE36t21
import Sub12LTE108t39
import Sub13LTE108t75
import Sub14LTE108t111

%default total


-- data ColDivSeq完全割数列    : Nat(6t+3のt) -> Type (3, 9, star(G含)で定義する)
-- data ExtDivSeq拡張完全割数列 : t            -> Type (ColDivSeq, star, extで定義する)
-- data LimitedExtDivSeq : Nat -> Type where
--   Is : (t -> Not . LimitedExtDivSeq BIG -> Not . LimitedExtDivSeq SMALL) の対偶
-- limitedExtDivSeq : (u : Nat) -> LimitedExtDivSeq u (反例の最小性に反する、もしくは整礎帰納法)
-- limitedColDivSeq : (n : Nat) -> LimitedColDivSeq n (最終的な定理、完全割数列は拡張完全割数列の部分集合)


-- 示すのに、整礎帰納法を使っている
-- 拡張完全割数列は有限長
limitedExtDivSeq : (u : Nat) -> LimitedExtDivSeq u
limitedExtDivSeq u = wfInd {P=LimitedExtDivSeq} {rel=LT'} step u where
  step : (x : Nat) -> ((y : Nat) -> LT' y x -> LimitedExtDivSeq y) -> LimitedExtDivSeq x
  step Z         _  = IsLimitedExtDivSeq10 -- 6*<0>+3 = 3
  step (S Z)     _  = IsLimitedExtDivSeq01 -- 6*<1>+3 = 9
  step (S (S x)) rs with (mod3 x)
    -- 6 mod 9
    step (S (S (j + j + j)))         rs | ThreeZero
            = IsLimitedExtDivSeq09 j
                  (rs j $ lteToLt' $ lte18t15 j)
    -- 3 mod 9
    step (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
      step (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
            = let y = (S (S (S (   (k+k)  +    (k+k)  +    (k+k))))) in
              IsLimitedExtDivSeq11 k
                  (rs k $ lteToLt' $ lte36t21 k)
      step (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
        step no12_18t06 rs | ThreeOne | Odd  | ThreeZero
            = IsLimitedExtDivSeq12 l
                  (rs (l+l) $ lteToLt' $ lte108t39 l)
        step no13_18t12 rs | ThreeOne | Odd  | ThreeOne
            = IsLimitedExtDivSeq13 l
                  (rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l)
        step no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
            = let x = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) in
              IsLimitedExtDivSeq14 l
                  (rs x $ lteToLt' $ lte108t111 l)
    -- 0 mod 9
    step (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
      step (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
        step no06_18t04 rs | ThreeTwo | Even | ThreeZero
            = let x = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) in
              IsLimitedExtDivSeq06 l
                  (rs x $ lteToLt' $ lte108t27_2 l)
        step no07_18t10 rs | ThreeTwo | Even | ThreeOne
            = let x = (S (S (S (S (l+l+l+l)+(l+l+l+l))))) in
              IsLimitedExtDivSeq07 l
                  (rs x $ lteToLt' $ lte108t63_2 l)
        step no08_18t16 rs | ThreeTwo | Even | ThreeTwo
            = let x = (S (S (S ((l+l)+(l+l))))) in
              IsLimitedExtDivSeq08 l
                  (rs x $ lteToLt' $ lte108t99_2 l)
      step (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
        step no02_12t07 rs | ThreeTwo | Odd | Even
            = IsLimitedExtDivSeq02 l
                  (rs l $ lteToLt' $ lte72t45_2 l)
        step noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
          step no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
            = IsLimitedExtDivSeq03 m
                  (rs (m+m) $ lteToLt' $ lte216t81_2 m)
          step no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
            = IsLimitedExtDivSeq04 m
                  (rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m)
          step no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
            = let x = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) in
              IsLimitedExtDivSeq05 m
                  (rs x $ lteToLt' $ lte216t225_2 m)

-- 最終的な定理
limitedColDivSeq : (n : Nat) -> LimitedColDivSeq n
limitedColDivSeq = IsLimitedColDivSeq limitedExtDivSeq

partial
theorem : (n : Nat) -> LimitedColDivSeq n
  -> (cnt ** limitedNStep (divSeq n) cnt = True)
theorem n (MakeLimitedColDivSeq n (IsLimited n p)) = p
partial
nearCollatz : (n : Nat) -> (cnt ** limitedNStep (divSeq n) cnt = True)
nearCollatz n = theorem n $ limitedColDivSeq n



