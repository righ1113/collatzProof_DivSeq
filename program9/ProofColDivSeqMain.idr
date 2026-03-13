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


-- 示すのに、整礎帰納法を使っている
-- コラッツ値が同じ完全割数列と拡張完全割数列は、行き先が同じ
isSameDesti : (u : Nat) -> SameDesti u
isSameDesti u = wfInd {P=SameDesti} {rel=LT'} step u where
  step : (x : Nat) -> ((y : Nat) -> LT' y x -> SameDesti y) -> SameDesti x
  step Z         _  = IsSameDesti10 -- 6*<0>+3 = 3
  step (S Z)     _  = IsSameDesti01 -- 6*<1>+3 = 9
  step (S (S x)) rs with (mod3 x)
    -- 6 mod 9
    step (S (S (j + j + j)))         rs | ThreeZero
            = IsSameDesti09 j
                (MakeSameDestiSeed09 j (C  j) (Ω (S (S (j + j + j))) z (extAnyX (S (S (j + j + j)))) (extAnyU z)))
                  $ rs j $ lteToLt' $ lte18t15 j
    -- 3 mod 9
    step (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
      step (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
            = let y = (S (S (S (   (k+k)  +    (k+k)  +    (k+k))))) in
              IsSameDesti11 k
                (MakeSameDestiSeed11 k (B  k) (Ω y z (extAnyX y) (extAnyU z)))
                  $ rs k $ lteToLt' $ lte36t21 k
      step (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
        step no12_18t06 rs | ThreeOne | Odd  | ThreeZero
            = IsSameDesti12 l
                (MakeSameDestiSeed12 l (DB l) (Ω no12_18t06 z (extAnyX no12_18t06) (extAnyU z)))
                  $ rs (l+l) $ lteToLt' $ lte108t39 l
        step no13_18t12 rs | ThreeOne | Odd  | ThreeOne
            = IsSameDesti13 l
                (MakeSameDestiSeed13 l (AB l) (Ω no13_18t12 z (extAnyX no13_18t12) (extAnyU z)))
                  $ rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l
        step no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
            = let x = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) in
              IsSameDesti14 l
                (MakeSameDestiSeed14 l (FB l) (Ω no14_18t18 z (extAnyX no14_18t18) (extAnyU z)))
                  $ rs x $ lteToLt' $ lte108t111 l
    -- 0 mod 9
    step (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
      step (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
        step no06_18t04 rs | ThreeTwo | Even | ThreeZero
            = let x = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) in
              IsSameDesti06 l
                (MakeSameDestiSeed06 l (CF l) (Ω no06_18t04 z (extAnyX no06_18t04) (extAnyU z)))
                  $ rs x $ lteToLt' $ lte108t27_2 l
        step no07_18t10 rs | ThreeTwo | Even | ThreeOne
            = let x = (S (S (S (S (l+l+l+l)+(l+l+l+l))))) in
              IsSameDesti07 l
                (MakeSameDestiSeed07 l (BF l) (Ω no07_18t10 z (extAnyX no07_18t10) (extAnyU z)))
                  $ rs x $ lteToLt' $ lte108t63_2 l
        step no08_18t16 rs | ThreeTwo | Even | ThreeTwo
            = let x = (S (S (S ((l+l)+(l+l))))) in
              IsSameDesti08 l
                (MakeSameDestiSeed08 l (EF l) (Ω no08_18t16 z (extAnyX no08_18t16) (extAnyU z)))
                  $ rs x $ lteToLt' $ lte108t99_2 l
      step (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
        step no02_12t07 rs | ThreeTwo | Odd | Even
            = IsSameDesti02 l
                (MakeSameDestiSeed02 l (E  l) (Ω no02_12t07 z (extAnyX no02_12t07) (extAnyU z)))
                  $ rs l $ lteToLt' $ lte72t45_2 l
        step noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
          step no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
            = IsSameDesti03 m
                (MakeSameDestiSeed03 m (DE m) (Ω no03_36t13 z (extAnyX no03_36t13) (extAnyU z)))
                  $ rs (m+m) $ lteToLt' $ lte216t81_2 m
          step no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
            = IsSameDesti04 m
                (MakeSameDestiSeed04 m (AE m) (Ω no04_36t25 z (extAnyX no04_36t25) (extAnyU z)))
                  $ rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m
          step no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
            = let x = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) in
              IsSameDesti05 m
                (MakeSameDestiSeed05 m (FE m) (Ω no05_36t37 z (extAnyX no05_36t37) (extAnyU z)))
                  $ rs x $ lteToLt' $ lte216t225_2 m

-- 最終的な定理
limitedDivSeq : (n : Nat) -> FirstLimited n
limitedDivSeq = IsFirstLimited isSameDesti IsFirstLimited10 IsFirstLimited01



