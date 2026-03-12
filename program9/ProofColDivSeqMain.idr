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
            = IsSameDesti09 j (MakeSameDestiSeed09 j (C j) (Ω j (S (S (j + j + j))) (C j) (extAny (S (S (j + j + j)))))) $ rs j $ lteToLt' $ lte18t15 j
    -- 3 mod 9
    step (S (S (S (j + j + j))))     rs | ThreeOne with (parity j)
      step (S (S (S (   (k+k)  +    (k+k)  +    (k+k)))))  rs | ThreeOne | Even
            = let x = (S (S (S (   (k+k)  +    (k+k)  +    (k+k))))) in
              IsSameDesti11 k (MakeSameDestiSeed11 k (B k) (Ω k x (B k) (extAny x))) $ rs k $ lteToLt' $ lte36t21 k
      step (S (S (S ((S (k+k)) + (S (k+k)) + (S (k+k)))))) rs | ThreeOne | Odd  with (mod3 k)
        step no12_18t06 rs | ThreeOne | Odd  | ThreeZero
            = IsSameDesti12 l (MakeSameDestiSeed12 l (DB l) (Ω (l+l) no12_18t06 (DB l) (extAny no12_18t06))) $ rs (l+l) $ lteToLt' $ lte108t39 l
        step no13_18t12 rs | ThreeOne | Odd  | ThreeOne
            = let omega = Ω (S ((l+l)+(l+l))) no13_18t12 (AB l) (extAny no13_18t12) in
              IsSameDesti13 l (MakeSameDestiSeed13 l (AB l) omega) $ rs (S ((l+l)+(l+l))) $ lteToLt' $ lte108t75 l
        step no14_18t18 rs | ThreeOne | Odd  | ThreeTwo
            = let x = (S (S (S (S (S (S (S (l+l+l+l)+(l+l+l+l)))))))) in
              IsSameDesti14 l (MakeSameDestiSeed14 l (FB l) (Ω x no14_18t18 (FB l) (extAny no14_18t18))) $ rs x $ lteToLt' $ lte108t111 l
    -- 0 mod 9
    step (S (S (S (S (j + j + j))))) rs | ThreeTwo with (parity j)
      step (S (S (S (S ((k+k) + (k+k) + (k+k)))))) rs | ThreeTwo | Even with (mod3 k)
        step no06_18t04 rs | ThreeTwo | Even | ThreeZero
            = let x = (S (S (S (l+l+l+l)+(l+l+l+l)+(l+l+l+l)+(l+l+l+l)))) in
              IsSameDesti06 l (MakeSameDestiSeed06 l (CF l) (Ω x no06_18t04 (CF l) (extAny no06_18t04))) $ rs x $ lteToLt' $ lte108t27_2 l
        step no07_18t10 rs | ThreeTwo | Even | ThreeOne
            = let x = (S (S (S (S (l+l+l+l)+(l+l+l+l))))) in
              IsSameDesti07 l (MakeSameDestiSeed07 l (BF l) (Ω x no07_18t10 (BF l) (extAny no07_18t10))) $ rs x $ lteToLt' $ lte108t63_2 l
        step no08_18t16 rs | ThreeTwo | Even | ThreeTwo
            = let x = (S (S (S ((l+l)+(l+l))))) in
              IsSameDesti08 l (MakeSameDestiSeed08 l (EF l) (Ω x no08_18t16 (EF l) (extAny no08_18t16))) $ rs x $ lteToLt' $ lte108t99_2 l
      step (S (S (S (S (S (k+k) + S (k+k) + S (k+k)))))) rs | ThreeTwo | Odd with (parity k)
        step no02_12t07 rs | ThreeTwo | Odd | Even
            = IsSameDesti02 l (MakeSameDestiSeed02 l (E l) (Ω l no02_12t07 (E l) (extAny no02_12t07))) $ rs l $ lteToLt' $ lte72t45_2 l
        step noxx_12t13 rs | ThreeTwo | Odd | Odd  with (mod3 l)
          step no03_36t13 rs | ThreeTwo | Odd | Odd | ThreeZero
            = IsSameDesti03 m (MakeSameDestiSeed03 m (DE m) (Ω (m+m) no03_36t13 (DE m) (extAny no03_36t13))) $ rs (m+m) $ lteToLt' $ lte216t81_2 m
          step no04_36t25 rs | ThreeTwo | Odd | Odd | ThreeOne
            = IsSameDesti04 m (MakeSameDestiSeed04 m (AE m) (Ω (S ((m+m)+(m+m))) no04_36t25 (AE m) (extAny no04_36t25))) $ rs (S ((m+m)+(m+m))) $ lteToLt' $ lte216t153_2 m
          step no05_36t37 rs | ThreeTwo | Odd | Odd | ThreeTwo
            = let x = (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))) in
              IsSameDesti05 m (MakeSameDestiSeed05 m (FE m) (Ω x no05_36t37 (FE m) (extAny no05_36t37))) $ rs x $ lteToLt' $ lte216t225_2 m

-- 最終的な定理
limitedDivSeq : (n : Nat) -> FirstLimited n
limitedDivSeq = IsFirstLimited isSameDesti IsFirstLimited10 IsFirstLimited01



