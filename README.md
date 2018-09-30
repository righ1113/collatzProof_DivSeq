# collatzProof_DivSeq
割数列を用いたコラッツ予想の証明
# 変更履歴
18/09/10 program:ver0.1をリリース  
18/09/17 program:ver0.2をリリース  
18/09/20 program:ver0.5をリリース　レベルを下げる関数の変更完了  
# コラッツ予想とは
コラッツの問題は、「任意の正の整数 n をとり、  
  
- n が偶数の場合、n を 2 で割る  
- n が奇数の場合、n に 3 をかけて 1 を足す  
  
という操作を繰り返すと、どうなるか」というものである。  
「どんな初期値から始めても、有限回の操作のうちに必ず 1 に到達する(そして 1→4→2→1 というループに入る)」という主張が、コラッツの予想である。   
（Wikipediaより）  
# 割数列とは
コラッツ操作で2で割った回数を並べます。  
これを割数列と名付けます。  
例えば9の場合は、コラッツ列は  
9,28,14,7,22,11,34,17,52,26,13,40,20,10,5,16,8,4,2,1  
ですから割数列は  
[2,1,1,2,3,4]  
となります。

初期値が3の倍数の割数列を完全割数列と名付けます。  
9≡[2,1,1,2,3,4]は完全割数列です。  
7≡[1,1,2,3,4]はふつうの割数列です。  
（5chより）  
# 証明&プログラムの説明
[Wiki](https://github.com/righ1113/collatzProof_DivSeq/wiki)をみてね  
  
  
  
