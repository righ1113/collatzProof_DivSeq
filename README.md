# collatzProof_DivSeq
割数列を用いたコラッツ予想の証明  

<br />
<br />
<br />

# 変更履歴
23/09/13　program7 と program8 は両方有効です  
23/08/22　復活しました。　program7 を見てください  
23/01/07　こちらは閉めます。続きはこっちで [divseq2](https://github.com/righ1113/divSeq2)  
22/12/10　再完成しました　program5：ver5.0をリリース  
22/11/25　また別の方法にしました。様子をみます  
22/11/17　相互再帰にして直しました。様子をみます  
22/05/07　問題が見つかったのでしばらく置きます  
22/02　　　Advances in Pure Mathematics 誌に accept されました  
20/09/19　完成しました　program3：ver4.0をリリース　Wiki：完  
20/03/20　復活しました　program3：ver3.0をリリース  
19/11/05　諦めました  
19/10/05　program3, Wiki：鋭意修正中  
19/08/10　program2：program3に移行する  
19/07/18　program：program2に移行する  
19/05/18　Wiki：最新の状態に更新  
19/05/06　program：ver2.0をリリース  
19/04/04　program：postulate命題12個を証明  
19/03/22　program：postulate命題2個を証明  
19/03/18　program：ver1.2をリリース　`Limited`を(全域)型として定義  
19/03/17　<a href="http://vixra.org/abs/1903.0296" target="_blank">English version Wiki is here.</a>  
19/01/25　program：ver1.1をリリース　`divSeq`の実装を`unfoldr`に変更  
18/11/18　program：ver1.0をリリース　program、Wiki共にひとまず完成  
18/11/03　Wiki：第1部を作成完了  
18/10/01　Wiki：第2部を作成完了  
18/09/20　program：ver0.5をリリース　レベルを下げる関数の変更完了  
18/09/17　program：ver0.2をリリース  
18/09/10　program：ver0.1をリリース  

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
9[2,1,1,2,3,4]は完全割数列です。  
7[1,1,2,3,4]はふつうの割数列です。  
　  

# 証明&プログラムの説明
[Wiki](https://github.com/righ1113/collatzProof_DivSeq/wiki)をみてね  

<br />
<br />
<br />
