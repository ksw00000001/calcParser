# calcParse
$\lambda$計算に対し最左簡約戦略に基づき $\beta$ 正規型を半アルゴリズム的に求めるプログラム
## 動作環境
GHC 8.8.4 on Ubuntu 22.04.03のもとで動作を確認。hsファイルを置いたディレクトリで以下を実行すれば良い。Haskellがコンパイルできればどこでも動くはず。
```bash
ghc lambdaCalcLeftMostParser.hs
./lambdaCalcLeftMostParser
```
## 入出力について

### 入力方法

 $(\lambda .x x ) (a b ) c$ を計算するには以下のどれかを入力すればいい。
 変数は\から始まらない文字列なら何でも良い。文字と文字の間はスペースで区切ること。\を $\lambda$ と読み替える。抽象部分のドットはあってもなくても良い。
```
( \x. x x ) ( a b ) c
(\x x x)(a b)c
```

### 出力
ステップごとの $\beta$ 変換 の結果が出力される。デフォルトでは10ステップまでの計算が行われる。正規型が求まればその時点で計算は打ち切られる。
上記の式を入力すると以下のように出力される。
```
( \x. x x ) ( a b ) c
( \x. ( x x ) ) ( a b ) c 
a b ( a b ) c 
Normal Form
```
もっと長く計算を続けるにはhsファイルの最後の10をステップ数に応じて訂正すればよい。

### 略記
抽象の中身はできるだけ多く取り、適用は左結合になるように取る。このルールのもとで括弧を略して入力しても良い。
$$\lambda x . MN = \lambda x . ( MN )$$
$$LMN=(LM)N$$
出力では適用の括弧は適宜省略されるが抽象の中身の括弧は付く

