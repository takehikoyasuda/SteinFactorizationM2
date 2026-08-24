# Stein factorization論文改訂案：グラフの直接計算

対象論文：Takehiko Yasuda, *An algorithm for the minimal model program in
dimension three*, arXiv:2603.13703v2

作成日：2026年8月7日

## 1. 結論

現論文のSection 5.2とAlgorithm 1では、Stein中間項

\[
Y \xrightarrow{h} Z \xrightarrow{g} X
\]

のうち、グラフ \(\Gamma_h\) を次のように求めている。

1. \(Y\times Z\to Y\times X\) による \(\Gamma_f\) の逆像を計算する。
2. その成分を計算する。
3. \(Y\) への射影が同型となる成分を選ぶ。

Lemma 5.2で得られる埋め込み

\[
C\hookrightarrow R_\gamma,
\qquad
\psi\longmapsto \frac{\psi(\gamma)}{\gamma}
\]

を使えば、成分分解を経ずに \(\Gamma_h\) をkernelとして直接計算できる。
ただし、現在のMacaulay2実装 `directSteinGraph` の二重次数の付け方は誤って
おり、そのまま論文に採用してはいけない。本稿では、正しい二重次数版の直接構成
を提案する。

## 2. 現在の実装で見つかった問題

現在の実装は、\(S=k[y,x]\) と \(Z\) の座標変数 \(z_i\) に対して

\[
\Phi:S[z_0,\ldots,z_N]\longrightarrow R_\gamma[t],
\qquad
z_i\longmapsto c_i t^{b_i}
\]

を作り、次の二重次数を与えている。

\[
\deg y_j=(d_j,0),\qquad
\deg x_i=(0,a_i),\qquad
\deg z_\ell=(0,b_\ell).
\]

ここでは、元の \(X\) 座標 \(x_i\) と新しい \(Z\) 座標 \(z_\ell\) が同じ
第二次数ブロックに入っている。しかし、\(\Gamma_f\times Z\) では両者は独立に
射影スケーリングされなければならない。この次数付けでは \(x\) と \(z\) の相対的
スカラーが余分な幾何学的パラメータとして残る。

### 恒等写像による反例

\(f:\mathbb P^1\to\mathbb P^1\) を恒等写像とする。現在のkernelは本質的に

\[
y_0x_1-y_1x_0,\qquad
y_0z_1-y_1z_0,\qquad
x_0z_1-x_1z_0
\]

で生成される。三つの座標対が比例するという式だが、現在の二重次数では
\((x_0,x_1,z_0,z_1)\) 全体が一つの \(\mathbb P^3\) の座標として扱われる。
したがって、得られるものは \(\mathbb P^1\times\mathbb P^3\) 内の2次元の
rank-one locusであり、1次元の恒等写像のグラフではない。

Macaulay2で確認すると、恒等写像、二乗写像、三乗写像のすべてで、入力グラフ環
のKrull次元が3であるのに対し、現在の `directSteinGraph` の出力環のKrull次元は
4となる。イデアルは素かつ斉次なので、現在のテストではこの誤りを検出できない。

## 3. 修正した直接構成

論文の記号を用いる。\(Y=\operatorname{Proj}B\)、\(X=\operatorname{Proj}A\)、
\(\Gamma_f=\operatorname{Proj}R\) とし、\(Y\) のambient weighted projective
spaceの座標を \(y_0,\ldots,y_n\)、\(\deg y_j=d_j\) とする。

Section 5.1で計算したStein中間項の座標環を

\[
C=\bigoplus_{v\geq0}H^0(Y,f^*\mathcal O_X(v))
\]

とする。\(c_0,\ldots,c_N\) を \(C\) の斉次 \(k\)-代数生成元とし、
\(\deg c_i=b_i>0\) とする。Lemma 5.2の埋め込みを

\[
\iota:C\hookrightarrow R_\gamma
\]

と書く。

二重次数付き多項式環

\[
T=k[y_0,\ldots,y_n,z_0,\ldots,z_N],
\qquad
\deg y_j=(d_j,0),\quad \deg z_i=(0,b_i)
\]

を作り、環準同型

\[
\Phi:T\longrightarrow R_\gamma[t]
\]

を

\[
\Phi(y_j)=\overline{y_j},
\qquad
\Phi(z_i)=\iota(c_i)t^{b_i}
\]

で定める。ここで \(t\) は \(z\)-方向のweighted homogeneous degreeを記録する
ための独立変数である。

提案するグラフイデアルは

\[
I_h:=\ker\Phi
\]

である。重要なのは、元の \(X\) 座標 \(x_i\) を \(T\) に含めないことである。
\(x_i\) はtarget ring \(R_\gamma[t]\) の内部計算には残ってよいが、出力する
二重射影空間の座標にはしない。kernelの計算が \(x_i\) を自動的に消去する。

## 4. 論文に追加する命題案

### Proposition（direct computation of the Stein graph）

Let the notation and assumptions be as in Section 5.1. Assume that \(Y\) is
integral, that \(\gamma\in R_{\geq\mathbf r}\) is nonzero, and that
\(c_0,\ldots,c_N\) are positive-degree homogeneous generators of \(C\) as a
\(k\)-algebra. Let

\[
\Phi:k[y_0,\ldots,y_n,z_0,\ldots,z_N]
\longrightarrow R_\gamma[t]
\]

be the homomorphism defined above. Then \(\ker\Phi\) is bihomogeneous, and the
biprojective subscheme defined by \(\ker\Phi\) is the graph of the morphism
\(h:Y\to Z=\operatorname{Proj}C\).

### 証明案

\(U=D_+(\gamma)\subset\Gamma_f\cong Y\) とする。\(Y\) はintegralかつ
\(\gamma\neq0\) なので、\(U\) は稠密開集合である。

Lemma 5.2の証明によれば、\(\iota(c_i)\in R_\gamma\) は \(c_i\) に対応する
\(Y\) 上の大域切断を \(U\) に制限したものである。したがって、\(U\) 上で
\(h\) はweighted homogeneous coordinates

\[
[\iota(c_0):\cdots:\iota(c_N)]
\]

により表される。

変数 \(t\) の指数を \(b_i\) とすることにより、異なるweighted degreeを持つ
項の間の不適切な相殺が防がれる。従って、\(\ker\Phi\) の各二重斉次部分は、
\(U\) 上のグラフ \(\Gamma_{h|_U}\) で消える二重斉次式全体に一致する。

\(Z\) は射影的、従って分離的なので、\(h\) のグラフ \(\Gamma_h\) は
\(Y\times Z\) の閉部分スキームである。また、integral schemeの稠密開部分は
schematically denseである。よって \(\Gamma_{h|_U}\) のscheme-theoretic
closureは \(\Gamma_h\) であり、\(\ker\Phi\) が定めるbiprojective subschemeは
\(\Gamma_h\) に一致する。

さらに、\(k[z_0,\ldots,z_N]\to R_\gamma\) は
\(k[z_0,\ldots,z_N]\twoheadrightarrow C\hookrightarrow R_\gamma\) と分解するため、
第二射影の像は \(\operatorname{Proj}C=Z\) に含まれる。

## 5. Section 5.2の改訂案

現Section 5.2のfiber-product/component-selection方式を、上の命題による直接
kernel方式に置き換えることを提案する。

改訂後の流れは次のとおりである。

1. Section 5.1で \(C\) と \(A\to C\) を計算する。
2. Lemma 5.2の埋め込み \(C\hookrightarrow R_\gamma\) と斉次生成元 \(c_i\) を
   計算する。
3. 上記の \(\Phi:T\to R_\gamma[t]\) を作る。
4. \(I_h=\ker\Phi\) を計算し、\(\Gamma_h=\operatorname{Proj}T/I_h\) を返す。

この変更により、次が不要になる。

- \(Y\times Z\to Y\times X\) による逆像の全体を構成すること。
- radicalまたはminimal-prime decompositionを行うこと。
- 各成分について \(Y\) への射影が同型かを判定すること。

旧方式を残す場合は、理論的な代替アルゴリズムまたは正しさの比較用としてRemark
に移すのがよい。なお、本文Section 5.2はreduced irreducible componentsを使う
一方、Algorithm 1はconnected componentsと書いているので、旧方式を残す場合は
この不一致も修正する必要がある。

## 6. Algorithm 1の改訂案

現在のSteps (2)--(4)を次で置き換える。

> (2) Choose a nonzero bihomogeneous element
> \(\gamma\in R_{\geq\mathbf r}\) and homogeneous generators
> \(c_0,\ldots,c_N\) of \(C\). Using Lemma 5.2, compute their images in
> \(R_\gamma\).
>
> (3) Form the bihomogeneous homomorphism
> \[
> k[y_0,\ldots,y_n,z_0,\ldots,z_N]\longrightarrow R_\gamma[t],
> \qquad y_j\mapsto\bar y_j,\quad z_i\mapsto c_i t^{\deg c_i}.
> \]
>
> (4) Compute its kernel and return the resulting graph morphism
> \(h:Y\to Z\), together with the homogeneous morphism \(g:Z\to X\).

## 7. 三重次数による代替表現

元の \(X\) 座標を残したい場合は、同じkernelに

\[
\deg y_j=(d_j,0,0),\qquad
\deg x_i=(0,a_i,0),\qquad
\deg z_\ell=(0,0,b_\ell)
\]

という三重次数を与えれば、\(\Gamma_f\times Z\) 内のグラフとして解釈できる。
現在の実装が計算しているungraded idealは、この三重次数では正しい候補である。

ただし、論文はmonograded/bigraded varietiesを基本データ型としているため、本文の
アルゴリズムには前節の \(x\) を消去した二重次数版を採用する方が整合的である。

## 8. 必要な仮定と注意点

論文では次を明記する必要がある。

- \(Y\) と \(\Gamma_f\) はintegralで、\(R\) はdomainである。
- \(\gamma\) は非零であり、\(D_+(\gamma)\) は稠密である。
- Corollary 4.3のboundが正しく、計算されたHom strandが本当に \(C\) である。
- \(c_i\) は \(C\) を斉次 \(k\)-代数として生成し、\(\deg c_i>0\) である。
- non-standard gradingおよびweighted projective spaceでも、指数
  \(t^{\deg c_i}\) を使う。
- suppliedまたはheuristic boundから得た結果については、boundが十分大きいと
  いう条件付きでのみ命題を適用できる。
- 「局所化がirrelevant idealで飽和する」とは書かない。正確には、kernelを
  \(R_\gamma[t]\) で取ることが、\(D_+(\gamma)\) 上のグラフの閉包、または
  \(\gamma\) に関するcontractionを計算する。

## 9. 実装後に必要な検証

単に `isPrime` と `isHomogeneous` を調べるだけでは不十分である。少なくとも次を
自動テストする。

1. 出力グラフ環のKrull次元が期待値 \(\dim Y+2\) である。
2. source側へのeliminationが \(Y\) の定義イデアルを返す。
3. target側へのeliminationが \(C\) の定義イデアルを返す。
4. 第一射影が \(Y\) と同型である。
5. 計算された写像について \(g\circ h=f\) が成り立つ。
6. 恒等写像、有限写像、正次元連結ファイバー、divisorial contraction、
   weighted source、非自由な有限 \(A\)-moduleの各例が通る。
7. 異なる非零 \(\gamma\) を選んでも、biprojective saturation後に同じグラフを
   得る。

## 10. 参考資料

- [Yasuda, arXiv:2603.13703v2](https://arxiv.org/abs/2603.13703)
- [論文PDF](https://arxiv.org/pdf/2603.13703)
- [Stacks Project, Proposition 41.6.1：separated morphismのgraphはclosed](https://stacks.math.columbia.edu/tag/024T)
- [Stacks Project, Section 27.12：morphisms into Proj](https://stacks.math.columbia.edu/tag/01N4)
