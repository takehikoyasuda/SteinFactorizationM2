# Yasuda の Stein factorization アルゴリズム：Macaulay2 実装計画

## 1. 一次資料と訂正

対象は Takehiko Yasuda, *An algorithm for the minimal model program in dimension three*, arXiv:2603.13703v2 (2026-04-04), 26 pp. である。依頼文の「安田健彦」ではなく、論文の著者表記は **Takehiko Yasuda** である。

該当箇所は §4（bigraded global Hom）、§5（Stein factorization）、末尾の Algorithm 1。直接の結論は Proposition 5.4 で、その根拠は Corollary 4.3 と Lemmas 5.1–5.3 である。

## 2. 入力と仮定

基礎体は論文全体では代数的数全体の体 `k = Qbar`。実装第一段階では Macaulay2 が安定して扱える `QQ` または明示的な有限代数拡大を使う。

入力は、重み付き射影多様体として与えた integral projective schemes

- `Y = Proj B`, `B = k[y]/q`;
- `X = Proj A`, `A = k[x]/p`;
- 全射 `f : Y -> X` のグラフ `Gamma_f = Proj R`;
- `R = (B tensor A)/t`（`y` 次数 `(positive,0)`、`x` 次数 `(0,positive)`）

である。論文ではこれを “surjective graph morphism of monograded varieties” と呼ぶ。非全射の場合は先に scheme-theoretic image で `X` を置換する。`Y,X` は variety、従って既約・被約・射影的であり、グラフ ideal は適切な bihomogeneous prime ideal と仮定される。

## 3. 正確な代数的翻訳

`S = k[y_0,...,y_n,x_0,...,x_m]` を上記の二重次数付き多項式環、`R=S/I_Gamma` とする。Stein 中間項は

`Z = Spec_X(f_* O_Y)`。

その homogeneous coordinate ring は

`C = direct_sum_{v>=0} H^0(X,(f_*O_Y)(v))`

である。Corollary 4.3 を `M=N=R` に適用すると

`C = Hom_R(R_{>=r},R)_{(0,>=0)}`

となる。ここで `R_{>=r} = direct_sum_{(a,b)>=(r1,r2)} R_(a,b)`（成分ごとの不等号）。十分な `r` は、`R` を **S-module として**取った minimal bigraded free resolution の shift から

`r >= max{ a_(d+1)(R), a_d(R), a_(|d|+1)(R), a_|d|(R) } - c + (1,1)`

で得る。`d=(n,m)`、`|d|=n+m`、`c=(sum deg(y_i),sum deg(x_j))`。ここで `a_(i1,i2)=(max first shifts in homological degree i1, max second shifts in degree i2)`。

次に非零 bihomogeneous `gamma in R_{>=r}` を取り、Lemma 5.2 の単射

`C -> R_gamma`, `psi |-> psi(gamma)/gamma`

を用いる。`C` の homogeneous A-module generators `psi_i` に対し

`C = A[psi_1(gamma)/gamma,...,psi_l(gamma)/gamma] subset R_gamma`。

したがって、新変数 `z_i` を加えた写像 `A[z_1,...,z_l] -> R[u]/(u gamma-1)` の kernel を elimination で計算すれば `C` の A-algebra presentation と有限射 `g:Z->X` が得られる。

最後に `Y x_Z?` ではなく、`Y x Z -> Y x X` による `Gamma_f` の inverse image `Gamma_tilde` を計算し、その reduced irreducible components のうち projection to `Y` が同型なものを一つ選ぶ。それが `h:Y->Z` のグラフである（Lemma 5.3）。Algorithm 1 の本文には “connected components” とあるが、§5.2 の議論は **reduced irreducible components** を使っているため、実装では primary/minimal-prime decomposition を採用するのが安全である。

## 4. Macaulay2 実装の分割

1. `validateInput`: 二重斉次性、prime/reduced、全射（elimination image）、graph projection を検査。
2. `yasudaBound`: `res(coker gens I_Gamma)` の shifts から上の `r` を計算。添付コードで実装済み。
3. `orthantTruncation`: `Truncations` package の `truncate({r1,r2},R^1)` により `R_{>=r}` の有限 presentation を作る。Macaulay2 1.13 以降は multidegree の成分ごとの順序を直接扱う。
4. `globalHomModule`: `Hom_R(R_{>=r},R)` を計算し、first degree `0` かつ second degree `>=0` の homogeneous generators を抽出する。試作ではここまで実装済み。次にこれを有限 A-module presentation として完全にパッケージ化する。
5. `coordinateAlgebra`: `gamma` 評価、局所化、kernel/elimination から `C` を生成。
6. `steinGraph`: base change ideal、`minimalPrimes radical`、projection-isomorphism test。
7. 結果を `SteinData => {C, AtoC, graphH, bound, diagnostics}` として返す。

添付の `SteinFactorizationPrototype.m2` は (2)–(4) と、有限二次写像について (5) の coordinate algebra 復元までを実行する。二次写像 `[s:t] -> [s^2:t^2]` では `C=QQ[X0,X1,z]/(X0*X1-z^2)` を自動的に得る。完全な Algorithm 1（任意入力、graph `h` の復元）にはまだ達していない。

## 5. テスト例

- 恒等写像 `P^1 -> P^1`: `Z=P^1`、`C=A`。
- 有限二次写像 `[s:t] |-> [s^2:t^2]`: Stein factorization は `Y --id--> Y -> X`。`C` は `A` 上 rank 2（一般点）になる。
- projection `P^1 x P^1 -> P^1`: fibers は geometrically connected、従って `Z=X`、`C=A`。
- 合成 `P^1 x P^1 -> P^1 -> P^1`（projection の後に二次写像）: 中間項は最初の `P^1`。connected-fiber 部と finite 部を同時に検査できる最重要 integration test。
- 重み付き例を一つ追加し、非標準 grading と bound 計算を回帰テストする。

各例で、`g o h=f`、`g` finite、一般 fiber の点数、`h_*O_Y=O_Z`（計算可能な次数範囲と Hilbert function）、既知の coordinate ring との同型を検査する。

## 6. 現実的なマイルストーン

- M1: standard bigraded (`deg y=(1,0), deg x=(0,1)`)・`QQ`・明示的グラフに限定して (3)(4) を完成。
- M2: `C` の algebra structure と有限射まで完成し、上の4例を通す。
- M3: graph `h` の自動選択まで実装し、Algorithm 1 全体を完成。
- M4: positive weights、有限代数拡大、入力検証、package化・documentation。

主要な残課題は `(0,>=0)` 部分を一般入力について有限 A-module presentation に落とす処理、および得られた algebra generators から graph `h` を自動復元する処理である。orthant truncation 自体は現行 Macaulay2 の `truncate` で直接計算できることを確認した。
