# Yasuda の Stein 因子分解アルゴリズムに対する実装査読報告

査読日: 2026-07-27  
対象論文: Takehiko Yasuda, *An algorithm for the minimal model program in dimension three*, arXiv:2603.13703v2 (2026-04-04), 特に §4, §5, Algorithm 1  
対象実装: `SteinFactorization.m2` および `tests/*.m2`

## 1. 結論

結論を先に述べる。

**このコードは、Yasuda 論文の Stein 因子分解アルゴリズムのうち、数学的中核である §4 の bigraded global Hom の切断境界と、§5.1 の Stein 中間項の斉次座標環の計算を、かなり忠実に実装している。** とくに、Corollary 4.3 の境界を自由分解の shift から計算し、

\[
C=\operatorname{Hom}_R(R_{\ge r},R)_{0,\ge0}
\]

を有限計算に落とし、Lemma 5.2 の写像

\[
\psi\longmapsto \frac{\psi(\gamma)}{\gamma}
\]

によって (C) の (A)-代数表示を kernel 計算から復元する部分には、論文とコードの間に明瞭な一対一対応がある。標準テストと別扱いのベンチマークは、査読時に Macaulay2 1.24.11 上で全て成功した。

しかし、**リポジトリ全体を「論文の Algorithm 1 を、その入力クラス全体について実装済み」と認定することはできない。** 論文 Algorithm 1 の Step (2)--(4) は、ファイバー積の逆像を作り、その成分を計算し、(Y) への射影が同型である成分を探索する。現コードの主経路 `directSteinGraph` は、Hom 生成元を使う別の直接的なグラフ閉包であり、論文記載の成分探索を一般入力について実行してはいない。また、論文が前提とする「variety」「surjective graph morphism」等の入力条件も自動検査されない。

したがって、妥当な判定は次の通りである。

| 評価対象 | 判定 |
|---|---|
| Corollary 4.3 の Stein 特殊化の境界 | 実装されている |
| 一般の bigraded global Hom の基本経路 | 実装されているが、検証範囲は狭い |
| §5.1 の (C) の (A)-加群および (A)-代数表示 | 実装されている |
| Lemma 5.2 の局所化による評価 | 実装されている |
| Stein 中間項 (Z=\operatorname{Proj}C) の具体例での復元 | 強い計算証拠がある |
| Algorithm 1 Step (2)--(4) の一般的な成分探索 | 未実装 |
| `directSteinGraph` による代替グラフ構成 | 実装済みで、多数の例に成功。ただし一般正当性の認証機構は未完成 |
| 論文の入力仮定の自動検証 | 未実装 |
| 論文 Algorithm 1 の完全な汎用実装 | 未達 |

これは「でたらめなコード」という評価とは大きく異なる。中核部分には理論との精密な対応と非自明な回帰試験がある。一方で、現状を完成版 Algorithm 1 と呼ぶのも正確ではない。

## 2. 査読方法

本査読では、リポジトリ内の説明を根拠として自己循環的に正当化することを避け、次の順に確認した。

1. 論文 v2 の Definition 4.1, Proposition 4.2, Corollary 4.3, Lemmas 5.1--5.3, Proposition 5.4, Algorithm 1 を一次資料として読んだ。
2. 各数式を `SteinFactorization.m2` の関数と行単位で対応させた。
3. 実装が返す量が、単なる同名のデータではなく、論文の構成に必要な環・加群・写像になっているかを調べた。
4. 全ての標準テストと twisted-cubic ベンチマークを実行した。
5. テストが検証している命題と、検証していない命題を分けた。

一次資料は [arXiv abstract](https://arxiv.org/abs/2603.13703) および [v2 PDF](https://arxiv.org/pdf/2603.13703) である。

## 3. 論文と実装の詳細な対応

### 3.1 二重次数と自由分解の shift

論文 §4 では

\[
S=k[x_{1,0},\ldots,x_{1,d_1},x_{2,0},\ldots,x_{2,d_2}]
\]

に、第一ブロックを ((c_{1,t},0))、第二ブロックを ((0,c_{2,t})) とする二重次数を入れる。コードも、source block を `(positive,0)`、target block を `(0,positive)` とする規約を明記している。

Definition 4.1 の (a_{s,i}) は、最小自由分解の第 (i) 項に現れる shift の第 (s) 成分の最大値である。コードでは `shiftCoordinateMax(ff,i,k)` がこれを読み、`aPair(ff,i,j)` が

\[
\mathbf a_{(i,j)}=(a_{1,i},a_{2,j})
\]

を作る。ここで第一成分と第二成分に別々の homological degree を使う点は、論文のベクトル添字の定義に忠実である。単に各自由加群の bidegree をまとめて最大化しているのではない。

### 3.2 Corollary 4.3 の切断境界

論文の境界は

\[
r\ge
\max\{\mathbf a_{\mathbf d+\mathbf 1}({}_SN),
       \mathbf a_{\mathbf d}({}_SN),
       \mathbf a_{|\mathbf d|+1}({}_SN),
       \mathbf a_{|\mathbf d|}({}_SN)\}
-\mathbf c+\mathbf 1.
\]

Stein 因子分解では (M=N=R) である。`bigradedTruncationBound` は、順に

- `(d1+1,d2+1)`,
- `(d1,d2)`,
- `(d1+d2+1,d1+d2+1)`,
- `(d1+d2,d1+d2)`

の shift を取り、成分ごとの最大値から `(c1,c2)` を引き `(1,1)` を足している。この式は Corollary 4.3 の直訳である。

さらに `steinHomData` は、(R=S/I_{\Gamma_f}) を **(S)-加群として** `coker gens igraph` で表し、その最小自由分解を使う。これは重要である。論文の境界は (R)-自由分解ではなく、ambient polynomial ring (S) 上の自由分解の shift を読むからである。コードは必要な最大 homological degree (|\mathbf d|+1=d_1+d_2+1) までに計算を制限しており、式に必要な情報を失わず不要な tail を避けている。

この対応は単なるコメント上の一致ではない。たとえば二次写像 (\mathbf P^1\to\mathbf P^1) では `{1,0}`、三次写像では `{2,0}`、二次 (\mathbf P^2\to\mathbf P^2) では `{2,0}` が実際に得られ、既知の Stein 環の復元まで成功する。

### 3.3 (R_{\ge r}) と global Hom

論文 Corollary 4.3 は、成分ごとの順序で

\[
R_{\ge r}=\bigoplus_{v\ge r}R_v
\]

を取り、§5.1 で

\[
C=\operatorname{Hom}_R(R_{\ge r},R)_{0,\ge0}
\]

を得る。コードは `truncate(bound,rr^1)` により orthant truncation を作り、`Hom(truncation,rr^1,MinimalGenerators=>true)` を計算する。その後 `truncate({0,0},rawHomModule)` で非負 orthant を取り、第一次数が 0 の生成元を `isSteinDegree` で選ぶ。

第一次数 0 の部分が (A=R_{0,\ge0}) 上の加群になることも反映されている。`steinCoordinateAlgebra` は第一次数が正の部分を商で落とし、`pushForward(inclusionAtoR,zeroFirstStrand)` によって (A)-加群としての presentation を作る。論文 pp. 15--16 が自由加群の strand、lift、cokernel を使って有限 presentation を構成するのに対し、コードは Macaulay2 の restriction-of-scalars に相当する機能で同じ有限 (A)-加群を得ている。手続きの低水準表現は違うが、対象は一致している。

### 3.4 Lemma 5.2 と (A)-代数構造

論文は非零 homogeneous element (gamma\in R_{\ge r}) を選び、

\[
R_\gamma=R[u]/(u\gamma-1),\qquad \deg u=-\deg\gamma
\]

を作る。コードも truncation の生成元から `gamma` を選び、`steinInverse*gamma-1` を課して同じ局所化表示を作る。

各 Hom 生成元 (psi_i) に対し、`evaluationMatrix` の `(gammaIndex,i)` 成分は (psi_i(\gamma)) である。これに `steinInverse` を掛けた像が (psi_i(\gamma)/\gamma) になる。続いて

\[
A[z_1,\ldots,z_l]\longrightarrow R_\gamma
\]

の kernel を計算して `definingIdeal` としている。これは Lemma 5.2 の直後に論文が記述する (C) の (A)-代数表示そのものである。次数 ((0,0)) の生成元は単位なので追加変数から除く処理も正しい。

この箇所には、有限二次写像で

\[
\mathbf Q[X_0,X_1,z]/(X_0X_1-z^2)
\]

を得る明示的検査、三次写像で twisted cubic の三つの二次関係式を得る検査がある。単に次元や生成元数だけを見ているのではなく、既知の定義 ideal との等号を検査している点は強い証拠である。

### 3.5 (g:Z\to X)

`baseImages` から (A) の presentation を kernel で作り、同じ像を (C) の多項式表示の最初の変数群に置いている。したがって、得られる環準同型 (A\to C) は論文 Lemma 5.1 の有限射 (g:\operatorname{Proj}C\to\operatorname{Proj}A) を与える。

ただし、コードは `baseImages` が本当に (A=R_{0,\ge0}) を生成することを検証しない。正しい入力を利用者が与えた場合の構成は論文と一致するが、誤った部分生成系に対しても結果を返し得る。

## 4. グラフ (h:Y\to Z) の評価

ここが「中核実装」と「Algorithm 1 完成版」を分ける箇所である。

### 4.1 論文の方法

論文 §5.2 と Algorithm 1 は、概略次を行う。

1. (Y\times Z\to Y\times X) による (Gamma_f) の逆像 (widetilde\Gamma) を作る。
2. その成分を計算する。
3. 各成分について (Y) への射影が同型かを判定する。
4. 同型な成分を (Gamma_h) として返す。

本文 §5.2 は reduced irreducible components を用いる一方、末尾の Algorithm 1 は connected components と書いており、原稿内にも表現上のずれがある。しかし、いずれの読み方でも「逆像の成分を列挙し、射影同型性を判定する」ことが記載手順の中心である。

### 4.2 現コードの方法

主関数 `directSteinGraph` は、この成分探索をしない。代わりに、局所化環中の (C) の生成元へ Rees parameter による projective scaling を付け、環写像の kernel を取ってグラフ閉包を作る。

この発想は数学的に自然である。正しい前提の下では、Lemma 5.2 により (C\subset R_\gamma) があり、(Gamma_f\cong Y) の稠密開集合上で (Y\dashrightarrow\operatorname{Proj}C) の座標が得られる。その像の graph closure を kernel で取ることで (Gamma_h) を直接回収できると期待される。有限写像、正次元連結ファイバー、divisorial contraction のテストで prime graph ideal が得られることも、この解釈を支持する。

しかし、現実装には一般入力について次を自動証明する処理がない。

- 得られた bihomogeneous ideal が projective graph として不要成分を含まないこと。
- その (Y) への射影が同型であること。
- (g\circ h=f) が一般入力で成立すること。
- 異なる (gamma) の選択が同じ projective graph を返すこと。

`saturationByLocalization => true` は計算経路を記録するフラグであり、それ自体は上記命題の検査結果ではない。テストの `isPrime(graphIdeal)` も「prime である」ことを示すだけで、射影同型性までは示さない。

補助関数 `certifiedHomogeneousGraph`, `selectCertifiedGraphComponent`, `certifyChartwiseProjectionIsomorphism` は、既知の座標表示や利用者が与えた chartwise inverse maps に対して強い証明書を与える。ただし、候補成分や逆写像を一般入力から自動生成するものではない。したがって、これらは個別例の認証には有効だが、Algorithm 1 Step (2)--(4) の一般実装ではない。

## 5. テスト結果と証拠の強さ

### 5.1 実行結果

査読時に次を実行し、全て exit code 0 で終了した。

- `run-tests.sh`: identity, (\mathbf P^1) の二次・三次写像、混合例、(\mathbf P^2) の二次・三次写像、一般 global Hom の小例、Mori fiber space、直線の blow-up。
- `tests/blowup-twisted-cubic.m2`: twisted cubic の blow-up の別ベンチマーク。

### 5.2 非自明な検証内容

| 例 | 検証された内容 | 評価 |
|---|---|---|
| identity (\mathbf P^1\to\mathbf P^1) | bound `{0,0}`、追加 Hom 生成元なし | sanity check |
| square (\mathbf P^1\to\mathbf P^1) | bound `{1,0}`、conic ideal (X_0X_1-z^2) の完全一致 | 強い |
| cubic (\mathbf P^1\to\mathbf P^1) | bound `{2,0}`、twisted-cubic ideal の完全一致、(g\circ h=f) | 強い |
| (\mathbf P^1\times\mathbf P^1\to\mathbf P^1) | 正次元連結ファイバーを持つ mixed case、twisted cubic 中間項、4 charts 上の射影同型 | 強い個別認証 |
| square (\mathbf P^2\to\mathbf P^2) | Veronese surface の codimension, degree, 6 quadrics, Hilbert value | 強い |
| cube (\mathbf P^2\to\mathbf P^2) | 非標準出力と冗長生成元、Hilbert values、prime ideal | 中程度から強い |
| (\mathbf P^1\times\mathbf P^2\to\mathbf P^2) | 一般ファイバーが4個の (\mathbf P^1)、期待する Veronese 中間項 | 強い幾何学的回帰 |
| (\operatorname{Bl}_L\mathbf P^3\to\mathbf P^3) | divisorial contraction、例外因子、8点ファイバー、Veronese 中間項 | 強い幾何学的回帰 |
| (\operatorname{Bl}_C\mathbf P^3\to\mathbf P^3) | supplied bound 下の strand と低次数 Hilbert values | 実験的。認証済み bound ではない |

これらは、単一の玩具例に合わせて hard-code した実装ではないことを強く示す。特に、有限射だけでなく、正次元連結ファイバーと divisorial contraction が含まれている点は適切である。

### 5.3 テストからは言えないこと

有限個の例の成功は、任意の許容入力に対する正しさの証明ではない。現テスト群には次が不足している。

- 正の非標準 weight を本格的に使う例。
- (mathbf Q) 以外の有限代数拡大、まして論文の (\overline{\mathbf Q}) を有限データで扱う層。
- 不正入力を拒否する negative tests。
- (gamma) を変えた不変性試験。
- `directSteinGraph` の結果に対する自動的な (Y)-射影同型証明。
- 論文どおりの fiber-product component route との比較試験。
- 一般の (M,N) に対する Proposition 4.2/Corollary 4.3 の多様な module tests。

## 6. 主要な留保事項

### 6.1 入力仮定が未検査

論文は projective varieties、すなわち既約・被約な入力、および surjective graph morphism を前提とする。現 API は、少なくとも次を検査しない。

- graph ideal の bihomogeneity、primality、irrelevant locus に関する適切性。
- 第一射影が本当に (Gamma_f\cong Y) を与えること。
- (f) の全射性、または (X) を scheme-theoretic image に置換したこと。
- `d1,d2,c1,c2` が実際の変数個数・weight sum と一致すること。
- `baseImages` が target ring (A) 全体を生成すること。

このため、`certifiedBound => true` は「渡された数値と環が論文の規約を満たすと仮定したとき、自由分解から論文式で bound を計算した」という意味に限定して読むべきである。入力全体が認証済みという意味ではない。

### 6.2 supplied/heuristic bound は証明ではない

`steinHomDataAtBound` と `steinDataByStabilization` は `certifiedBound => false` を明示しており、この区別は良い設計である。twisted-cubic blow-up は `{2,0}` を外から与えており、得られた Hilbert values が期待値と一致するが、Corollary 4.3 の十分条件を計算したわけではない。この例を「論文アルゴリズムの完全な成功例」と数えてはならない。

### 6.3 一般 global Hom API の検証は限定的

`bigradedGlobalHomData` は Proposition 4.2 の (-\underline{\mathbf a}_0(M)) を組み込んでおり、target (N) を (S)-加群として明示的に渡す設計も正しい。ただしテストは diagonal structure sheaf とその shift にほぼ限られる。

また `sourceResolution := res sourceModule` は、実際には第0自由加群の下側 shift しか利用しないのに resolution 全体を要求している。商環上の一般加群では自由分解が長大または無限になり得るため、アルゴリズムの停止性・実用性を悪化させる可能性がある。少なくとも必要次数に制限するのが望ましい。

### 6.4 (gamma) と base generator の防御的検査

コードは `gammaIndex` で選ばれた元が非零であること、index が範囲内であること、局所化が意図した稠密開集合を与えることを明示検査しない。論文の正しい入力では非零 homogeneous (gamma) を選べるが、公開 API としては検査と明瞭な error message が必要である。

### 6.5 「prime」は「Stein graph の認証」ではない

複数のテストが `isPrime(graphIdeal)` を確認する。これは有用だが、prime graph ideal であることだけから、その射影が (Y) と同型であることや、連結ファイバー条件が従うわけではない。個別の cubic/mixed case には合成や chartwise inverse の追加検査があるが、全例共通の証明書ではない。

## 7. 数学者向けの信頼性評価

AI 生成コードに対する合理的な懸念は、主に次の三つである。

1. 記号を似せただけで、実際には別の対象を計算している。
2. 玩具例だけを通し、一般構造を反映していない。
3. 成功した計算を数学的証明と混同する。

本実装は、第1の懸念にはかなりよく応えている。(S)-加群としての自由分解、四つの shift vector、orthant truncation、第一次数0の strand、(psi(\gamma)/\gamma)、kernel による (A)-代数表示という、間違えやすい要点が論文どおり接続されている。

第2の懸念にも相当程度応えている。曲線の有限写像だけでなく、曲面、三次元の blow-up、正次元ファイバーを含む例がある。既知 ideal の完全一致、Hilbert 関数、degree、fiber decomposition、chartwise inverse maps など、相互に異なる不変量を検査している。

一方、第3の懸念については、コード自身は `certifiedBound` の区別など慎重な設計をしているものの、README の「direct graph closure」「regression examples」という記述だけを読んで Algorithm 1 全体が完成したと解釈する余地がある。本報告の最大の留保はここである。**計算核の正しさを支持する証拠は強いが、一般入力に対する完全性の証明書はまだない。**

## 8. 完全実装と認定するための推奨事項

優先順位順に次を推奨する。

1. `validateSteinInput` を実装し、bihomogeneity、prime/reduced、graph projection、surjectivity、weight data、`baseImages` の生成性を検査する。
2. 論文 Algorithm 1 の fiber-product inverse image、reduced irreducible component 分解、(Y) への射影同型判定を一般関数として実装する。
3. `directSteinGraph` を高速な代替 strategy と位置付け、その出力に対し chartwise あるいは環論的に projection isomorphism と (g\circ h=f) を認証する。
4. exact component strategy と direct strategy が同じ saturated graph ideal を返す回帰試験を、小さな複数例で追加する。
5. non-standard positive weights と代数的数体の例を追加する。
6. `gammaIndex`、非零性、base generator completeness に防御的検査を加える。
7. 一般 global Hom では source resolution を必要部分までに制限し、非自明な (M,N) の試験を増やす。
8. twisted-cubic blow-up について Corollary 4.3 の certified bound を実際に計算するか、別の数学的証明で supplied bound を認証する。

## 9. 最終判定

本実装について、次の二文を同時に述べるのが最も正確である。

> Yasuda 論文 §4 と §5.1 に基づく Stein 座標環計算は、数式とコードの対応、実行結果、既知例との比較から見て、実質的かつ説得力をもって実現されている。

> しかし、論文 Algorithm 1 の全手順を、論文の全入力仮定を検査しながら一般入力に対して実行する完成実装ではない。特に、Step (2)--(4) の成分探索と射影同型判定は、現状では直接グラフ構成と個別例の証明書に置き換えられている。

従って査読判定は、**「中核アルゴリズムは実装済み、完全な Algorithm 1 は major revision を要する」** とする。
