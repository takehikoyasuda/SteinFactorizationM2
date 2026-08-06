# マニュアル・コード修正方針

対象リビジョン: `8dd83d3`（`codex/review-by-chatgpt` ブランチ）

作成日: 2026-08-07

`MANUAL-REVIEW-BY-CHATGPT.md` の指摘を精査し、どれを取り入れ、どれを取り入れ
ないかを決めた作業計画である。この文書自体はコードもマニュアルも変更しない。
指摘の各項目は現物（`SteinFactorization.m2` の実装部と `doc` ブロック、
`tests/`、`README.md`）に当たって真偽を確認したうえで判定した。

## 全体方針

1. **誤りを直すことを最優先にする。** 名前・語彙・構成の改善はその後。読者を
   誤らせる記述（証明していないものを「certify」と呼ぶ、次数2の射を同型と呼ぶ）
   は、プロトタイプであることを理由に据え置いてよい類のものではない。
2. **API の変更は、数学的な内容が変わるものか、誤用を防ぐものに限る。** 引数の
   並べ替えやオプション化は、それ自体では正しさを増やさず、`README.md`・
   `IMPLEMENTATION.tex`・`tests/` の三箇所に波及する。見送るものは見送る。
3. **記法は論文に合わせたままにする。** `S`, `r`, `B`, `I` は Yasuda (2026) の
   記号であり、`Inputs` 節で説明されている。`ambientRing`, `truncationBound` へ
   の一括改名は例を冗長にするだけで情報を増やさない。ただし**同じ物が三通りに
   綴られている**のは別問題で、これは直す。

---

## 採用する修正

### A. 誤りの訂正（最優先）

#### A-1. `certifyChartwiseProjectionIsomorphism` の証明書を実態に合わせる

**指摘は正しい。** [SteinFactorization.m2:484-498](SteinFactorization.m2#L484-L498)
の実装は (i) `coverElements` が `Proj(sourceRing)` を被覆すること、(ii) 各
`chartMapPairs` の二本の環準同型が互いに逆であること、の二つしか検査していない。
にもかかわらず戻り値には

```m2
"overlapCompatibilityCertified" => true,
"projectionIsomorphismCertified" => true
```

が無条件で入る。前者は同じページの `Caveat`（重なりは検査しないと書いてある）
と正面から矛盾する。後者も、被覆元と写像対の対応も、写像の始域・終域が
`sourceRing` の局所化や `directSteinGraph` の出力と関係することも検査していない
以上、根拠がない。`#coverElements == #chartMapPairs` すら見ていない。

変更内容:

- 戻り値から `"overlapCompatibilityCertified"` と
  `"projectionIsomorphismCertified"` を**削除する**。残すのは
  `"coverCertified"`, `"localIsomorphismsCertified"`, `"numberOfCharts"`。
- 関数名を実態に合わせて改める。案は `checkChartwiseInverses`（採用推奨）、
  `verifyChartwiseInversePairs`。レビューの
  `checkInverseRingMapPairsOnProjectiveCover` は正確だが長すぎる。
- `#coverElements != #chartMapPairs` をエラーにする。安価で、対応の取り違えの
  うち一番よくある形は捕まえられる。
- ページの見出しと本文から「certify」を外し、「呼び出し側が用意したチャートに
  ついて、被覆と逆写像の恒等式だけを確かめる補助関数である。チャートを
  `directSteinGraph` の出力と同一視する責任は呼び出し側にある」と明記する。
- 例の `y0`/`y1` のずれを直す。本文は最初の写像対を「$y_1\neq0$ のチャート」と
  説明しているのに、渡している被覆元の先頭は `y0`。被覆元を `{y1,y0}` の順に
  するのが最小の修正。
- [tests/basic.m2:171](tests/basic.m2#L171) の
  `assert(mixedChartCertificate#"projectionIsomorphismCertified")` を
  `"coverCertified"` と `"localIsomorphismsCertified"` への assertion に置き換える。
- [MANUAL-REVIEW.md](MANUAL-REVIEW.md) の該当行のページ名を更新する。

**本物の証明書に作り直す案は採らない。** 各チャートについて被覆元・源の局所化・
グラフの局所化・射影・逆射を束ねた入力型を設計し、構造写像と重なりまで検査する
のは、この関数一つの改修ではなく新しい設計である。プロトタイプの現段階では、
「弱い検査を弱いと名乗る」ほうが「強い検査を装う」より正しい。将来やるなら
`MANUAL-REVIEW.md` の open questions に積む。

#### A-2. 重み付き標的の例は同型ではない

**指摘は正しい。** [SteinFactorization.m2:1041](SteinFactorization.m2#L1041) は
$(r_0,r_1^2)$ による $\mathbb{P}^1\to\mathbb{P}(1,2)$ を同型と呼んでいるが、これは
次数2である。$y_0\neq0$ のチャートで $\mathbb{P}(1,2)$ の座標は $u=y_1/y_0^2$ で、
その引き戻しは $(r_1/r_0)^2$。$\mathbb{P}(1,2)\cong\mathbb{P}^1$ を
$[y_0:y_1]\mapsto[y_0^2:y_1]$ で書けば合成は $t\mapsto t^2$ になる。

そもそも $e=1$ でこの形の写像が同型になることはない。$h_0$ が1次、$h_1$ が2次で
共通零点を持たないなら、合成は必ず $[h_0^2:h_1]$ という次数2の写像である。

変更内容:

- ページの説明を「$(r_0,r_1^2)$ による $\mathbb{P}^1\to\mathbb{P}(1,2)$ の次数2の
  射」に改める。
- 重み付き標的のチャートの読み方を一行足す。「$y_0\neq0$ 上の座標は
  $y_1/y_0^2$」とだけ書けば、次数の比例条件（写像が定義されるための条件）と
  射の次数が別物であることが読者に伝わる。
- 共通倍率 $e$ の幾何的な意味も一行。比例していることは写像が well-defined で
  あることしか意味せず、有限性・双有理性・同型性は何も言わない。
- [tests/weighted.m2:81-83](tests/weighted.m2#L81-L83) の Test 5 のコメントを同様に
  訂正する。テストの assertion 自体（base point free、次数、斉次性、素性）は
  正しく、同型であることは一つも主張していないので、変更は不要。
- 同型の例が欲しければ Test 2 の $\mathbb{P}(1,2)\to\mathbb{P}^1$, $(y_0^2,y_1)$
  がすでにある。ページからそちらに言及するだけでよい。

`README.md` の「an isomorphism and a degree-two map out of `P(1,2)`」は重み付き
**源**の Test 2・Test 3 を指しており、正しい。変更しない。

#### A-3. 無条件の真偽値というパターンそのものを見直す（レビュー未指摘）

レビューは `certifyChartwiseProjectionIsomorphism` だけを挙げているが、同じ形が
二箇所ある。

- [SteinFactorization.m2:442](SteinFactorization.m2#L442):
  `certifiedWeightedGraph` の `"projectionIsomorphismCertified" => true`。
  こちらは**主張としては正しい**（射の graph は源に同型に射影し、base point
  freeness は実際に検査している）が、計算した結果のように見える鍵名が誤解を
  招く。`"projectionIsomorphismByConstruction"` に改名するか、`Outputs` に
  「構成から従う事実であって、この呼び出しが検査した結果ではない」と明記する。
- [SteinFactorization.m2:380](SteinFactorization.m2#L380):
  `directSteinGraph` の `"saturationByLocalization" => true`。同じく手法の宣言で
  あって検査結果ではない。`Outputs` でそう述べる。

### B. 前提条件と検証（次点）

#### B-1. トップページに「Assumptions」段落を置く

**指摘は正しい。** [SteinFactorization.m2:1175](SteinFactorization.m2#L1175) 付近の
`evaluateSteinGenerators` の議論は「$R$ は整域である、$\Gamma_f$ が variety だから」
に依存しているが、`steinHomData` は素性を検査せず、`Inputs` は「bihomogeneous
ideal」としか要求していない。トップページが「variety」と呼んでいるのは意図の
表明としては読めるが、API の前提条件としては間接的すぎる。

トップページに短い段落を足し、主要な入口からリンクする。書くべきこと:

| 前提 | 検査するか |
|---|---|
| 係数環が体 | 検査しない（`pushForward` などが暗黙に要求） |
| `Igraph` が素（$R$ が整域） | **検査しない**。Lemma 5.2 の単射性がこれに依存 |
| 二つのブロックへの分解 | `blockDegreeData` が検査する |
| 入力が本当に射のグラフであること | 検査しない（`certifiedHomogeneousGraph` 経由なら構成から従う） |
| 標数 | 制限は課していない |

`evaluateSteinGenerators` のページでは、単射性を無条件の事実として書かず、
整域性の仮定の下での事実として書く。

#### B-2. 安価な入力検証を足す

対応しているはずの引数どうしの整合は、多くの箇所で信用されているだけである。
**安価に確かめられるものだけ**を検査し、残りは `Caveat` で呼び出し側の責任だと
明言する。

検査する:

- `steinHomDataAtBound`: `r` が長さ2の整数リストであること。
- `steinDataByStabilization`: `startBound` が長さ2、`hilbertMax >= 0`、および
  `requiredMatches > maxSteps - 1` が原理的に成功しえない組み合わせであること
  （現状 [SteinFactorization.m2:301-302](SteinFactorization.m2#L301-L302) は
  `maxSteps >= 2` と `requiredMatches >= 1` しか見ていない）。
- `selectCertifiedGraphComponent`: 各候補が `certified#"productRing"` のイデアル
  であること（`ring candidates#i === pp`）。
- `directSteinGraph`: `algebraData` が同じ `homData` 由来であること。
  `coefficientRing (algebraData#"localizationPresentation") === homData#"ring"`
  で環の同一性まで見られる。安価。
- `bigradedGlobalHomData`: `ring M === ring N`。
- `steinCoordinateAlgebra` と `evaluateSteinGenerators`: `evaluationElementIndex`
  が有効な範囲にあること、選ばれた $\gamma$ が零でないこと。現状は範囲外なら
  M2 の添字エラーが出るだけで、何が悪いか読者に伝わらない。

検査しない（`Caveat` に書く）:

- `NS` が制限後の `N` を本当に表現していること。これを確かめるのは
  `bigradedGlobalHomData` がやろうとしている計算と同程度に高くつく。

#### B-3. `steinCoordinateAlgebra` の一引数形を足す

**指摘は妥当。** 得られる部分環は $\gamma$ の選び方によらないとページ自身が
書いており、実際に全ての例が `0` を渡している。主要な三段の呼び出しのまん中に、
数学的内容のない実装上の選択が露出している。

```m2
algebraData = steinCoordinateAlgebra homData          -- 新設、既定で 0
algebraData = steinCoordinateAlgebra(homData, 3)      -- 既存、そのまま残す
```

- 実装は `method()` への変更が要る（現状は単なる関数値の代入なので arity で
  分岐できない）。ドキュメントの `Key` を
  `(steinCoordinateAlgebra, HashTable)` / `(steinCoordinateAlgebra, HashTable, ZZ)`
  に割るかどうかは実装時に決める。
- レビューの `EvaluationElementIndex => 0` というオプション形は**採らない**。
  二引数形がすでに expert 向けの入口として機能しており、`method(Options=>...)`
  への書き換えは正味の利得がない。
- `evaluateSteinGenerators` は添字が意味を持つ低水準関数なので、引数は必須の
  まま残す。
- 波及: `README.md` の三段ワークフロー、`IMPLEMENTATION.tex:142` と `:188`。

### C. マニュアルの読みやすさ

#### C-1. トップページに end-to-end の例を置く

現状、新しい読者は三つのページを回って呼び出しの順序を自分で組み立てる必要が
ある。二乗写像で三行の例を置き、主要な結果が入っている三つの鍵（確定した
bound、$Z$ の座標環、$h$ のグラフイデアル）を示す。読む順序をここで確立する。

#### C-2. 戻り値のハッシュテーブルの鍵を表にする

**指摘は妥当だが、そのままは採らない。** 全ての鍵を網羅的に文書化すると、
プロトタイプの内部表現を仕様として固定してしまう。代わりに各ページの `Outputs`
に「公開の鍵」の表（鍵・型・意味）を置き、それ以外は内部用であって将来変わりうる
と一行で断る。

優先して書くべきもの:

- `steinHomData`: `homModule`（非負象限に切り詰めたもの）と
  `steinGeneratorIndices`（$(0,\ge0)$-strand に落ちる添字）の区別。ここは今
  一番混乱しやすい。
- `steinCoordinateAlgebra`: `images`, `baseInclusion`, `extraHomIndices`。
- `directSteinGraph`: `jointRing`, `graphIdeal`, `graphMap`、および A-3 の
  `saturationByLocalization`。
- `steinDataByStabilization`: `history` の各項の構造と `consecutiveMatches`。
- `certifiedHomogeneousGraph` / `certifiedWeightedGraph`: `basePointFree` が何を
  検査した結果か、A-3 の鍵が何を意味するか。
- `bigradedGlobalHomData`: `sourceResolution` が `LengthLimit=>0` で要求した
  自由被覆でしかないこと（[SteinFactorization.m2:115-119](SteinFactorization.m2#L115-L119)
  のコメントはそう言っているが、ページは言っていない）。

`README.md:94` の「both resolutions」も同じ理由で不正確。源側は自由被覆である。

#### C-3. `steinCoordinateAlgebra` に基本例を前置する

現在の円錐標的の例は、多項式環でない基底環と自由でない有限加群を同時に見せる
点で数学的に価値があり、直前のコミット `f8473b6` で意図的に入ったものなので
**残す**。ただしこの中心的な関数の最初の操作例としては重い。

- `steinHomData` の二乗写像の例を数行で continue し、`ring` と
  `definingIdeal` を見せる基本例を前に置く。
- 現在の例は「advanced example: $A$ 上自由でない場合」の小節に降ろす。
- 「the first of these modulo the second」は出力の並び順に依存した言い方なので、
  `polynomialRing / definingIdeal` と明示する。
- $C_n=k[u,v]_{4n}$ の段落は、$A$ が何か / $C$ が何か / なぜ1次の加群生成元が
  二つ $A$ に足りないのか / 表示の列が何を意味するか、に分ける。
- `Caveat` の「has not been run to completion」が、既知の正しさの限界なのか、
  時間切れなのか、単に高くつくだけなのかを書き分ける。

#### C-4. コメントアウトされた `Text` ブロックの処理

三箇所ある（[:581-585](SteinFactorization.m2#L581-L585),
[:646-656](SteinFactorization.m2#L646-L656), [:675](SteinFactorization.m2#L675)）。
一律に削除はしない。

- `:581-585`（Corollary 4.3 の四つの数を渡さない理由）は `blockDegreeData` の
  ページに同じ説明があるので**削除**。
- `:646-656`（$A$ が引数でない理由、$C$ が $A$ より大きいことが要点である
  こと）は今もページに書かれていない有用な内容なので、**通常の散文として復活**
  させる。後者は特にこの関数の存在理由そのものである。
- `:675` は文の断片なので削除。

#### C-5. ページごとの細かい訂正

| ページ | 変更 |
|---|---|
| トップ | 「geometrically connected fibres」と書く（$h_*\mathcal{O}_Y=\mathcal{O}_Z$ が与えるのはこちら）。第一ブロックが $Y$（$\Gamma_f$）の射影埋め込み、第二が $X$ だと明示する |
| `steinHomData` | 有界分解の計算コストを例の前に述べ、`steinHomDataAtBound` へのリンクを張る |
| `directSteinGraph` | 「Working over $R[1/\gamma]$ ... is what saturates the result」を、何に関する飽和で何の閉包が得られるのかまで書き下す。例のグラフイデアルを解釈し、どの新しい座標が余分な Stein 生成元かを示す |
| `blockDegreeData` | 入力が多項式環に限るのかどうかを述べる（実装は次数しか見ないので商環でも動く） |
| `steinHomDataAtBound` | `r` が長さ2の整数リストであること、「large enough」がどの半順序かを述べる。この小さい例で `steinHomData(S,Igraph)#"bound"` との一致を実際に表示する。「out of reach」という機械依存の絶対的表現を、再現できる観測に置き換える |
| `steinDataByStabilization` | 第一座標しか増やさない探索方向の制限を `Caveat` に移し、なぜそれが適切かを述べる。fingerprint が次元・有限個の Hilbert 値・加群生成元次数からなる理由と、見落としうる変化を挙げる。`chosenBound` が「最後に試した bound」であることを一般の出力説明にも書く（現在は例の中でしか言っていない）。「that is the only place it can be checked」は言い過ぎなので「独立に確定できる場合に対する健全性検査」と書く |
| `certifiedHomogeneousGraph` | `hImages` は `B` の代表元を受け取り `B/I` で解釈する、と書く（実装は `sub` している）。`steinHomData` への受け渡しを例で示す |
| `certifiedWeightedGraph` | A-2 に加え、次数が比例しない入力が拒否される例を足す。ただし `Example` の中でエラーを起こすとドキュメントのビルドが落ちるので、`try` で包むか散文で述べるかを実装時に選ぶ |
| `selectCertifiedGraphComponent` | 候補を生成するのはこのパッケージではなく、これは選ぶだけだと述べる。イデアルは飽和の後で比較されるので、返る添字が同定するのは biprojective な部分スキームであってイデアルそのものの一致ではない、と述べる。`Usage` の出力名 `i` を `candidateIndex` にする |
| `bigradedGlobalHomData` | `R^{{1,1}}` の符号の向きを説明し、bound がどう動くはずかを数値で予告してから例を出す |
| `Bibliography` | Stacks Project のリンクを Stein factorization の該当タグに変える（レビューは 03GX を挙げている。**要確認**）。Smith (2000) に DOI か安定リンクを足す（**要確認**）。番号付き結果が arXiv v2 に紐づいていることを明記する |

### D. 文書間の整合

- `README.md`: 「both resolutions」を訂正（C-2）。三段ワークフローを
  `steinCoordinateAlgebra homData` に更新（B-3）。`IGraph` の綴りを統一。
- `IMPLEMENTATION.tex`: 同じく `evaluationElementIndex` の扱い（`:142`, `:188`）。
- 記号の統一。同じ物が現在 `igraph`（実装の仮引数）・`Igraph`（マニュアル）・
  `IGraph`（README）・`graphIdeal`（ハッシュの鍵）の四通りに書かれている。
  **マニュアルと README の使用例では `Igraph`、ハッシュの鍵は `graphIdeal`** に
  揃える。`NS`（マニュアル）と `NoverS`（README）も `NS` に揃える。
- M2 のバージョン: **最低要求バージョンと、計測・出力確認に使ったバージョンを
  分けて書く**。`README.md` は「1.24.11 or later」、`IMPLEMENTATION.tex` は
  1.24.11 での計測を記録しているが、現在の環境と `make docs` は 1.26.06。
  タイミングは 1.26.06 で取り直すか、1.24.11 での計測だと明記する。
- `newPackage` に `HomePage` を足し、`insufficient citation data: howpublished`
  の警告をなくす。

---

## 採用しない指摘

| 指摘 | 判断 | 理由 |
|---|---|---|
| `certifyChartwiseProjectionIsomorphism` を本物の証明書に作り直す | 見送り | 各チャートで被覆元・源の局所化・グラフの局所化・射影・逆射を束ねる入力型の設計が要る。一関数の改修ではなく新設計であり、現段階では「弱い検査だと名乗る」（A-1）で足りる。open questions に積む |
| `steinDataByStabilization` の三つの調整引数をオプション化 | 見送り | 位置引数6個が読みにくいのは事実だが、`method(Options=>...)` への書き換えが `README.md`・`IMPLEMENTATION.tex`・`tests/` に波及し、数学的な利得はゼロ。代わりに不可能な組み合わせの検査（B-2）と `Caveat` の整備（C-5）で実害を潰す |
| `S`→`ambientRing`, `r`→`truncationBound`, `B`, `I` などの一括改名 | 不採用 | 論文の記号であり `Inputs` で説明済み。改名は例を冗長にするだけで、読者が `Inputs` を読み返す手間は変わらない。ただし**同一物の綴りの不統一は別問題**として直す（D） |
| `NS`→`targetOverAmbient` | 不採用（統一のみ採用） | 同上。`README.md` の `NoverS` を `NS` に寄せる |
| `evaluateSteinGenerators` が Hom 次数と評価値の組を返す | 不採用 | 表示の都合で公開関数の返り値の型を変えることになる。次数は `homData#"steinGeneratorDegrees"` に同じ順序で既にある |
| `blockDegreeData` の例の出力 `{1,1,2,2}` / `{1,1,3,2}` を散文にも書く | 見送り | 出力は例の直下に表示される。重み付きのほうは散文が既に $c_1=1+2=3$ と述べており、そこだけで足りる |
| ドキュメントからテストファイル名への参照をやめる | 部分採用 | 参照自体は有用（リポジトリは公開されている）なので残す。ただし**数学的な要点はページ本文に書き、テストへの参照は補足に留める**という原則は採る |
| `evaluateSteinGenerators` の「最初の生成元は $y_1$」が生成元の順序に依存する件 | 部分採用 | 例が `(gens homData#"truncation")_(0,0)` を実際に表示してから「so $\gamma=y_1$」と言っているので、prose が出力に先行してはいない。ただし M2 の版が変われば散文だけ古くなる。今回は直さず `MANUAL-REVIEW.md` の open questions に記録する |
| 全ての鍵を網羅した表を全ページに置く | 部分採用 | 内部表現を仕様として固定してしまう。公開の鍵だけを表にし、残りは内部用と断る（C-2） |

---

## 作業順序

1. **A-1**: `certifyChartwiseProjectionIsomorphism` の鍵・名前・例・テストの訂正。
2. **A-2**: 重み付き標的の例とテストコメントの訂正。
3. **A-3**: 他の二箇所の無条件真偽値の扱いを決める。
4. **B-1**: トップページの Assumptions と、各入口からのリンク。
5. **B-3**: `steinCoordinateAlgebra` の一引数形（`README.md`・
   `IMPLEMENTATION.tex` の波及を含む）。
6. **B-2**: 安価な入力検証。
7. **C-1**, **C-3**, **C-4**: トップページの end-to-end 例、
   `steinCoordinateAlgebra` の基本例、コメントアウト部の処理。
8. **C-2**: 各ページの鍵の表。
9. **C-5**, **D**: 細かい訂正、記号の統一、文献、バージョン、`HomePage`。
10. `make docs-all` で再ビルドし、レンダリングされた全ページを読み直す。
    `MANUAL-REVIEW.md` を、各ページがどのリビジョンで受理されたかで更新する。

1〜3 と 5 はコードに触るので、その都度 `./run-tests.sh` を通す。

## 検証

- 各段階で `make docs`（例が走ることの確認）と `./run-tests.sh`。
- `A-1` と `B-3` はテストの assertion と呼び出し形を変えるので、テストの変更が
  意図した変更だけであることを diff で確認する。
- 最後に `make docs-all` の出力に警告が残っていないこと（D の `HomePage`）。

## `MANUAL-REVIEW.md` の扱い

今回のレビューはどのページも受理していない。加えて `steinHomData` は受理後の
コミットで散文が変わっているので、受理リビジョンは古い。上記の作業が済んだ
時点で全ページを読み直し、受理リビジョンを付け直す。

open questions に積むもの:

- `certifyChartwiseProjectionIsomorphism` を本物のチャート証明書にする設計。
- `evaluateSteinGenerators` の例が M2 の生成元順序に依存している件。
- `IMPLEMENTATION.tex` 第2節とパッケージドキュメントの重複（既出）。
