# `SteinFactorization.m2` 簡潔なコードガイド

## 全体の流れ

このファイルは、射のグラフ環からStein因子分解の中間項を計算する。

```text
グラフ ideal → 二重次数付き環 R → Hom_R(R_{>=r},R)
             → Stein中間項の座標環 C → Stein写像のグラフ
```

中心となる対象は `C = Hom_R(R_{>=r},R)_(0,>=0)` である。

## 主要な関数

| 関数 | 役割 |
|---|---|
| `bigradedTruncationBound` | 自由分解のshiftからbigraded truncation boundを計算 |
| `steinHomData` | グラフ環、自由分解、Hom加群、Stein生成元を計算 |
| `steinHomDataAtBound` | boundを外から与える実験用の入口 |
| `evaluateSteinGenerators` | Hom生成元を`gamma`で評価 |
| `steinCoordinateAlgebra` | 評価結果のkernelからStein座標環を作る |
| `directSteinGraph` | Stein写像のグラフidealを作る |

## 計算の流れ

### 1. bound

`componentMax`、`shiftCoordinateMax`、`aPair`、`pairMax`は、bigraded自由分解のshiftの最大値を調べる補助関数である。`bigradedTruncationBound(ff,d1,d2,c1,c2)`が、bigraded版のshift boundに従って`{r1,r2}`を返す。

### 2. Hom加群

`steinHomData(S, graphIdeal, d1, d2, c1, c2)`は、次を順に行う。

1. `S/graphIdeal`をグラフ環`R`とする。
2. `R`のbigraded自由分解を計算する。
3. `R_{>=r}`を作る。
4. `Hom_R(R_{>=r},R)`を計算する。
5. 次数`(0,>=0)`の生成元を選ぶ。

結果のHashTableから、`data#"ring"`、`data#"bound"`、`data#"homModule"`、`data#"steinGeneratorDegrees"`などを取り出せる。

自由分解を省略する場合は、`steinHomDataAtBound(S, graphIdeal, {2,0})`を使う。この場合、`data#"certifiedBound"`は`false`になる。

### 3. Hom生成元の評価

`evaluateSteinGenerators(data,gammaIndex)`は、`R_{>=r}`の生成元`gamma`にHom写像を作用させ、`psi_i(gamma)`を計算する。Lemma 5.2に従い、座標関数としては`psi_i(gamma)/gamma`を使う。

### 4. Stein座標環

`steinCoordinateAlgebra(data, gammaIndex, baseImages)`は、`gamma`を可逆にした局所化環を作り、target側の座標とHom生成元をそこへ送る。その写像のkernelがStein中間項の定義idealになる。

主な出力は、`cData#"ring"`、`cData#"definingIdeal"`、`cData#"baseRing"`、`cData#"strandAsAModule"`である。二次写像では、例えば`QQ[X0,X1,z]/(X0*X1-z^2)`が得られる。

### 5. Stein写像のグラフ

`directSteinGraph(data,cData)`は、Hom生成元を局所化環の元に送り、Reesパラメータを加えてkernelを取る。`gData#"graphIdeal"`がStein写像のグラフidealである。

## その他の関数

- `certifiedHomogeneousGraph`：明示的な同次数の座標で定義された射のグラフを作り、base pointがないことを確認する。
- `selectCertifiedGraphComponent`：候補グラフから、既知の正しいグラフと一致する成分を選ぶ。
- `certifyChartwiseProjectionIsomorphism`：chartごとに環写像が互いに逆であることを確認する。
- `steinFingerprint`：次元、Hilbert関数、生成元次数をまとめる。
- `steinDataByStabilization`：boundを増やし、fingerprintの一致を調べる。ただし証明ではない。

## 典型的な3行

`data = steinHomData(...)`でHom加群を計算し、`cData = steinCoordinateAlgebra(...)`でStein中間項の座標環を作り、`gData = directSteinGraph(...)`でStein写像のグラフを作る。

## 注意点

- `steinHomData`は、自由分解からboundを計算する認証的な経路。
- `steinHomDataAtBound`は、boundを外から与える実験的な経路。
- `steinDataByStabilization`の安定化は、計算結果の一致を示すだけである。
- Hom加群の生成元には、代数生成元として冗長なものが含まれることがある。
- twisted cubicのblow-upでは、この冗長性のためグラフ構成が完全自動化されていない。
