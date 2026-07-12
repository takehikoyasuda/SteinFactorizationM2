# 実装状況

## 対応する論文箇所

- Definition 4.1: 自由分解のshift invariant
- Corollary 4.3: truncation bound
- §5.1: `C = Hom_R(R_{>=r},R)_(0,>=0)`
- Lemma 5.2: `psi -> psi(gamma)/gamma`
- Algorithm 1: Stein中間項とグラフの構成

## 実装済み

- 二重次数環とグラフidealを入力する汎用フロントエンド
- Corollary 4.3で必要なhomological degreeまでの自由分解
- `(0,>=0)` strandを有限 `A`-加群として構成
- Hom生成元からStein座標環を復元
- 局所化の縮約による直接グラフ閉包
- certified boundとsupplied/heuristic boundの区別

## 検証例

- `P1 -> P1` の二次・三次写像
- `P2 -> P2` の二次・三次Veronese型写像
- `P1 x P2 -> P2` のMori fiber space
- `Bl_L(P3) -> P3` のdivisorial contraction
- twisted cubicのブローアップ

## 現在の課題

1. 有限 `A`-加群生成元から冗長な代数生成元を除去する。
2. twisted-cubic例の明示bound自由分解を高速化する。
3. Macaulay2 package形式のdocumentationと公開APIを整える。
4. exact Algorithm 1方式（fiber productの成分選択）を代替strategyとして保持する。

