# 技術ノート

- `SteinFactorizationM2-note.tex`: English LaTeX manuscript
- `SteinFactorizationM2-note.pdf`: 生成済みPDF
- `index.html`: MathJax付きのウェブ版。関数ごとのコード表示とCopyボタンを含む。

LuaLaTeXでビルドする。

```sh
TEXMFVAR=/tmp/yasuda-texmf-var \
TEXMFCONFIG=/tmp/yasuda-texmf-config \
lualatex -interaction=nonstopmode SteinFactorizationM2-note.tex
```

The manuscript summarizes the current Macaulay2 implementation, test examples,
Hilbert functions, graph primality checks, fiber-component counts, and notes on
using AI during implementation.
