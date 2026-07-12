# 技術ノート

- `YasudaSteinM2-note.tex`: 日本語LaTeX原稿
- `YasudaSteinM2-note.pdf`: 生成済みPDF

LuaLaTeXでビルドする。

```sh
TEXMFVAR=/tmp/yasuda-texmf-var \
TEXMFCONFIG=/tmp/yasuda-texmf-config \
lualatex -interaction=nonstopmode YasudaSteinM2-note.tex
```

The manuscript summarizes the current Macaulay2 implementation, test examples,
Hilbert functions, graph primality checks, fiber-component counts, and notes on
using AI during implementation.
