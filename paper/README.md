# Manuscript

Daniel Tubbenhauer, *Positivity in symmetric webs and block permanents*. The PDF and TeX are the author’s 17 November 2026 files. All figures are drawn in TikZ. The source includes its bibliography. [Paper](paper.pdf) · [Source](main.tex)

## Build

From this directory, use a TeX Live installation with the AMS classes, PGF/TikZ and latexmk.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is `main.pdf`. The supplied `paper.pdf` is the author’s build.

## Verification copy

The Lean index was prepared against the 16 November draft. The 17 November source changes “Both packets” to “The packets” in Example 3A.4 and splits a sentence at the start of Section 3B. All formulas, statement numbers and TeX line references carry over. Both drafts print the same intermediate equality in the proof of Lemma 5B.1. The erratum gives the corrected equality. [Erratum](../ERRATUM.md) · [Proof index](../ai/theorem-index.md)

The reverse patch recovers the precise TeX input used for Stage 40.

```sh
patch --silent -o stage-40.tex main.tex < stage-40-source.patch
```

| Input | SHA-256 |
| --- | --- |
| Stage 40 TeX, recovered with the patch | `d74e3e35195f2a9c8d3d6dd7895afe5f098e8d78da7d761b536237302598ef39` |
| Stage 40 PDF used to check printed numbering | `79e1c7053b6966721f1aea3763c23a71f64e72389efe4db643e2c667a9238043` |
| Current TeX | `3f36e28e17db38eb4711229793e3264510ebd086f481f389fcc5920cff39a3b1` |
| Current PDF | `636575cb457c744ed0e47e887736c13c704094a12f2e3197e6b4b7a2bf323fc1` |
