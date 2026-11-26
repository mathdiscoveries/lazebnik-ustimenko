# Exact Girths of Lazebnik–Ustimenko Graphs `D(k, q)`: Lean 4 + Mathlib Formalization

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490751.svg)](https://doi.org/10.5281/zenodo.24490751)

Unconditional Lean 4 (`v4.35.0`) + Mathlib (`v4.35.0`) formalization (208 audited declarations, zero `sorry`, zero `native_decide`, standard axioms `propext`, `Quot.sound`, `Classical.choice` only).

Companion manuscript, interactive Proof Blueprint, and verification archive:
<https://mathdiscoveries.org/results/lazebnik-ustimenko>

## Compared Theorems (`Challenge.lean` / `Solution.lean`)

### Results of the Companion Paper
1. `D9_D10_exact_girth_14_all_q_ge_4` — `girth D(9, F) = girth D(10, F) = 14` for every finite field `F` with `|F| ≥ 4` (closing characteristics 2 and 3, left open by Pikuta 2008).
2. `D9_D10_orig_exact_girth_14_all_q_ge_4` — same in the original DS28 minus-sign representation `DGraphOrig`.
3. `D9_D10_exact_girth_14_galoisField` — direct `GaloisField p n` instantiation for every prime power `p^n ≥ 4`.
4. `DS28_table7_blank_cells_27_32` — explicit closure of the four empty DS28 Table 7 cells `(9, 27), (10, 27), (9, 32), (10, 32)`.
5. `card_admissible_ge_two_of_card_ge_four` — at least 2 admissible cycle parameters in every finite field with `|F| ≥ 4`.
6. `D3_exact_girths_highlights` — unconditional kernel-verified exact ternary girths at `k = 15, 16 (20)`, `47, 48 (52)`, `55, 56 (60)`, `79, 80 (84)`, `99 (104)`, `103, 104 (108)`.
7. `D3_k52_bounds_56_60` — unconditional tightening `56 ≤ girth D(52, 3) ≤ 60`.

### Second Proof of the Earlier Binary Girth Law (Cheng, Chen, and Tang 2014)
The complete binary girth formula `girth D(k, 2) = 2^s` for all `k ≥ 2` was originally proved by X. Cheng, W. Chen, and Y. Tang (*Discrete Math.* **335** (2014), 25-34, `doi:10.1016/j.disc.2014.07.004`, Zbl 1298.05227) and quoted in M. Xu, X. Cheng, and Y. Tang (*Finite Fields Appl.* **92** (2023), 102296, Example 1). The companion paper (Proposition 13) proves that law a second time via an affine unipotent 4-step transition operator `T4(p) = (I + N)p + b` over `ZMod 2` in both sign models, and this repository formalizes that proof; the paper applies the law to refute the conflicting survey statement `D(k, 2) ≅ 2^(k-3) C_16` (`k ≥ 5`) in Lazebnik-Sun-Wang (2017) and Lazebnik-Wang DS28 (2026) for every `k ≥ 13`:

8. `D2_exact_girth_law` — independent Lean 4 proof of `girth D(k, 2) = 2^s` for `s ≥ 3` and `2^(s-1) - 4 < k ≤ 2^s - 4`.
9. `D2_exact_girth_orig_law` — same in `DGraphOrig`.
10. `D2_girth_gt_16_of_ge_13` — corollary refuting the `2^(k-3) C_16` claim: for all `k ≥ 13`, `girth D(k, 2) ≥ 32` and `D(k, 2)` contains no 16-cycle.

Coverage by this package's Palomar comparison, against the 5 main results the companion paper counts: 1 is compared in Lean in full (20%; the binary girth law, Proposition 13) and 2 in part (Theorem 5(b), girth 14 in dimensions 9 and 10, for every finite field with at least 4 elements but not for infinite fields; Theorem 11(a), 11 of the 27 exact ternary girths, plus `56 ≤ girth D(52, 3) ≤ 60`). The universal lower bound (Theorem 5(a)) and the other 16 ternary girths are proved in this package's Lean library but not compared; the ternary table through `k = 50` (Theorem 11(b)) combines Lean upper bounds with external search lower bounds and is not compared. Theorems 7 and 9 and Proposition 10 of the paper, outside its count of five, are not proved in this package (it has only Theorem 9's inputs from Theorem 5(b) and Proposition 13); Theorem 5(c), also outside the count, is in the library only as bridges that take the cited lifting theorems as hypotheses.

## Verification

```sh
lake build LazebnikUstimenko LazebnikUstimenko.Verify Challenge Solution
lake env lean LazebnikUstimenko/Verify.lean
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B. Hughes**. No human mathematician has yet refereed the proof. Licensed under Apache-2.0.
