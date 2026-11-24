# Exact Girths of Lazebnik–Ustimenko Graphs `D(k, q)`: Lean 4 + Mathlib Formalization

Unconditional Lean 4 (`v4.35.0`) + Mathlib (`v4.35.0`) formalization (208 audited declarations, zero `sorry`, zero `native_decide`, standard axioms `propext`, `Quot.sound`, `Classical.choice` only).

Companion manuscript, interactive Proof Blueprint, and verification archive:
<https://mathdiscoveries.org/results/lazebnik-ustimenko>

## Compared Theorems (`Challenge.lean` / `Solution.lean`)

1. `D9_D10_exact_girth_14_all_q_ge_4` — `girth D(9, F) = girth D(10, F) = 14` for every finite field `F` with `|F| ≥ 4` (closing characteristics 2 and 3).
2. `D9_D10_orig_exact_girth_14_all_q_ge_4` — same in the original DS28 minus-sign representation `DGraphOrig`.
3. `D9_D10_exact_girth_14_galoisField` — direct `GaloisField p n` instantiation for every prime power `p^n ≥ 4`.
4. `DS28_table7_blank_cells_27_32` — explicit closure of the four empty DS28 Table 7 cells `(9, 27), (10, 27), (9, 32), (10, 32)`.
5. `card_admissible_ge_two_of_card_ge_four` — at least 2 admissible cycle parameters in every finite field with `|F| ≥ 4`.
6. `D2_exact_girth_law` — complete binary girth law `girth D(k, 2) = 2^s` for `s ≥ 3` and `2^(s-1) - 4 < k ≤ 2^s - 4`.
7. `D2_exact_girth_orig_law` — complete binary girth law in `DGraphOrig`.
8. `D2_girth_gt_16_of_ge_13` — for all `k ≥ 13`, `girth D(k, 2) ≥ 32` and no 16-cycle (refuting the `2^(k-3) C_16` claim).
9. `D3_exact_girths_highlights` — unconditional kernel-verified ternary girths at `k = 15, 16 (20)`, `47, 48 (52)`, `55, 56 (60)`, `79, 80 (84)`, `99 (104)`, `103, 104 (108)`.
10. `D3_k52_bounds_56_60` — unconditional tightening `56 ≤ girth D(52, 3) ≤ 60`.

## Verification

```sh
lake build LazebnikUstimenko LazebnikUstimenko.Verify Challenge Solution
lake env lean LazebnikUstimenko/Verify.lean
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B. Hughes**. No human mathematician has yet refereed the proof. Licensed under Apache-2.0.
