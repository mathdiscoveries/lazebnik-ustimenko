module

public import LazebnikUstimenko.CascadeAndDk3
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Binary Girth Law (`D(k, 2)`), Admissible Census, DS28 Tables 7–12, and Extended `D(k, 3)` Girths

This purely additive module strengthens `LazebnikUstimenko` in four directions without modifying
any baseline module:

1. **Complete Unconditional Binary Girth Law & Refutation of the DS28 (2026) / LSW (2017) Erratum:**
   Proves via an exact affine unipotent 4-step decomposition `T4(p) = (I + N)p + b` over `ZMod 2`
   that for **every** `s ≥ 3` and **every** `k` with `2^(s - 1) - 4 < k ≤ 2^s - 4`,
   `HasExactGirth (DGraph k (ZMod 2)) (2 ^ s)` (and identically in `DGraphOrig`).
   In particular, `girth D(k, 2) = 8` on `[2, 4]`, `16` on `[5, 12]`, `32` on `[13, 28]`,
   `64` on `[29, 60]`, and for **every** `k ≥ 13`, `girth D(k, 2) ≥ 32 > 16` with no `16`-cycle
   (`D2_girth_gt_16_of_ge_13`), unconditionally refuting the printed claim
   `D(k, 2) ≅ 2^(k-3) C_16` (`k ≥ 5`) in Lazebnik–Sun–Wang (2017) and DS28 (2026).

2. **Exact Admissible Parameter Census Across All Finite Fields & Original-Model Sharpness:**
   Computes the exact cardinality `Nat.card {c : F // Admissible c}` over every finite field
   `F` of size `q`: `q - 2` in characteristic `2`, `q - 5` in odd characteristic when `IsSquare 2`,
   and `q - 3` in odd characteristic when `¬ IsSquare 2` (specializing via quadratic reciprocity on
   `ZMod p` to `p - 5` for `p ≡ ±1 (mod 8)` and `p - 3` for `p ≡ ±3 (mod 8)`). Deduces `0`
   admissible parameters in `GF(2)` and `GF(3)`, at least `2` admissible parameters in **every**
   finite field of cardinality `q ≥ 4`, injectivity of `c ↦ walk14 c`, and exact `D(11, F)`
   non-closure residue `c (c - 1) / (c² + 2 c - 1)` in the original minus-sign model `DGraphOrig`.

3. **Explicit `GaloisField p n` Bridges & DS28 Tables 7–12 Cells at `q = 27, 32`:**
   Bridges directly to Mathlib's `GaloisField p n` (`p^n ≥ 4`), unconditionally filling DS28
   Table 7's blank cells `(9, 27), (10, 27), (9, 32), (10, 32) → 14` and supplying the missing
   cascade foundation for DS28 Tables 8 & 10's six ungrounded printed cells
   `(23, 27), (24, 27), (23, 32), (24, 32) → 28` and `(51, 27), (51, 32) → 56`, as well as
   Table 9/12 char-3 cells `(37, 27), (38, 27) → 42`, `(79, 27), (80, 27) → 84` and char-2 cell
   `(52, 32) → 56`.

4. **Complete Tight `D(k, 3)` Unconditional Certificates (`k ≤ 51` + Beyond-`51` Sharpenings):**
   * Formalizes the exact `19`-entry set `R19_4_2_new_k_set` (`card = 19`, correcting prose `"23"`).
   * Adds the remaining **6** unconditional exact `D(k, 3)` girths for `k ≤ 51`
     (`k = 31, 32 → 36`; `35 → 40`; `49, 50 → 54`; `51 → 56`), achieving **19/19 (100%)**
     unconditional coverage of all tight `k ≤ 51`.
   * Proves **8** additional unconditional tight `D(k, 3)` girths beyond `k = 51` in Lean's pure
     kernel (standard `decide` under default kernel limits): `k = 55, 56 → 60` (sharpening DS28 Table 4's
     `55: ≤ 68` to exact `60`, filling `56`, and tightening the first open Problem 47 case
     `D(52, 3)` from `[56, 68]` to `[56, 60]`), `k = 67 → 72`, `k = 79, 80 → 84` (sharpening
     `79: ≤ 96` and filling `80`), `k = 99 → 104` (genuinely new from `D(48, 3) = 52`), and
     `k = 103, 104 → 108`, bringing the library total to **27 unconditional exact `D(k, 3)`
     girths**; plus explicit `DS28Thm55Hyp (ZMod 3) 3` lifts for `k = 115 → 120` and the new
     infinite ray `D(52 · 3^s - 5, 3) = D(52 · 3^s - 4, 3) = 52 · 3^s` (yielding `151, 152 → 156`).
-/

@[expose] public section

namespace LazebnikUstimenko

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-! ### Part 1: Complete Exact Binary Girth Law (`D(k, ZMod 2)`) & DS28 Erratum Refutation -/

/-- Infinite-dimensional line step over `ZMod 2` (truncating to `Fin k` agrees with `stepLine`). -/
def stepLineInf (p : ℕ → ZMod 2) (x : ZMod 2) : ℕ → ZMod 2
  | 0 => x
  | 1 => p 0 * x - p 1
  | 2 => p 0 * stepLineInf p x 1 - p 2
  | j + 3 =>
    if ((j + 3) + 1) % 4 = 0 ∨ ((j + 3) + 1) % 4 = 1 then
      p (j + 1) * x - p (j + 3)
    else
      p 0 * stepLineInf p x (j + 1) - p (j + 3)

/-- Infinite-dimensional point step over `ZMod 2` (truncating to `Fin k` agrees with `stepPoint`). -/
def stepPointInf (l : ℕ → ZMod 2) (x : ZMod 2) : ℕ → ZMod 2
  | 0 => x
  | 1 => x * l 0 - l 1
  | 2 => x * l 1 - l 2
  | j + 3 =>
    if ((j + 3) + 1) % 4 = 0 ∨ ((j + 3) + 1) % 4 = 1 then
      stepPointInf l x (j + 1) * l 0 - l (j + 3)
    else
      x * l (j + 1) - l (j + 3)

/-- Canonical 4-step binary transition `p ↦ l₁(0) ↦ p₂(1) ↦ l₃(1) ↦ p₄(0)` in `D(∞, ZMod 2)`. -/
def T4 (p : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  stepPointInf (stepLineInf (stepPointInf (stepLineInf p 0) 1) 1) 0

/-- Constant translation vector `b = T4(0)` (`1` on coordinates `1, 2, 3, 4`, `0` elsewhere). -/
def bD2 : ℕ → ZMod 2
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | _ => 0

/-- Closed-form strictly-shifting linear operator `N = T4 - I - b` on `{p : ℕ → ZMod 2 | p 0 = 0}`. -/
def opN (v : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => v 1
  | 5 => v 1
  | 6 => v 1 + v 2
  | 7 => v 1 + v 3
  | 8 => v 1 + v 2 + v 4
  | j + 9 =>
    if (j + 9) % 4 = 1 ∨ (j + 9) % 4 = 2 then
      v (j + 5) + v (j + 3)
    else
      v (j + 5) + v (j + 3) + v (j + 1)

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by fin_cases a <;> fin_cases b <;> decide

lemma zmod2_neg_eq (a : ZMod 2) : -a = a := by fin_cases a <;> rfl

lemma zmod2_eq_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl h | rfl

lemma stepLineInf_eq_stepLine {k : ℕ} {p : Fin k → ZMod 2} {P : ℕ → ZMod 2}
    (hagree : ∀ j : Fin k, P j.val = p j) (x : ZMod 2) :
    ∀ j : Fin k, stepLineInf P x j.val = stepLine p x j := by
  intro ⟨j, hjlt⟩
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => rfl
    | 1 =>
      simp only [stepLineInf, stepLine, stepLineCoord]
      rw [hagree ⟨0, by omega⟩, hagree ⟨1, hjlt⟩]
    | 2 =>
      simp only [stepLineInf, stepLine, stepLineCoord]
      rw [hagree ⟨0, by omega⟩, hagree ⟨1, by omega⟩, hagree ⟨2, hjlt⟩]
    | j + 3 =>
      simp only [stepLineInf, stepLine, stepLineCoord]
      split_ifs
      · rw [hagree ⟨j + 1, by omega⟩, hagree ⟨j + 3, hjlt⟩]
      · rw [hagree ⟨0, by omega⟩, hagree ⟨j + 3, hjlt⟩, ih (j + 1) (by omega) (by omega)]
        rfl

lemma stepPointInf_eq_stepPoint {k : ℕ} {l : Fin k → ZMod 2} {L : ℕ → ZMod 2}
    (hagree : ∀ j : Fin k, L j.val = l j) (x : ZMod 2) :
    ∀ j : Fin k, stepPointInf L x j.val = stepPoint l x j := by
  intro ⟨j, hjlt⟩
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => rfl
    | 1 =>
      simp only [stepPointInf, stepPoint, stepPointCoord]
      rw [hagree ⟨0, by omega⟩, hagree ⟨1, hjlt⟩]
    | 2 =>
      simp only [stepPointInf, stepPoint, stepPointCoord]
      rw [hagree ⟨1, by omega⟩, hagree ⟨2, hjlt⟩]
    | j + 3 =>
      simp only [stepPointInf, stepPoint, stepPointCoord]
      split_ifs
      · rw [hagree ⟨0, by omega⟩, hagree ⟨j + 3, hjlt⟩, ih (j + 1) (by omega) (by omega)]
        rfl
      · rw [hagree ⟨j + 1, by omega⟩, hagree ⟨j + 3, hjlt⟩]

lemma stepLineInf_zero_eq {p : ℕ → ZMod 2} (hp0 : p 0 = 0) : stepLineInf p 0 = p := by
  funext j
  match j with
  | 0 => simpa [stepLineInf] using hp0.symm
  | 1 => simp [stepLineInf, hp0]
  | 2 => simp [stepLineInf, hp0]
  | j + 3 =>
    simp only [stepLineInf, hp0, mul_zero, zero_mul, zero_sub, zmod2_neg_eq, ite_self]

lemma stepPointInf_one_of_zero {p : ℕ → ZMod 2} (hp0 : p 0 = 0) (j : ℕ) :
    stepPointInf p 1 j =
      match j with
      | 0 => 1
      | 1 => p 1
      | 2 => p 1 + p 2
      | j + 3 =>
        if ((j + 3) + 1) % 4 = 0 ∨ ((j + 3) + 1) % 4 = 1 then
          p (j + 3)
        else
          p (j + 1) + p (j + 3) := by
  match j with
  | 0 => rfl
  | 1 => simp [stepPointInf, hp0]
  | 2 => simp [stepPointInf, zmod2_sub_eq_add]
  | j + 3 =>
    simp only [stepPointInf, hp0, mul_zero, zero_sub, one_mul, zmod2_neg_eq, zmod2_sub_eq_add]

lemma stepLineInf_l3_formula {p : ℕ → ZMod 2} (hp0 : p 0 = 0) :
    let p2 := stepPointInf p 1
    let l3 := stepLineInf p2 1
    l3 0 = 1 ∧ l3 1 = 1 + p 1 ∧ l3 2 = 1 + p 2 ∧
    l3 3 = p 1 + p 3 ∧ l3 4 = p 1 + p 2 + p 4 ∧
    l3 5 = p 1 + p 5 ∧ l3 6 = p 1 + p 2 + p 6 ∧
    l3 7 = p 3 + p 5 + p 7 ∧ l3 8 = p 4 + p 6 + p 8 ∧
    (∀ j : ℕ, l3 (j + 9) =
      if (j + 9) % 4 = 1 ∨ (j + 9) % 4 = 2 then
        p (j + 3) + p (j + 5) + p (j + 9)
      else
        p (j + 5) + p (j + 7) + p (j + 9)) := by
  dsimp only
  have hp2 := stepPointInf_one_of_zero hp0
  have h0 : stepPointInf p 1 0 = 1 := hp2 0
  have h1 : stepPointInf p 1 1 = p 1 := hp2 1
  have h2 : stepPointInf p 1 2 = p 1 + p 2 := hp2 2
  have h3 : stepPointInf p 1 3 = p 3 := by simpa using hp2 3
  have h4 : stepPointInf p 1 4 = p 4 := by simpa using hp2 4
  have h5 : stepPointInf p 1 5 = p 3 + p 5 := by simpa using hp2 5
  have h6 : stepPointInf p 1 6 = p 4 + p 6 := by simpa using hp2 6
  have h7 : stepPointInf p 1 7 = p 7 := by simpa using hp2 7
  have h8 : stepPointInf p 1 8 = p 8 := by simpa using hp2 8
  have hl0 : stepLineInf (stepPointInf p 1) 1 0 = 1 := rfl
  have hl1 : stepLineInf (stepPointInf p 1) 1 1 = 1 + p 1 := by
    simp [stepLineInf, h0, h1, zmod2_sub_eq_add]
  have hl2 : stepLineInf (stepPointInf p 1) 1 2 = 1 + p 2 := by
    simp only [stepLineInf, h0, h1, h2, one_mul, mul_one, zmod2_sub_eq_add]
    have ha := zmod2_add_self (p 1)
    linear_combination ha
  have hl3 : stepLineInf (stepPointInf p 1) 1 3 = p 1 + p 3 := by
    simp [stepLineInf, h1, h3, zmod2_sub_eq_add]
  have hl4 : stepLineInf (stepPointInf p 1) 1 4 = p 1 + p 2 + p 4 := by
    simp [stepLineInf, h2, h4, zmod2_sub_eq_add]
  have hl5 : stepLineInf (stepPointInf p 1) 1 5 = p 1 + p 5 := by
    have hstep : stepLineInf (stepPointInf p 1) 1 5 =
        stepPointInf p 1 0 * stepLineInf (stepPointInf p 1) 1 3 - stepPointInf p 1 5 := by
      simp [stepLineInf]
    rw [hstep, h0, hl3, h5, one_mul, zmod2_sub_eq_add]
    have ha := zmod2_add_self (p 3)
    linear_combination ha
  have hl6 : stepLineInf (stepPointInf p 1) 1 6 = p 1 + p 2 + p 6 := by
    have hstep : stepLineInf (stepPointInf p 1) 1 6 =
        stepPointInf p 1 0 * stepLineInf (stepPointInf p 1) 1 4 - stepPointInf p 1 6 := by
      simp [stepLineInf]
    rw [hstep, h0, hl4, h6, one_mul, zmod2_sub_eq_add]
    have ha := zmod2_add_self (p 4)
    linear_combination ha
  have hl7 : stepLineInf (stepPointInf p 1) 1 7 = p 3 + p 5 + p 7 := by
    have hstep : stepLineInf (stepPointInf p 1) 1 7 =
        stepPointInf p 1 5 * 1 - stepPointInf p 1 7 := by simp [stepLineInf]
    rw [hstep, h5, h7, mul_one, zmod2_sub_eq_add]
  have hl8 : stepLineInf (stepPointInf p 1) 1 8 = p 4 + p 6 + p 8 := by
    have hstep : stepLineInf (stepPointInf p 1) 1 8 =
        stepPointInf p 1 6 * 1 - stepPointInf p 1 8 := by simp [stepLineInf]
    rw [hstep, h6, h8, mul_one, zmod2_sub_eq_add]
  refine ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, ?_⟩
  intro j
  have hstep : stepLineInf (stepPointInf p 1) 1 (j + 9) =
      if ((j + 9) + 1) % 4 = 0 ∨ ((j + 9) + 1) % 4 = 1 then
        stepPointInf p 1 (j + 7) * 1 - stepPointInf p 1 (j + 9)
      else
        stepPointInf p 1 0 * stepLineInf (stepPointInf p 1) 1 (j + 7) -
          stepPointInf p 1 (j + 9) := rfl
  rw [hstep]
  by_cases hm : (j + 9) % 4 = 1 ∨ (j + 9) % 4 = 2
  · have hm1 : ¬ (((j + 9) + 1) % 4 = 0 ∨ ((j + 9) + 1) % 4 = 1) := by omega
    have hm_prev : ((j + 7) + 1) % 4 = 0 ∨ ((j + 7) + 1) % 4 = 1 := by omega
    have hm_prev2 : ¬ (((j + 5) + 1) % 4 = 0 ∨ ((j + 5) + 1) % 4 = 1) := by omega
    simp only [hm, hm1, ite_true, ite_false, h0, one_mul, zmod2_sub_eq_add]
    have hl_prev : stepLineInf (stepPointInf p 1) 1 (j + 7) =
        stepPointInf p 1 (j + 5) + stepPointInf p 1 (j + 7) := by
      have hs : stepLineInf (stepPointInf p 1) 1 (j + 7) =
          if ((j + 7) + 1) % 4 = 0 ∨ ((j + 7) + 1) % 4 = 1 then
            stepPointInf p 1 (j + 5) * 1 - stepPointInf p 1 (j + 7)
          else
            stepPointInf p 1 0 * stepLineInf (stepPointInf p 1) 1 (j + 5) -
              stepPointInf p 1 (j + 7) := rfl
      rw [hs]; simp [hm_prev, zmod2_sub_eq_add]
    have hp2_9 : stepPointInf p 1 (j + 9) = p (j + 7) + p (j + 9) := by
      have := hp2 (j + 9); simpa [hm1] using this
    have hp2_7 : stepPointInf p 1 (j + 7) = p (j + 7) := by
      have := hp2 (j + 7); simpa [hm_prev] using this
    have hp2_5 : stepPointInf p 1 (j + 5) = p (j + 3) + p (j + 5) := by
      have := hp2 (j + 5); simpa [hm_prev2] using this
    rw [hl_prev, hp2_5, hp2_7, hp2_9]
    have ha := zmod2_add_self (p (j + 7))
    linear_combination ha
  · have hm1 : ((j + 9) + 1) % 4 = 0 ∨ ((j + 9) + 1) % 4 = 1 := by omega
    have hm_prev : ¬ (((j + 7) + 1) % 4 = 0 ∨ ((j + 7) + 1) % 4 = 1) := by omega
    simp only [hm, hm1, ite_true, ite_false, mul_one, zmod2_sub_eq_add]
    have hp2_9 : stepPointInf p 1 (j + 9) = p (j + 9) := by
      have := hp2 (j + 9); simpa [hm1] using this
    have hp2_7 : stepPointInf p 1 (j + 7) = p (j + 5) + p (j + 7) := by
      have := hp2 (j + 7); simpa [hm_prev] using this
    rw [hp2_7, hp2_9]

/-- Exact affine unipotent decomposition of the canonical 4-step binary map:
`T4 p = p + opN p + bD2` whenever `p 0 = 0`. -/
theorem T4_eq_add_opN_add_b {p : ℕ → ZMod 2} (hp0 : p 0 = 0) :
    T4 p = p + opN p + bD2 := by
  funext j
  simp only [T4, stepLineInf_zero_eq hp0, Pi.add_apply]
  rcases stepLineInf_l3_formula hp0 with
    ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9⟩
  have hp4_5 : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 5 = p 1 + p 5 := by
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 5 =
        0 * stepLineInf (stepPointInf p 1) 1 3 - stepLineInf (stepPointInf p 1) 1 5 := by
      simp [stepPointInf]
    rw [hs, zero_mul, zero_sub, zmod2_neg_eq, hl5]
  have hp4_6 : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 6 = p 1 + p 2 + p 6 := by
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 6 =
        0 * stepLineInf (stepPointInf p 1) 1 4 - stepLineInf (stepPointInf p 1) 1 6 := by
      simp [stepPointInf]
    rw [hs, zero_mul, zero_sub, zmod2_neg_eq, hl6]
  match j with
  | 0 => simp [stepPointInf, opN, bD2, hp0]
  | 1 =>
    simp only [stepPointInf, opN, bD2, zero_mul, zero_sub, zmod2_neg_eq, hl1, add_zero]
    ring
  | 2 =>
    simp only [stepPointInf, opN, bD2, zero_mul, zero_sub, zmod2_neg_eq, hl2, add_zero]
    ring
  | 3 =>
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 3 =
        stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 1 *
          stepLineInf (stepPointInf p 1) 1 0 - stepLineInf (stepPointInf p 1) 1 3 := by
      simp [stepPointInf]
    have h1 : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 1 = 1 + p 1 := by
      simp [stepPointInf, hl1, add_comm]
    rw [hs, h1, hl0, hl3, mul_one, zmod2_sub_eq_add]
    simp only [opN, bD2, add_zero]
    have ha := zmod2_add_self (p 1)
    linear_combination ha
  | 4 =>
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 4 =
        stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 2 *
          stepLineInf (stepPointInf p 1) 1 0 - stepLineInf (stepPointInf p 1) 1 4 := by
      simp [stepPointInf]
    have h2 : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 2 = 1 + p 2 := by
      simp [stepPointInf, hl2, add_comm]
    rw [hs, h2, hl0, hl4, mul_one, zmod2_sub_eq_add]
    simp only [opN, bD2]
    have ha := zmod2_add_self (p 2)
    linear_combination ha
  | 5 =>
    rw [hp4_5]; simp only [opN, bD2, add_zero]; ring
  | 6 =>
    rw [hp4_6]; simp only [opN, bD2, add_zero]; ring
  | 7 =>
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 7 =
        stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 5 *
          stepLineInf (stepPointInf p 1) 1 0 - stepLineInf (stepPointInf p 1) 1 7 := by
      simp [stepPointInf]
    rw [hs, hp4_5, hl0, hl7, mul_one, zmod2_sub_eq_add]
    simp only [opN, bD2, add_zero]
    have ha := zmod2_add_self (p 5)
    linear_combination ha
  | 8 =>
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 8 =
        stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 6 *
          stepLineInf (stepPointInf p 1) 1 0 - stepLineInf (stepPointInf p 1) 1 8 := by
      simp [stepPointInf]
    rw [hs, hp4_6, hl0, hl8, mul_one, zmod2_sub_eq_add]
    simp only [opN, bD2, add_zero]
    have ha := zmod2_add_self (p 6)
    linear_combination ha
  | j + 9 =>
    have hs : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 (j + 9) =
        if ((j + 9) + 1) % 4 = 0 ∨ ((j + 9) + 1) % 4 = 1 then
          stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 (j + 7) *
            stepLineInf (stepPointInf p 1) 1 0 - stepLineInf (stepPointInf p 1) 1 (j + 9)
        else
          0 * stepLineInf (stepPointInf p 1) 1 (j + 7) -
            stepLineInf (stepPointInf p 1) 1 (j + 9) := rfl
    rw [hs]
    simp only [opN, bD2, add_zero]
    by_cases hm : (j + 9) % 4 = 1 ∨ (j + 9) % 4 = 2
    · have hm1 : ¬ (((j + 9) + 1) % 4 = 0 ∨ ((j + 9) + 1) % 4 = 1) := by omega
      simp only [hm, hm1, ite_true, ite_false, zero_mul, zero_sub, zmod2_neg_eq]
      rw [hl9 j]
      simp only [hm, ite_true]
      ring
    · have hm1 : ((j + 9) + 1) % 4 = 0 ∨ ((j + 9) + 1) % 4 = 1 := by omega
      have hm_prev : ¬ (((j + 7) + 1) % 4 = 0 ∨ ((j + 7) + 1) % 4 = 1) := by omega
      simp only [hm, hm1, ite_true, ite_false, hl0, mul_one, zmod2_sub_eq_add]
      have hp4_prev : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 (j + 7) =
          stepLineInf (stepPointInf p 1) 1 (j + 7) := by
        have hsp : stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 (j + 7) =
            if ((j + 7) + 1) % 4 = 0 ∨ ((j + 7) + 1) % 4 = 1 then
              stepPointInf (stepLineInf (stepPointInf p 1) 1) 0 (j + 5) *
                stepLineInf (stepPointInf p 1) 1 0 - stepLineInf (stepPointInf p 1) 1 (j + 7)
            else
              0 * stepLineInf (stepPointInf p 1) 1 (j + 5) -
                stepLineInf (stepPointInf p 1) 1 (j + 7) := rfl
        rw [hsp]; simp [hm_prev]
      rw [hp4_prev, hl9 j]
      simp only [hm, ite_false]
      match j with
      | 0 => omega
      | 1 => omega
      | 2 =>
        have h9 : (2 + 7 : ℕ) = 0 + 9 := rfl
        rw [h9, hl9 0]
        have hm09 : (0 + 9) % 4 = 1 := by decide
        simp only [hm09, true_or, ite_true]
        have ha := zmod2_add_self (p 9)
        linear_combination ha
      | 3 =>
        have h10 : (3 + 7 : ℕ) = 1 + 9 := rfl
        rw [h10, hl9 1]
        have hm19 : (1 + 9) % 4 = 2 := by decide
        simp only [hm19, or_true, ite_true]
        have ha := zmod2_add_self (p 10)
        linear_combination ha
      | j + 4 =>
        have hidx : (j + 4 + 7 : ℕ) = (j + 2) + 9 := by omega
        rw [hidx, hl9 (j + 2)]
        have hm2 : ((j + 2) + 9) % 4 = 1 ∨ ((j + 2) + 9) % 4 = 2 := by omega
        simp only [hm2, ite_true]
        have ha := zmod2_add_self (p (j + 11))
        linear_combination ha

lemma opN_add (u v : ℕ → ZMod 2) : opN (u + v) = opN u + opN v := by
  funext j
  match j with
  | 0 | 1 | 2 | 3 => simp [opN]
  | 4 | 5 => simp [opN]
  | 6 | 7 | 8 => simp [opN]; ring
  | j + 9 =>
    simp only [opN, Pi.add_apply]
    split_ifs <;> ring

lemma opN_zero : opN 0 = 0 := by
  funext j
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => simp [opN]
  | j + 9 => simp only [opN, Pi.zero_apply]; split_ifs <;> simp

lemma opN_iter_add (m : ℕ) (u v : ℕ → ZMod 2) :
    opN^[m] (u + v) = opN^[m] u + opN^[m] v := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Function.iterate_succ_apply', ih, opN_add]

lemma T4_zero_coord (p : ℕ → ZMod 2) : T4 p 0 = 0 := rfl

lemma T4_iter_zero_coord (n : ℕ) {p : ℕ → ZMod 2} (hp0 : p 0 = 0) : T4^[n] p 0 = 0 := by
  induction n with
  | zero => exact hp0
  | succ n _ => rw [Function.iterate_succ_apply']; rfl

lemma zmod2_fn_add_self (v : ℕ → ZMod 2) : v + v = 0 := by
  funext j; exact zmod2_add_self (v j)

/-- Exact power-of-2 iterate formula in characteristic 2:
`T4^[2^r] p = p + opN^[2^r] p + opN^[2^r - 1] bD2` whenever `p 0 = 0`. -/
theorem T4_pow_two (r : ℕ) {p : ℕ → ZMod 2} (hp0 : p 0 = 0) :
    T4^[2 ^ r] p = p + opN^[2 ^ r] p + opN^[2 ^ r - 1] bD2 := by
  induction r generalizing p with
  | zero =>
    simpa using T4_eq_add_opN_add_b hp0
  | succ r ih =>
    have hsplit : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
    rw [hsplit, Function.iterate_add_apply]
    have hp1 : T4^[2 ^ r] p 0 = 0 := T4_iter_zero_coord (2 ^ r) hp0
    rw [ih hp1, ih hp0, opN_iter_add, opN_iter_add, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply]
    have hpow : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by omega)
    have hexp : 2 ^ r + (2 ^ r - 1) = 2 ^ r + 2 ^ r - 1 := by omega
    rw [hexp]
    funext j
    simp only [Pi.add_apply]
    have h1 := zmod2_add_self (opN^[2 ^ r] p j)
    have h2 := zmod2_add_self (opN^[2 ^ r - 1] bD2 j)
    linear_combination h1 + h2

/-- Shift lemma for `opN`: if `J ≥ 4` and `v` vanishes below `J`, then `opN v` vanishes
below `J + 4`. -/
lemma opN_shift {J : ℕ} (hJ : 4 ≤ J) {v : ℕ → ZMod 2} (hv : ∀ j < J, v j = 0) :
    ∀ j < J + 4, opN v j = 0 := by
  intro j hj
  match j with
  | 0 | 1 | 2 | 3 => rfl
  | 4 | 5 => simp [opN, hv 1 (by omega)]
  | 6 => simp [opN, hv 1 (by omega), hv 2 (by omega)]
  | 7 => simp [opN, hv 1 (by omega), hv 3 (by omega)]
  | 8 => simp [opN, hv 1 (by omega), hv 2 (by omega), hv 4 (by omega)]
  | j + 9 =>
    simp only [opN]
    split_ifs
    · rw [hv (j + 5) (by omega), hv (j + 3) (by omega), add_zero]
    · rw [hv (j + 5) (by omega), hv (j + 3) (by omega), hv (j + 1) (by omega), add_zero, add_zero]

/-- Iterated shift lemma: if `J ≥ 4` and `v` vanishes below `J`, then `opN^[d] v` vanishes
below `J + 4 * d`. -/
lemma opN_iter_shift (d : ℕ) {J : ℕ} (hJ : 4 ≤ J) {v : ℕ → ZMod 2}
    (hv : ∀ j < J, v j = 0) : ∀ j < J + 4 * d, opN^[d] v j = 0 := by
  induction d with
  | zero => simpa using hv
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    have hstep := opN_shift (J := J + 4 * d) (by omega) ih
    intro j hj
    exact hstep j (by omega)

/-- Exact leading-nonzero valuation of `opN^[m] bD2`: for every `m ≥ 1`, `opN^[m] bD2` vanishes
on all `j < 4 * m` and equals `1` at `j = 4 * m`. -/
theorem opN_iter_bD2_valuation {m : ℕ} (hm : 1 ≤ m) :
    (∀ j < 4 * m, opN^[m] bD2 j = 0) ∧ opN^[m] bD2 (4 * m) = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · refine ⟨?_, by rfl⟩
      intro j hj
      match j with
      | 0 | 1 | 2 | 3 => rfl
    · rcases ih hm1 with ⟨hvan, hlead⟩
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_⟩
      · have hsh := opN_shift (J := 4 * m) (by omega) hvan
        intro j hj
        exact hsh j (by omega)
      · by_cases hm_eq1 : m = 1
        · subst hm_eq1
          change opN (opN^[1] bD2) 8 = 1
          simp only [opN]
          rw [hvan 1 (by omega), hvan 2 (by omega), hlead]
          norm_num
        · have hm2 : 2 ≤ m := by omega
          have heq : 4 * (m + 1) = (4 * m - 5) + 9 := by omega
          rw [heq]
          simp only [opN]
          have hmod : ¬ (((4 * m - 5) + 9) % 4 = 1 ∨ ((4 * m - 5) + 9) % 4 = 2) := by omega
          simp only [hmod, ite_false]
          have h1 : 4 * m - 5 + 5 = 4 * m := by omega
          have h2 : 4 * m - 5 + 3 < 4 * m := by omega
          have h3 : 4 * m - 5 + 1 < 4 * m := by omega
          rw [h1, hlead, hvan _ h2, hvan _ h3]
          norm_num

/-- Coordinate 1 of `T4^[u] 0` equals `(u : ZMod 2)` for every `u : ℕ`. -/
lemma T4_iter_zero_one (u : ℕ) : T4^[u] 0 1 = (u : ZMod 2) := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Function.iterate_succ_apply', T4_eq_add_opN_add_b (T4_iter_zero_coord u rfl)]
    simp only [Pi.add_apply, opN, bD2, ih, add_zero, Nat.cast_add, Nat.cast_one]

/-- Exact vanishing and leading coordinate of `T4^[2^r * u] 0` for `r ≥ 1` and arbitrary `u`:
vanishes below `4 * (2^r - 1)` and equals `(u : ZMod 2)` at `4 * (2^r - 1)`. -/
lemma T4_iter_pow_two_mul {r : ℕ} (hr : 1 ≤ r) (u : ℕ) :
    (∀ j < 4 * (2 ^ r - 1), T4^[2 ^ r * u] 0 j = 0) ∧
    T4^[2 ^ r * u] 0 (4 * (2 ^ r - 1)) = (u : ZMod 2) := by
  have hpow : 2 ≤ 2 ^ r := by
    have : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr
    omega
  have hval := opN_iter_bD2_valuation (m := 2 ^ r - 1) (by omega)
  induction u with
  | zero =>
    refine ⟨fun _ _ => rfl, by simp⟩
  | succ u ih =>
    rcases ih with ⟨hvan, hlead⟩
    have hmul : 2 ^ r * (u + 1) = 2 ^ r + 2 ^ r * u := by ring
    rw [hmul, Function.iterate_add_apply, T4_pow_two r (T4_iter_zero_coord (2 ^ r * u) rfl)]
    have hsh := opN_iter_shift (2 ^ r) (J := 4 * (2 ^ r - 1)) (by omega) hvan
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [Pi.add_apply, hvan j hj, hsh j (by omega), hval.1 j hj, add_zero]
    · simp only [Pi.add_apply, hlead, hsh (4 * (2 ^ r - 1)) (by omega), hval.2,
        add_zero, Nat.cast_add, Nat.cast_one]

/-- Exact 2-adic factorization of any positive natural number: `n = 2^r * u` with `Odd u`. -/
lemma exists_pow_two_mul_odd {n : ℕ} (hn : 1 ≤ n) :
    ∃ r u : ℕ, Odd u ∧ n = 2 ^ r * u := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : Even n
    · rcases he with ⟨m, hm⟩
      have hm1 : 1 ≤ m := by omega
      rcases ih m (by omega) hm1 with ⟨r, u, hu, hmu⟩
      refine ⟨r + 1, u, hu, ?_⟩
      calc n = m + m := hm
        _ = 2 * m := by ring
        _ = 2 * (2 ^ r * u) := by rw [hmu]
        _ = 2 ^ (r + 1) * u := by rw [pow_succ]; ring
    · exact ⟨0, n, Nat.not_even_iff_odd.1 he, by simp⟩

/-- Every simple cycle of length `L` in `D(k, ZMod 2)` (`k ≥ 2`) forces `4 ∣ L` and
`∀ j < k, T4^[L / 4] 0 j = 0`. -/
theorem walkD2_canonical_of_cycle {k L : ℕ} (hk : 2 ≤ k)
    (hc : HasCycleOfLen (DGraph k (ZMod 2)) L) :
    4 ∣ L ∧ ∀ j < k, T4^[L / 4] 0 j = 0 := by
  rcases even_cycle_len_D hc with ⟨r, hr⟩
  have hL_eq : L = 2 * r := by omega
  subst hL_eq
  have hL3 := hc.1
  have hr2 : 2 ≤ r := by omega
  have hk0 : 0 < k := by omega
  rcases cycle_to_zero_walk_D hk0 hr2 hc with ⟨u0, hu0_zero, hu0_adj, hu0_nb⟩
  have hex_canon : ∃ u : Fin (2 * r) → Fin k → ZMod 2,
      u ⟨0, by omega⟩ = 0 ∧ u ⟨1, by omega⟩ ⟨0, hk0⟩ = 0 ∧
      (∀ i : Fin (2 * r),
        if Even i.val then
          PLAdj k (ZMod 2) (u i) (u ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩)
        else
          PLAdj k (ZMod 2) (u ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩) (u i)) ∧
      (∀ i : Fin (2 * r),
        u i ⟨0, hk0⟩ ≠ u ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩ ⟨0, hk0⟩) := by
    by_cases h1 : u0 ⟨1, by omega⟩ ⟨0, hk0⟩ = 0
    · exact ⟨u0, hu0_zero, h1, hu0_adj, hu0_nb⟩
    · have h1_eq : u0 ⟨1, by omega⟩ ⟨0, hk0⟩ = 1 := by
        have := zmod2_eq_add_one_of_ne h1; simpa using this
      let u : Fin (2 * r) → Fin k → ZMod 2 :=
        fun i => u0 ⟨(2 * r - i.val) % (2 * r), Nat.mod_lt _ (by omega)⟩
      refine ⟨u, ?_, ?_, ?_, ?_⟩
      · simp [u, hu0_zero]
      · have hidx : (2 * r - 1) % (2 * r) = 2 * r - 1 := Nat.mod_eq_of_lt (by omega)
        have hnb := hu0_nb ⟨2 * r - 1, by omega⟩
        have hmod : (2 * r - 1 + 2) % (2 * r) = 1 := by
          rw [show 2 * r - 1 + 2 = 2 * r + 1 by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [hmod, h1_eq] at hnb
        have hval : u0 ⟨2 * r - 1, by omega⟩ ⟨0, hk0⟩ = 0 := by
          have := zmod2_eq_add_one_of_ne hnb; simpa [zmod2_add_self] using this
        simpa [u, hidx] using hval
      · intro ⟨i, hilt⟩
        have hidx1 : (2 * r - (i + 1) % (2 * r)) % (2 * r) = 2 * r - (i + 1) := by
          by_cases hlast : i + 1 < 2 * r
          · rw [Nat.mod_eq_of_lt hlast]; exact Nat.mod_eq_of_lt (by omega)
          · have hi_eq : i + 1 = 2 * r := by omega
            rw [hi_eq, Nat.mod_self, Nat.sub_zero, Nat.mod_self, Nat.sub_self]
        have hsucc : ((2 * r - (i + 1)) + 1) % (2 * r) = (2 * r - i) % (2 * r) := by
          by_cases hi0 : i = 0
          · subst hi0
            rw [show 2 * r - (0 + 1) + 1 = 2 * r by omega, Nat.sub_zero, Nat.mod_self]
          · rw [show 2 * r - (i + 1) + 1 = 2 * r - i by omega]
        have h := hu0_adj ⟨2 * r - (i + 1), by omega⟩
        have hpar : Even (2 * r - (i + 1)) ↔ ¬ Even i := by
          constructor
          · rintro ⟨m, hm⟩ ⟨m', hm'⟩; omega
          · intro hne
            rcases Nat.not_even_iff_odd.1 hne with ⟨m, hm⟩
            exact ⟨r - m - 1, by omega⟩
        by_cases hei : Even i
        · have hno : ¬ Even (2 * r - (i + 1)) := fun h' => hpar.1 h' hei
          simp only [hei, ite_true, u, hidx1]
          simp only [hno, ite_false, hsucc] at h
          exact h
        · have he' : Even (2 * r - (i + 1)) := hpar.2 hei
          simp only [hei, ite_false, u, hidx1]
          simp only [he', ite_true, hsucc] at h
          exact h
      · intro ⟨i, hilt⟩
        by_cases hlt2 : i + 2 < 2 * r
        · have hidx2 : (2 * r - (i + 2) % (2 * r)) % (2 * r) = 2 * r - (i + 2) := by
            rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt (by omega)]
          have hnb := hu0_nb ⟨2 * r - (i + 2), by omega⟩
          have hadd2 : ((2 * r - (i + 2)) + 2) % (2 * r) = (2 * r - i) % (2 * r) := by
            by_cases hi0 : i = 0
            · subst hi0
              rw [show 2 * r - (0 + 2) + 2 = 2 * r by omega, Nat.sub_zero, Nat.mod_self]
            · rw [show 2 * r - (i + 2) + 2 = 2 * r - i by omega]
          simp only [hadd2] at hnb
          simp only [u, hidx2]
          exact hnb.symm
        · by_cases hi_eq : i + 2 = 2 * r
          · have hidx2 : (2 * r - (i + 2) % (2 * r)) % (2 * r) = 0 := by
              rw [hi_eq, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
            have hidx_i : (2 * r - i) % (2 * r) = 2 := by
              rw [show 2 * r - i = 2 by omega, Nat.mod_eq_of_lt (by omega)]
            have hnb := hu0_nb ⟨0, by omega⟩
            have hmod2 : (0 + 2) % (2 * r) = 2 := Nat.mod_eq_of_lt (by omega)
            simp only [hmod2] at hnb
            simp only [u, hidx2, hidx_i]
            exact hnb.symm
          · have hi_last : i = 2 * r - 1 := by omega
            have hidx2 : (2 * r - (i + 2) % (2 * r)) % (2 * r) = 2 * r - 1 := by
              have hmod1 : (i + 2) % (2 * r) = 1 := by
                rw [show i + 2 = 2 * r + 1 by omega, Nat.add_mod_left]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hmod1, Nat.mod_eq_of_lt (by omega)]
            have hidx_i : (2 * r - i) % (2 * r) = 1 := by
              rw [show 2 * r - i = 1 by omega, Nat.mod_eq_of_lt (by omega)]
            have hnb := hu0_nb ⟨2 * r - 1, by omega⟩
            have hmod1 : (2 * r - 1 + 2) % (2 * r) = 1 := by
              rw [show 2 * r - 1 + 2 = 2 * r + 1 by omega, Nat.add_mod_left]
              exact Nat.mod_eq_of_lt (by omega)
            simp only [hmod1] at hnb
            simp only [u, hidx2, hidx_i]
            exact hnb.symm
  rcases hex_canon with ⟨u, hu0, hu1, huadj, hunb⟩
  have hfc : ∀ t : ℕ, (ht : t < 2 * r) →
      u ⟨t, ht⟩ ⟨0, hk0⟩ = if (t / 2) % 2 = 0 then 0 else 1 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      match t with
      | 0 => simp [hu0]
      | 1 => simp [hu1]
      | t + 2 =>
        have hprev := ih t (by omega) (by omega)
        have hnb := hunb ⟨t, by omega⟩
        have hmod : (t + 2) % (2 * r) = t + 2 := Nat.mod_eq_of_lt ht
        simp only [hmod] at hnb
        have hne : u ⟨t + 2, ht⟩ ⟨0, hk0⟩ ≠ u ⟨t, by omega⟩ ⟨0, hk0⟩ := hnb.symm
        have heq := zmod2_eq_add_one_of_ne hne
        rw [heq, hprev]
        have hdiv : (t + 2) / 2 = t / 2 + 1 := by omega
        rw [hdiv]
        by_cases hm : (t / 2) % 2 = 0
        · have hm' : (t / 2 + 1) % 2 ≠ 0 := by omega
          simp [hm, hm']
        · have hm' : (t / 2 + 1) % 2 = 0 := by omega
          simp [hm, hm', zmod2_add_self]
  have hr_even : Even r := by
    have hnb := hunb ⟨2 * r - 2, by omega⟩
    have hmod : (2 * r - 2 + 2) % (2 * r) = 0 := by
      rw [show 2 * r - 2 + 2 = 2 * r by omega, Nat.mod_self]
    simp only [hmod, hu0, Pi.zero_apply] at hnb
    have hval := hfc (2 * r - 2) (by omega)
    rw [hval] at hnb
    have hdiv : (2 * r - 2) / 2 = r - 1 := by omega
    rw [hdiv] at hnb
    by_cases hm : (r - 1) % 2 = 0
    · simp [hm] at hnb
    · exact ⟨r / 2, by omega⟩
  rcases hr_even with ⟨n, hn⟩
  have hr_eq : r = 2 * n := by omega
  subst hr_eq
  have hn1 : 1 ≤ n := by omega
  have h4dvd : 4 ∣ 2 * (2 * n) := ⟨n, by ring⟩
  have hdiv4 : 2 * (2 * n) / 4 = n := by omega
  refine ⟨h4dvd, ?_⟩
  rw [hdiv4]
  have htrack : ∀ m ≤ n, ∀ j : Fin k,
      u ⟨(4 * m) % (2 * (2 * n)), Nat.mod_lt _ (by omega)⟩ j = T4^[m] 0 j.val := by
    intro m
    induction m with
    | zero =>
      intro _ j
      simp [hu0]
    | succ m ih =>
      intro hmle
      have hmlt : m < n := by omega
      have hprev := ih (by omega)
      have hmod0 : (4 * m) % (2 * (2 * n)) = 4 * m := Nat.mod_eq_of_lt (by omega)
      have hmod1 : (4 * m + 1) % (2 * (2 * n)) = 4 * m + 1 := Nat.mod_eq_of_lt (by omega)
      have hmod2 : (4 * m + 2) % (2 * (2 * n)) = 4 * m + 2 := Nat.mod_eq_of_lt (by omega)
      have hmod3 : (4 * m + 3) % (2 * (2 * n)) = 4 * m + 3 := Nat.mod_eq_of_lt (by omega)
      have hmod4 : ((4 * m + 3) + 1) % (2 * (2 * n)) = (4 * (m + 1)) % (2 * (2 * n)) := rfl
      have ha0 : PLAdj k (ZMod 2) (u ⟨4 * m, by omega⟩) (u ⟨4 * m + 1, by omega⟩) := by
        have h := huadj ⟨4 * m, by omega⟩
        have he : Even (4 * m) := ⟨2 * m, by omega⟩
        simpa only [he, ite_true, hmod1] using h
      have ha1 : PLAdj k (ZMod 2) (u ⟨4 * m + 2, by omega⟩) (u ⟨4 * m + 1, by omega⟩) := by
        have h := huadj ⟨4 * m + 1, by omega⟩
        have hno : ¬ Even (4 * m + 1) := by intro ⟨t, ht⟩; omega
        simpa only [hno, ite_false, show 4 * m + 1 + 1 = 4 * m + 2 by omega, hmod2] using h
      have ha2 : PLAdj k (ZMod 2) (u ⟨4 * m + 2, by omega⟩) (u ⟨4 * m + 3, by omega⟩) := by
        have h := huadj ⟨4 * m + 2, by omega⟩
        have he : Even (4 * m + 2) := ⟨2 * m + 1, by omega⟩
        simpa only [he, ite_true, show 4 * m + 2 + 1 = 4 * m + 3 by omega, hmod3] using h
      have ha3 : PLAdj k (ZMod 2)
          (u ⟨(4 * (m + 1)) % (2 * (2 * n)), Nat.mod_lt _ (by omega)⟩)
          (u ⟨4 * m + 3, by omega⟩) := by
        have h := huadj ⟨4 * m + 3, by omega⟩
        have hno : ¬ Even (4 * m + 3) := by intro ⟨t, ht⟩; omega
        simpa only [hno, ite_false, hmod4] using h
      have hfc1 : u ⟨4 * m + 1, by omega⟩ ⟨0, hk0⟩ = 0 := by
        rw [hfc (4 * m + 1) (by omega)]
        simp only [show ((4 * m + 1) / 2) % 2 = 0 by omega, ite_true]
      have hfc2 : u ⟨4 * m + 2, by omega⟩ ⟨0, hk0⟩ = 1 := by
        rw [hfc (4 * m + 2) (by omega)]
        simp only [show ¬ ((4 * m + 2) / 2) % 2 = 0 by omega, ite_false]
      have hfc3 : u ⟨4 * m + 3, by omega⟩ ⟨0, hk0⟩ = 1 := by
        rw [hfc (4 * m + 3) (by omega)]
        simp only [show ¬ ((4 * m + 3) / 2) % 2 = 0 by omega, ite_false]
      have hfc4 : u ⟨(4 * (m + 1)) % (2 * (2 * n)), Nat.mod_lt _ (by omega)⟩ ⟨0, hk0⟩ = 0 := by
        by_cases hlast : m + 1 = n
        · subst hlast
          have hm0 : (4 * (m + 1)) % (2 * (2 * (m + 1))) = 0 := by
            rw [show 2 * (2 * (m + 1)) = 4 * (m + 1) by omega, Nat.mod_self]
          have hfin : (⟨(4 * (m + 1)) % (2 * (2 * (m + 1))), Nat.mod_lt _ (by omega)⟩ :
              Fin (2 * (2 * (m + 1)))) = ⟨0, by omega⟩ := Fin.ext hm0
          rw [hfin, hu0]; rfl
        · have hmod' : (4 * (m + 1)) % (2 * (2 * n)) = 4 * (m + 1) := Nat.mod_eq_of_lt (by omega)
          simp only [hmod']
          rw [hfc (4 * (m + 1)) (by omega)]
          simp only [show ((4 * (m + 1)) / 2) % 2 = 0 by omega, ite_true]
      have hu_m : ∀ j : Fin k, T4^[m] 0 j.val = u ⟨4 * m, by omega⟩ j := by
        intro j; simpa only [hmod0] using (hprev j).symm
      have eq1 : stepLine (u ⟨4 * m, by omega⟩) 0 = u ⟨4 * m + 1, by omega⟩ :=
        stepLine_eq_of_plAdj hk0 ha0 hfc1
      have eq2 : stepPoint (u ⟨4 * m + 1, by omega⟩) 1 = u ⟨4 * m + 2, by omega⟩ :=
        stepPoint_eq_of_plAdj hk0 ha1 hfc2
      have eq3 : stepLine (u ⟨4 * m + 2, by omega⟩) 1 = u ⟨4 * m + 3, by omega⟩ :=
        stepLine_eq_of_plAdj hk0 ha2 hfc3
      have eq4 : stepPoint (u ⟨4 * m + 3, by omega⟩) 0 =
          u ⟨(4 * (m + 1)) % (2 * (2 * n)), Nat.mod_lt _ (by omega)⟩ :=
        stepPoint_eq_of_plAdj hk0 ha3 hfc4
      have ag1 : ∀ j : Fin k, stepLineInf (T4^[m] 0) 0 j.val = u ⟨4 * m + 1, by omega⟩ j := by
        intro j; rw [stepLineInf_eq_stepLine hu_m 0 j, eq1]
      have ag2 : ∀ j : Fin k,
          stepPointInf (stepLineInf (T4^[m] 0) 0) 1 j.val = u ⟨4 * m + 2, by omega⟩ j := by
        intro j; rw [stepPointInf_eq_stepPoint ag1 1 j, eq2]
      have ag3 : ∀ j : Fin k,
          stepLineInf (stepPointInf (stepLineInf (T4^[m] 0) 0) 1) 1 j.val =
            u ⟨4 * m + 3, by omega⟩ j := by
        intro j; rw [stepLineInf_eq_stepLine ag2 1 j, eq3]
      intro j
      rw [Function.iterate_succ_apply', T4]
      exact (stepPointInf_eq_stepPoint ag3 0 j).trans (congrFun eq4 j) |>.symm
  intro j hj
  have hfin := htrack n le_rfl ⟨j, hj⟩
  have hm0 : (4 * n) % (2 * (2 * n)) = 0 := by
    rw [show 2 * (2 * n) = 4 * n by omega, Nat.mod_self]
  simp only [hm0, hu0, Pi.zero_apply] at hfin
  exact hfin.symm

/-- Canonical binary infinite walk vertex sequence starting from `(0)` with steps
`0, 1, 1, 0, 0, 1, 1, 0, ...`. -/
def walkD2Inf (t : ℕ) : ℕ → ZMod 2 :=
  let base := T4^[t / 4] 0
  match t % 4 with
  | 0 => base
  | 1 => stepLineInf base 0
  | 2 => stepPointInf (stepLineInf base 0) 1
  | _ => stepLineInf (stepPointInf (stepLineInf base 0) 1) 1

lemma walkD2Inf_firstCoord (t : ℕ) :
    walkD2Inf t 0 = if (t / 2) % 2 = 0 then 0 else 1 := by
  have hm : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hm with h0 | h1 | h2 | h3
  · have hzt : T4^[t / 4] 0 0 = 0 := T4_iter_zero_coord (p := 0) (t / 4) rfl
    simp [walkD2Inf, h0, hzt, show (t / 2) % 2 = 0 by omega]
  · simp [walkD2Inf, h1, stepLineInf, show (t / 2) % 2 = 0 by omega]
  · simp [walkD2Inf, h2, stepPointInf, show (t / 2) % 2 ≠ 0 by omega]
  · simp [walkD2Inf, h3, stepLineInf, show (t / 2) % 2 ≠ 0 by omega]

/-- Converse: if `T4^[n] 0` vanishes on `< k` (`k ≥ 1, n ≥ 1`), then `D(k, ZMod 2)` admits a closed
non-backtracking walk of length `4 * n`. -/
theorem closedNBWalk_D2_of_T4_zero {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hzero : ∀ j < k, T4^[n] 0 j = 0) :
    ClosedNBWalk (DGraph k (ZMod 2)) (4 * n) := by
  have hk0 : 0 < k := by omega
  let v : Fin (4 * n) → Vertex k (ZMod 2) := fun i =>
    if Even i.val then
      Sum.inl (fun j => walkD2Inf i.val j.val)
    else
      Sum.inr (fun j => walkD2Inf i.val j.val)
  refine ⟨by omega, v, ?_, ?_⟩
  · intro ⟨i, hilt⟩
    have hm : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    rcases hm with h0 | h1 | h2 | h3
    · have he : Even i := ⟨2 * (i / 4), by omega⟩
      have hno : ¬ Even (i + 1) := by intro ⟨t, ht⟩; omega
      have hmod : (i + 1) % (4 * n) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hdiv : (i + 1) / 4 = i / 4 := by omega
      have hrem : (i + 1) % 4 = 1 := by omega
      dsimp only [DGraph, AdjD, v]
      simp only [hmod, he, hno, ite_true, ite_false]
      have hstep : (fun j : Fin k => walkD2Inf (i + 1) j.val) =
          stepLine (fun j : Fin k => walkD2Inf i j.val) 0 := by
        funext j
        simp only [walkD2Inf, h0, hdiv, hrem]
        exact stepLineInf_eq_stepLine (fun _ => rfl) 0 j
      rw [hstep]
      exact stepLine_adj _ 0
    · have hno : ¬ Even i := by intro ⟨t, ht⟩; omega
      have he : Even (i + 1) := ⟨2 * (i / 4) + 1, by omega⟩
      have hmod : (i + 1) % (4 * n) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hdiv : (i + 1) / 4 = i / 4 := by omega
      have hrem : (i + 1) % 4 = 2 := by omega
      dsimp only [DGraph, AdjD, v]
      simp only [hmod, he, hno, ite_true, ite_false]
      have hstep : (fun j : Fin k => walkD2Inf (i + 1) j.val) =
          stepPoint (fun j : Fin k => walkD2Inf i j.val) 1 := by
        funext j
        simp only [walkD2Inf, h1, hdiv, hrem]
        exact stepPointInf_eq_stepPoint (fun _ => rfl) 1 j
      rw [hstep]
      exact stepPoint_adj _ 1
    · have he : Even i := ⟨2 * (i / 4) + 1, by omega⟩
      have hno : ¬ Even (i + 1) := by intro ⟨t, ht⟩; omega
      have hmod : (i + 1) % (4 * n) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hdiv : (i + 1) / 4 = i / 4 := by omega
      have hrem : (i + 1) % 4 = 3 := by omega
      dsimp only [DGraph, AdjD, v]
      simp only [hmod, he, hno, ite_true, ite_false]
      have hstep : (fun j : Fin k => walkD2Inf (i + 1) j.val) =
          stepLine (fun j : Fin k => walkD2Inf i j.val) 1 := by
        funext j
        simp only [walkD2Inf, h2, hdiv, hrem]
        exact stepLineInf_eq_stepLine (fun _ => rfl) 1 j
      rw [hstep]
      exact stepLine_adj _ 1
    · have hno : ¬ Even i := by intro ⟨t, ht⟩; omega
      by_cases hlast : i + 1 < 4 * n
      · have he : Even (i + 1) := ⟨2 * (i / 4) + 2, by omega⟩
        have hmod : (i + 1) % (4 * n) = i + 1 := Nat.mod_eq_of_lt hlast
        have hdiv : (i + 1) / 4 = i / 4 + 1 := by omega
        have hrem : (i + 1) % 4 = 0 := by omega
        dsimp only [DGraph, AdjD, v]
        simp only [hmod, he, hno, ite_true, ite_false]
        have hstep : (fun j : Fin k => walkD2Inf (i + 1) j.val) =
            stepPoint (fun j : Fin k => walkD2Inf i j.val) 0 := by
          funext j
          simp only [walkD2Inf, h3, hdiv, hrem, Function.iterate_succ_apply', T4]
          exact stepPointInf_eq_stepPoint (fun _ => rfl) 0 j
        rw [hstep]
        exact stepPoint_adj _ 0
      · have hi_eq : i + 1 = 4 * n := by omega
        have hmod : (i + 1) % (4 * n) = 0 := by rw [hi_eq, Nat.mod_self]
        have hq : i / 4 + 1 = n := by omega
        dsimp only [DGraph, AdjD, v]
        simp only [hmod, hno, Even.zero, ite_true, ite_false]
        have hstep : (fun j : Fin k => walkD2Inf 0 j.val) =
            stepPoint (fun j : Fin k => walkD2Inf i j.val) 0 := by
          funext j
          have hz : T4^[i / 4 + 1] 0 j.val = 0 := by rw [hq]; exact hzero j.val j.isLt
          have hcalc : stepPoint (fun j : Fin k => walkD2Inf i j.val) 0 j =
              T4^[i / 4 + 1] 0 j.val := by
            rw [Function.iterate_succ_apply', T4]
            have := (stepPointInf_eq_stepPoint (L := walkD2Inf i) (fun _ => rfl) 0 j).symm
            simpa [walkD2Inf, h3] using this
          rw [hcalc, hz]
          rfl
        rw [hstep]
        exact stepPoint_adj _ 0
  · intro ⟨i, hilt⟩ heq
    have hfc := congrArg (firstCoord hk0) heq
    have hv_fc : ∀ a : Fin (4 * n), firstCoord hk0 (v a) = walkD2Inf a.val 0 := by
      intro a
      dsimp only [v]
      split_ifs <;> rfl
    rw [hv_fc, hv_fc, walkD2Inf_firstCoord, walkD2Inf_firstCoord] at hfc
    have hpar : (((i + 2) % (4 * n)) / 2) % 2 ≠ (i / 2) % 2 := by
      by_cases hlt2 : i + 2 < 4 * n
      · rw [Nat.mod_eq_of_lt hlt2]; omega
      · have hmod : (i + 2) % (4 * n) = i + 2 - 4 * n := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have h1 : (i + 2 - 4 * n) / 2 = 0 := by omega
        have h2 : (i / 2) % 2 = 1 := by omega
        rw [h1, h2]
        decide
    by_cases h1 : (i / 2) % 2 = 0
    · have h2 : (((i + 2) % (4 * n)) / 2) % 2 ≠ 0 := fun h => hpar (h.trans h1.symm)
      simp only [h1, h2, ite_true, ite_false] at hfc
      exact zero_ne_one hfc
    · have h1' : (i / 2) % 2 = 1 := by omega
      have h2 : (((i + 2) % (4 * n)) / 2) % 2 = 0 := by
        have hlt2 : (((i + 2) % (4 * n)) / 2) % 2 < 2 := Nat.mod_lt _ (by omega)
        omega
      simp only [h1, h2, ite_true, ite_false] at hfc
      exact one_ne_zero hfc

/-- **Complete Exact Binary Girth Law (Cheng–Chen–Tang 2014 / XCT 2023 Ex. 1), proved 100%
unconditionally in Lean 4 for every `s ≥ 3` and every `k ≥ 2` with `2^(s - 1) - 4 < k ≤ 2^s - 4`:**
`HasExactGirth (DGraph k (ZMod 2)) (2 ^ s)`. -/
theorem D2_exact_girth_law {s k : ℕ} (hs : 3 ≤ s) (hk2 : 2 ≤ k)
    (hlo : 2 ^ (s - 1) - 4 < k) (hhi : k ≤ 2 ^ s - 4) :
    HasExactGirth (DGraph k (ZMod 2)) (2 ^ s) := by
  have hpow_ge : 2 ≤ 2 ^ (s - 2) := by
    have : 2 ^ 1 ≤ 2 ^ (s - 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h4n : 4 * 2 ^ (s - 2) = 2 ^ s := by
    conv_rhs => rw [show s = (s - 2) + 2 by omega, pow_add]
    ring
  have hge : GirthAtLeast (DGraph k (ZMod 2)) (2 ^ s) := by
    intro L hL3 hLlt hc
    rcases walkD2_canonical_of_cycle hk2 hc with ⟨h4dvd, hvan⟩
    rcases h4dvd with ⟨n, rfl⟩
    have hn1 : 1 ≤ n := by omega
    have hnlt : n < 2 ^ (s - 2) := by omega
    have hdiv : 4 * n / 4 = n := by omega
    rw [hdiv] at hvan
    rcases exists_pow_two_mul_odd hn1 with ⟨r, u, hu, hnu⟩
    have hu_z2 : (u : ZMod 2) = 1 := by
      rcases hu with ⟨m, rfl⟩
      have h2z : (2 : ZMod 2) = 0 := by decide
      simp [Nat.cast_add, Nat.cast_mul, h2z]
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · have h1 := T4_iter_zero_one n
      have hu_eq : n = u := by simpa using hnu
      rw [hu_eq, hu_z2] at h1
      have hz := hvan 1 (by omega)
      rw [hu_eq] at hz
      rw [hz] at h1
      exact zero_ne_one h1
    · have hr_le : r ≤ s - 3 := by
        by_contra hgt
        have hr_ge : s - 2 ≤ r := by omega
        have hpow_le : 2 ^ (s - 2) ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr_ge
        have hu1 : 1 ≤ u := by rcases hu with ⟨m, rfl⟩; omega
        have : 2 ^ (s - 2) ≤ n := by
          rw [hnu]; exact le_trans hpow_le (Nat.le_mul_of_pos_right _ hu1)
        omega
      have hJ_lt : 4 * (2 ^ r - 1) < k := by
        have hle : 2 ^ r ≤ 2 ^ (s - 3) := Nat.pow_le_pow_right (by omega) hr_le
        have h4s : 4 * 2 ^ (s - 3) = 2 ^ (s - 1) := by
          conv_rhs => rw [show s - 1 = (s - 3) + 2 by omega, pow_add]
          ring
        have : 4 * (2 ^ r - 1) ≤ 2 ^ (s - 1) - 4 := by omega
        omega
      have hval := (T4_iter_pow_two_mul hr1 u).2
      rw [← hnu, hu_z2] at hval
      have hz := hvan (4 * (2 ^ r - 1)) hJ_lt
      rw [hz] at hval
      exact zero_ne_one hval
  have hclose : ∀ j < k, T4^[2 ^ (s - 2)] 0 j = 0 := by
    have hvan := (T4_iter_pow_two_mul (r := s - 2) (by omega) 1).1
    intro j hj
    have hlt : j < 4 * (2 ^ (s - 2) - 1) := by omega
    simpa only [mul_one] using hvan j hlt
  have hw : ClosedNBWalk (DGraph k (ZMod 2)) (2 ^ s) := by
    rw [← h4n]
    exact closedNBWalk_D2_of_T4_zero (by omega) (by omega) hclose
  exact hasExactGirth_of_closed_nb_walk_of_girthAtLeast hge hw

/-- Same exact binary girth law for the original minus-sign representation `DGraphOrig`. -/
theorem D2_exact_girth_orig_law {s k : ℕ} (hs : 3 ≤ s) (hk2 : 2 ≤ k)
    (hlo : 2 ^ (s - 1) - 4 < k) (hhi : k ≤ 2 ^ s - 4) :
    HasExactGirth (DGraphOrig k (ZMod 2)) (2 ^ s) :=
  (D2_exact_girth_law hs hk2 hlo hhi).of_iso (DGraph_iso_DGraphOrig k (ZMod 2))

/-- Exact binary girth `8` for `k ∈ [2, 4]`. -/
theorem D2_girth_eq_8 {k : ℕ} (hlo : 2 ≤ k) (hhi : k ≤ 4) :
    HasExactGirth (DGraph k (ZMod 2)) 8 :=
  D2_exact_girth_law (s := 3) (by omega) hlo (by omega) (by omega)

/-- Exact binary girth `16` for `k ∈ [5, 12]`. -/
theorem D2_girth_eq_16 {k : ℕ} (hlo : 5 ≤ k) (hhi : k ≤ 12) :
    HasExactGirth (DGraph k (ZMod 2)) 16 :=
  D2_exact_girth_law (s := 4) (by omega) (by omega) (by omega) (by omega)

/-- Exact binary girth `32` for `k ∈ [13, 28]`. -/
theorem D2_girth_eq_32 {k : ℕ} (hlo : 13 ≤ k) (hhi : k ≤ 28) :
    HasExactGirth (DGraph k (ZMod 2)) 32 :=
  D2_exact_girth_law (s := 5) (by omega) (by omega) (by omega) (by omega)

/-- Exact binary girth `64` for `k ∈ [29, 60]`. -/
theorem D2_girth_eq_64 {k : ℕ} (hlo : 29 ≤ k) (hhi : k ≤ 60) :
    HasExactGirth (DGraph k (ZMod 2)) 64 :=
  D2_exact_girth_law (s := 6) (by omega) (by omega) (by omega) (by omega)

/-- **Direct Unconditional Refutation of the Published DS28 (2026) & LSW (2017) Erratum:**
for **every** `k ≥ 13`, `girth D(k, 2) ≥ 32 > 16` and `D(k, 2)` contains **no 16-cycle**
(contradicting `D(k, 2) ≅ 2^(k-3) C_16` printed for all `k ≥ 5`). -/
theorem D2_girth_gt_16_of_ge_13 {k : ℕ} (hk : 13 ≤ k) :
    GirthAtLeast (DGraph k (ZMod 2)) 32 ∧ ¬ HasCycleOfLen (DGraph k (ZMod 2)) 16 := by
  have hge32 : GirthAtLeast (DGraph k (ZMod 2)) 32 :=
    girthAtLeast_of_le (by omega) hk (D2_girth_eq_32 le_rfl (by omega)).1
  exact ⟨hge32, hge32 16 (by omega) (by omega)⟩

/-! ### Part 2: Exact Admissible Parameter Census & Original-Model `D(11, F)` Sharpness -/

/-- Exact admissible count in characteristic 2: `Nat.card {c : F // Admissible c} = |F| - 2`. -/
theorem card_admissible_char2 (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) = 0) :
    Nat.card {c : F // Admissible c} = Fintype.card F - 2 := by
  classical
  have hiff : ∀ c : F, Admissible c ↔ c ∉ ({0, 1} : Finset F) := by
    intro c
    simp only [Admissible, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨h0, h1, _, _⟩; exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨h0, h1, ?_, ?_⟩
      · intro hcp1
        apply h1
        have : c + 1 = c - 1 := by linear_combination h2
        rw [this] at hcp1
        exact sub_eq_zero.1 hcp1
      · intro hq
        have hsq : (c - 1) * (c - 1) = 0 := by linear_combination hq + (1 - 2 * c) * h2
        exact h1 (sub_eq_zero.1 (mul_self_eq_zero.1 hsq))
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilt : Finset.univ.filter (fun c : F => Admissible c) =
      Finset.univ \ ({0, 1} : Finset F) := by
    ext c; simp [hiff]
  rw [hfilt, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Finset.card_pair (zero_ne_one : (0 : F) ≠ 1)]

/-- Exact admissible count in odd characteristic when `2` is a square in `F`:
`Nat.card {c : F // Admissible c} = |F| - 5`. -/
theorem card_admissible_odd_isSquare (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (hsq : IsSquare (2 : F)) :
    Nat.card {c : F // Admissible c} = Fintype.card F - 5 := by
  classical
  rcases hsq with ⟨r, hr⟩
  have hr_sq : r ^ 2 = 2 := by rw [sq]; exact hr.symm
  have hr_ne0 : r ≠ 0 := by intro h; rw [h] at hr_sq; norm_num at hr_sq; exact h2 hr_sq.symm
  have hbad_eq : ∀ c : F,
      ¬ Admissible c ↔ c ∈ ({0, 1, -1, r - 1, -r - 1} : Finset F) := by
    intro c
    simp only [Admissible, not_and_or, not_not, Finset.mem_insert, Finset.mem_singleton]
    have hq_iff : c ^ 2 + 2 * c - 1 = 0 ↔ c = r - 1 ∨ c = -r - 1 := by
      have hfac : c ^ 2 + 2 * c - 1 = (c + 1 - r) * (c + 1 + r) := by linear_combination hr_sq
      rw [hfac, mul_eq_zero]
      constructor
      · rintro (h | h)
        · left; linear_combination h
        · right; linear_combination h
      · rintro (rfl | rfl)
        · left; ring
        · right; ring
    have hcp1_iff : c + 1 = 0 ↔ c = -1 := by
      constructor <;> intro h <;> linear_combination h
    rw [hcp1_iff, hq_iff]
  have hne_0_1 : (0 : F) ≠ 1 := zero_ne_one
  have hne_0_m1 : (0 : F) ≠ -1 := fun h => one_ne_zero (by linear_combination h : (1 : F) = 0)
  have hne_1_m1 : (1 : F) ≠ -1 := fun h => h2 (by linear_combination h : (2 : F) = 0)
  have hne_r_1 : r ≠ 1 := fun h =>
    one_ne_zero (by linear_combination -hr_sq + (r + 1) * h : (1 : F) = 0)
  have hne_r_m1 : r ≠ -1 := fun h =>
    one_ne_zero (by linear_combination -hr_sq + (r - 1) * h : (1 : F) = 0)
  have hne_r_2 : r ≠ 2 := fun h =>
    h2 (by linear_combination hr_sq - (r + 2) * h : (2 : F) = 0)
  have hne_r_m2 : r ≠ -2 := fun h =>
    h2 (by linear_combination hr_sq - (r - 2) * h : (2 : F) = 0)
  have hne_r_mr : r ≠ -r := fun h => mul_ne_zero h2 hr_ne0 (by linear_combination h : 2 * r = 0)
  have hcard5 : ({0, 1, -1, r - 1, -r - 1} : Finset F).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      intro h; exact hne_r_mr (by linear_combination h)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hr_ne0 (by linear_combination -h)
      · exact hr_ne0 (by linear_combination h)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact hne_1_m1 h
      · exact hne_r_2 (by linear_combination -h)
      · exact hne_r_m2 (by linear_combination h)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h | h)
      · exact hne_0_1 h
      · exact hne_0_m1 h
      · exact hne_r_1 (by linear_combination -h)
      · exact hne_r_m1 (by linear_combination h)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilt : Finset.univ.filter (fun c : F => Admissible c) =
      Finset.univ \ ({0, 1, -1, r - 1, -r - 1} : Finset F) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    exact not_iff_not.1 (by simpa only [not_not] using hbad_eq c)
  rw [hfilt, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard5]

/-- Exact admissible count in odd characteristic when `2` is NOT a square in `F`:
`Nat.card {c : F // Admissible c} = |F| - 3`. -/
theorem card_admissible_odd_not_isSquare (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (hnsq : ¬ IsSquare (2 : F)) :
    Nat.card {c : F // Admissible c} = Fintype.card F - 3 := by
  classical
  have hq_ne : ∀ c : F, c ^ 2 + 2 * c - 1 ≠ 0 := by
    intro c hq
    apply hnsq
    refine ⟨c + 1, ?_⟩
    linear_combination -hq
  have hiff : ∀ c : F, Admissible c ↔ c ∉ ({0, 1, -1} : Finset F) := by
    intro c
    simp only [Admissible, Finset.mem_insert, Finset.mem_singleton, not_or]
    have hcp1 : c + 1 ≠ 0 ↔ c ≠ -1 := not_congr ⟨fun h => by linear_combination h,
      fun h => by linear_combination h⟩
    rw [hcp1]
    exact ⟨fun ⟨h0, h1, hm1, _⟩ => ⟨h0, h1, hm1⟩, fun ⟨h0, h1, hm1⟩ => ⟨h0, h1, hm1, hq_ne c⟩⟩
  have hcard3 : ({0, 1, -1} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      intro h; exact h2 (by linear_combination h : (2 : F) = 0)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact zero_ne_one h
      · exact one_ne_zero (by linear_combination h : (1 : F) = 0)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilt : Finset.univ.filter (fun c : F => Admissible c) =
      Finset.univ \ ({0, 1, -1} : Finset F) := by
    ext c; simp [hiff]
  rw [hfilt, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard3]

open scoped Classical in
/-- **Exact Admissible Parameter Census Across ALL Finite Fields `F`:**
`q - 2` if `char F = 2`, `q - 5` if `char F ≠ 2 ∧ IsSquare 2`, and `q - 3` otherwise. -/
theorem card_admissible_exact (F : Type*) [Field F] [Fintype F] :
    Nat.card {c : F // Admissible c} =
      if (2 : F) = 0 then Fintype.card F - 2
      else if IsSquare (2 : F) then Fintype.card F - 5
      else Fintype.card F - 3 := by
  split_ifs with h2 hsq
  · exact card_admissible_char2 F h2
  · exact card_admissible_odd_isSquare F h2 hsq
  · exact card_admissible_odd_not_isSquare F h2 hsq

/-- Exact admissible count `0` over `GF(2)` (`ZMod 2`). -/
theorem card_admissible_zmod2 : Nat.card {c : ZMod 2 // Admissible c} = 0 := by
  rw [card_admissible_char2 (ZMod 2) (by decide), ZMod.card]

/-- Exact admissible count `0` over `GF(3)` (`ZMod 3`). -/
theorem card_admissible_zmod3 : Nat.card {c : ZMod 3 // Admissible c} = 0 := by
  have hnsq : ¬ IsSquare (2 : ZMod 3) := by
    rintro ⟨r, hr⟩
    fin_cases r <;> revert hr <;> decide
  rw [card_admissible_odd_not_isSquare (ZMod 3) (by decide) hnsq, ZMod.card]

/-- Exact admissible count over every odd prime field `ZMod p` via quadratic reciprocity:
`p - 5` if `p % 8 ∈ {1, 7}` and `p - 3` if `p % 8 ∈ {3, 5}`. -/
theorem card_admissible_zmod_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card {c : ZMod p // Admissible c} =
      if p % 8 = 1 ∨ p % 8 = 7 then p - 5 else p - 3 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h)
    have hp_prime : p.Prime := Fact.out
    exact hp ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).1 hdvd)
  by_cases hsq : IsSquare (2 : ZMod p)
  · have hm : p % 8 = 1 ∨ p % 8 = 7 := (ZMod.exists_sq_eq_two_iff hp).1 hsq
    simp only [hm, ite_true]
    rw [card_admissible_odd_isSquare (ZMod p) h2 hsq, ZMod.card]
  · have hm : ¬ (p % 8 = 1 ∨ p % 8 = 7) := fun h => hsq ((ZMod.exists_sq_eq_two_iff hp).2 h)
    simp only [hm, ite_false]
    rw [card_admissible_odd_not_isSquare (ZMod p) h2 hsq, ZMod.card]

/-- Every finite field `F` with `|F| ≥ 4` has **at least 2** distinct admissible parameters
(sharp at `q = 4, 5, 7`, which each have exactly `2`). -/
theorem card_admissible_ge_two_of_card_ge_four (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    2 ≤ Nat.card {c : F // Admissible c} := by
  by_cases h2 : (2 : F) = 0
  · rw [card_admissible_char2 F h2]; omega
  · by_cases hsq : IsSquare (2 : F)
    · rw [card_admissible_odd_isSquare F h2 hsq]
      by_cases h7 : 7 ≤ Fintype.card F
      · omega
      · have hchar_prime : Nat.Prime (ringChar F) := by
          have h0 : ringChar F ≠ 0 := by
            intro hzero
            have hinj : Function.Injective (fun k : Fin (Fintype.card F + 1) => (k.val : F)) := by
              intro a b hab
              dsimp only at hab
              apply Fin.ext
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have hsub : ((b.val - a.val : ℕ) : F) = 0 := by
                  rw [Nat.cast_sub (le_of_lt hlt), hab, sub_self]
                have hdvd : ringChar F ∣ (b.val - a.val) := (ringChar.spec F _).1 hsub
                rw [hzero, zero_dvd_iff] at hdvd; omega
              · have hsub : ((a.val - b.val : ℕ) : F) = 0 := by
                  rw [Nat.cast_sub (le_of_lt hgt), hab, sub_self]
                have hdvd : ringChar F ∣ (a.val - b.val) := (ringChar.spec F _).1 hsub
                rw [hzero, zero_dvd_iff] at hdvd; omega
            have hle := Fintype.card_le_of_injective _ hinj
            simp only [Fintype.card_fin] at hle; omega
          exact (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right h0
        have hdvd : ringChar F ∣ Fintype.card F := by
          have hord : addOrderOf (1 : F) = ringChar F := by
            rw [addOrderOf_eq_iff hchar_prime.pos]
            refine ⟨by simp, fun m hm hpos hm0 => ?_⟩
            have hdv := (ringChar.spec F m).1 (by simpa using hm0)
            exact Nat.not_lt_of_ge (Nat.le_of_dvd hpos hdv) hm
          rw [← hord]; exact addOrderOf_dvd_card (x := (1 : F))
        have hchar_ne2 : ringChar F ≠ 2 := by
          intro hc2
          have hcast : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
          rw [hc2] at hcast; norm_num at hcast; exact h2 hcast
        have hchar_ge3 : 3 ≤ ringChar F := by have := hchar_prime.two_le; omega
        have hcard_cases : Fintype.card F = 4 ∨ Fintype.card F = 5 ∨ Fintype.card F = 6 := by omega
        rcases hcard_cases with h4 | h5 | h6
        · rw [h4] at hdvd
          have hle := Nat.le_of_dvd (by omega) hdvd
          have : ringChar F = 3 ∨ ringChar F = 4 := by omega
          rcases this with h3 | h4'
          · rw [h3] at hdvd; omega
          · rw [h4'] at hchar_prime; exact absurd hchar_prime (by decide)
        · rw [h5] at hdvd
          have hp5 : ringChar F = 5 := (Nat.prime_dvd_prime_iff_eq hchar_prime (by decide)).1 hdvd
          have h5z : (5 : F) = 0 := by
            have := ringChar.Nat.cast_ringChar (R := F); rw [hp5] at this; simpa using this
          have hinj5 : Function.Injective (fun k : Fin 5 => (k.val : F)) := by
            intro a b hab
            dsimp only at hab
            apply Fin.ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hsub : ((b.val - a.val : ℕ) : F) = 0 := by
                rw [Nat.cast_sub (le_of_lt hlt), hab, sub_self]
              have hdv := (ringChar.spec F _).1 hsub; rw [hp5] at hdv; omega
            · have hsub : ((a.val - b.val : ℕ) : F) = 0 := by
                rw [Nat.cast_sub (le_of_lt hgt), hab, sub_self]
              have hdv := (ringChar.spec F _).1 hsub; rw [hp5] at hdv; omega
          have hbij5 : Function.Bijective (fun k : Fin 5 => (k.val : F)) :=
            (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj5, by simp [h5]⟩
          rcases hsq with ⟨r, hr⟩
          rcases hbij5.2 r with ⟨k, rfl⟩
          fin_cases k
          · dsimp only at hr; norm_num at hr; exact False.elim (h2 hr)
          · dsimp only at hr; norm_num at hr
            exact False.elim (one_ne_zero (by linear_combination hr : (1 : F) = 0))
          · dsimp only at hr; norm_num at hr
            exact False.elim (h2 (by linear_combination -hr : (2 : F) = 0))
          · dsimp only at hr; norm_num at hr
            exact False.elim (h2 (by linear_combination -hr - h5z : (2 : F) = 0))
          · dsimp only at hr; norm_num at hr
            exact False.elim (one_ne_zero (by linear_combination hr + 3 * h5z : (1 : F) = 0))
        · exfalso
          have hle := Nat.le_of_dvd (by omega) hdvd
          have hp3 : ringChar F = 3 := by
            have : ringChar F = 3 ∨ ringChar F = 4 ∨ ringChar F = 5 ∨ ringChar F = 6 := by omega
            rcases this with h | h | h | h
            · exact h
            · rw [h] at hchar_prime; exact absurd hchar_prime (by decide)
            · rw [h] at hdvd; omega
            · rw [h] at hchar_prime; exact absurd hchar_prime (by decide)
          have : CharP F 3 := hp3 ▸ ringChar.charP F
          rcases FiniteField.card F 3 with ⟨d, hcd⟩
          rw [h6] at hcd
          have hd_le : (d : ℕ) ≤ 2 := by
            by_contra hgt
            have : 3 ^ 3 ≤ 3 ^ (d : ℕ) := Nat.pow_le_pow_right (by omega) (by omega)
            omega
          have hd_val : (d : ℕ) = 1 ∨ (d : ℕ) = 2 := by have := d.pos; omega
          rcases hd_val with hd1 | hd2
          · rw [hd1] at hcd; norm_num at hcd
          · rw [hd2] at hcd; norm_num at hcd
    · rw [card_admissible_odd_not_isSquare F h2 hsq]
      by_cases h5 : 5 ≤ Fintype.card F
      · omega
      · -- `|F| = 4` forces `char F = 2`, contradicting `h2`
        exfalso
        have h4 : Fintype.card F = 4 := by omega
        have hchar_prime : Nat.Prime (ringChar F) := by
          have h0 : ringChar F ≠ 0 := by
            intro hzero
            have hinj : Function.Injective (fun k : Fin (Fintype.card F + 1) => (k.val : F)) := by
              intro a b hab
              dsimp only at hab
              apply Fin.ext
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have hsub : ((b.val - a.val : ℕ) : F) = 0 := by
                  rw [Nat.cast_sub (le_of_lt hlt), hab, sub_self]
                have hdvd : ringChar F ∣ (b.val - a.val) := (ringChar.spec F _).1 hsub
                rw [hzero, zero_dvd_iff] at hdvd; omega
              · have hsub : ((a.val - b.val : ℕ) : F) = 0 := by
                  rw [Nat.cast_sub (le_of_lt hgt), hab, sub_self]
                have hdvd : ringChar F ∣ (a.val - b.val) := (ringChar.spec F _).1 hsub
                rw [hzero, zero_dvd_iff] at hdvd; omega
            have hle := Fintype.card_le_of_injective _ hinj
            simp only [Fintype.card_fin] at hle; omega
          exact (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right h0
        have hdvd : ringChar F ∣ 4 := by
          have hord : addOrderOf (1 : F) = ringChar F := by
            rw [addOrderOf_eq_iff hchar_prime.pos]
            refine ⟨by simp, fun m hm hpos hm0 => ?_⟩
            have hdv := (ringChar.spec F m).1 (by simpa using hm0)
            exact Nat.not_lt_of_ge (Nat.le_of_dvd hpos hdv) hm
          rw [← hord, ← h4]; exact addOrderOf_dvd_card (x := (1 : F))
        have hle := Nat.le_of_dvd (by omega) hdvd
        have hge2 := hchar_prime.two_le
        have hp2 : ringChar F = 2 := by
          interval_cases h : ringChar F
          · rfl
          · omega
          · exact absurd hchar_prime (by decide)
        have hcast : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
        rw [hp2] at hcast; norm_num at hcast; exact h2 hcast

/-- Distinct parameters `c₁ ≠ c₂` yield genuinely distinct 14-walks `walk14 c₁ ≠ walk14 c₂`
in `D(10, F)` (vertex `v₅` has first coordinate `c`). -/
theorem walk14_injective_in_param {F : Type*} [Field F] {c₁ c₂ : F}
    (h : walk14 c₁ = walk14 c₂) : c₁ = c₂ := by
  have h5 := congrFun h ⟨5, by omega⟩
  have hfc := congrArg (firstCoord (by omega : 0 < 10)) h5
  simpa [walk14, firstCoord, w14_5] using hfc

/-- Original minus-sign model `DGraphOrig 11 F` sharpness: the lifted 14-walk fails to close at
coordinate 11 with the exact same nonzero residue `c * (c - 1) / (c ^ 2 + 2 * c - 1)` (since
`signFactor F 10 = (-1) ^ ((10 + 1) / 4) = (-1) ^ 2 = 1`). -/
theorem walk14_D11_orig_fails_closure {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    let a := (1 - c) / (1 + c)
    let b := (c - 1) / (c ^ 2 + 2 * c - 1)
    let d := 2 * c / (c ^ 2 + 2 * c - 1)
    let p0 : Fin 11 → F := 0
    let p14 := stepPoint (stepLine (stepPoint (stepLine (stepPoint (stepLine
      (stepPoint (stepLine (stepPoint (stepLine (stepPoint (stepLine (stepPoint
      (stepLine p0 0) 1) a) b) c) d) a) b) c) 0) 0) 1) 1) 0
    signFlipVec p14 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) ∧
    signFlipVec p14 ≠ 0 := by
  rcases walk14_D11_fails_closure hc with ⟨hval, hne⟩
  have hsf : signFactor F 10 = 1 := by
    simp [signFactor]
  refine ⟨?_, ?_⟩
  · simpa [signFlipVec, hsf] using hval
  · intro hz
    apply hne
    have hinv := congrArg signFlipVec hz
    rw [signFlipVec_involutive] at hinv
    have hsf0 : signFlipVec (0 : Fin 11 → F) = 0 := by
      funext j; simp [signFlipVec]
    exact hinv.trans hsf0

/-! ### Part 3: Explicit `GaloisField p n` Bridges & DS28 Tables 7–12 Cells (`q = 27, 32`) -/

/-- Direct unconditional `GaloisField p n` bridge for `D(9, p^n)` and `D(10, p^n)` whenever
`4 ≤ p ^ n` (`n ≠ 0`). -/
theorem D9_D10_exact_girth_14_galoisField (p n : ℕ) [Fact p.Prime]
    (hn : n ≠ 0) (hq : 4 ≤ p ^ n) :
    HasExactGirth (DGraph 9 (GaloisField p n)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField p n)) 14 := by
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  have hcard : 4 ≤ Fintype.card (GaloisField p n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
    exact hq
  exact D9_D10_exact_girth_14_all_q_ge_4 (GaloisField p n) hcard

/-- **DS28 Table 7 Blank Cells Filled Unconditionally (`q = 27, 32`):**
`girth D(9, 27) = girth D(10, 27) = 14` and `girth D(9, 32) = girth D(10, 32) = 14`. -/
theorem DS28_table7_blank_cells_27_32 :
    HasExactGirth (DGraph 9 (GaloisField 3 3)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField 3 3)) 14 ∧
    HasExactGirth (DGraph 9 (GaloisField 2 5)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField 2 5)) 14 := by
  have h27 := D9_D10_exact_girth_14_galoisField 3 3 (by decide) (by decide)
  have h32 := D9_D10_exact_girth_14_galoisField 2 5 (by decide) (by decide)
  exact ⟨h27.1, h27.2, h32.1, h32.2⟩

/-- **DS28 Tables 8 & 10 Six Ungrounded Cells Supplied Rigorously (`q = 27, 32`):**
supplies the missing `D(10, q) = 14` foundation for DS28's six printed entries
`(23, 27), (24, 27), (23, 32), (24, 32) → 28` and `(51, 27), (51, 32) → 56`. -/
theorem DS28_tables8_10_six_ungrounded_cells
    (h2_27 : XCTThm2Part2Hyp (GaloisField 3 3))
    (h3_27 : XCTThm2Part3Hyp (GaloisField 3 3))
    (h2_32 : XCTThm2Part2Hyp (GaloisField 2 5))
    (h3_32 : XCTThm2Part3Hyp (GaloisField 2 5)) :
    HasExactGirth (DGraph 23 (GaloisField 3 3)) 28 ∧
    HasExactGirth (DGraph 24 (GaloisField 3 3)) 28 ∧
    HasExactGirth (DGraph 51 (GaloisField 3 3)) 56 ∧
    HasExactGirth (DGraph 23 (GaloisField 2 5)) 28 ∧
    HasExactGirth (DGraph 24 (GaloisField 2 5)) 28 ∧
    HasExactGirth (DGraph 51 (GaloisField 2 5)) 56 := by
  let _ : Fintype (GaloisField 3 3) := Fintype.ofFinite _
  let _ : Fintype (GaloisField 2 5) := Fintype.ofFinite _
  have hc27 : 4 ≤ Fintype.card (GaloisField 3 3) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 3 (by decide)]; decide
  have hc32 : 4 ≤ Fintype.card (GaloisField 2 5) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 5 (by decide)]; decide
  rcases cascade_XCT_23_24_51 (GaloisField 3 3) hc27 h2_27 h3_27 with ⟨a1, a2, a3⟩
  rcases cascade_XCT_23_24_51 (GaloisField 2 5) hc32 h2_32 h3_32 with ⟨b1, b2, b3⟩
  exact ⟨a1, a2, a3, b1, b2, b3⟩

/-- **DS28 Tables 9 & 12 New Characteristic-3 Cells (`q = 27`):**
`(37, 27), (38, 27) → 42` and `(79, 27), (80, 27) → 84`. -/
theorem DS28_table9_12_char3_new_cells_27
    (h55 : DS28Thm55Hyp (GaloisField 3 3) 3)
    (h2 : XCTThm2Part2Hyp (GaloisField 3 3))
    (h3 : XCTThm2Part3Hyp (GaloisField 3 3)) :
    HasExactGirth (DGraph 37 (GaloisField 3 3)) 42 ∧
    HasExactGirth (DGraph 38 (GaloisField 3 3)) 42 ∧
    HasExactGirth (DGraph 79 (GaloisField 3 3)) 84 ∧
    HasExactGirth (DGraph 80 (GaloisField 3 3)) 84 := by
  let _ : Fintype (GaloisField 3 3) := Fintype.ofFinite _
  have hc27 : 4 ≤ Fintype.card (GaloisField 3 3) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 3 (by decide)]; decide
  exact cascade_char3_cells_37_38_79_80 (GaloisField 3 3) hc27 h55 h2 h3

/-- **DS28 Table 10 Characteristic-2 Cell (`q = 32`):** `(51, 32), (52, 32) → 56` from the
char-2 ray at `t = 3`. -/
theorem DS28_table10_char2_cell_52_32
    (h3 : XCTThm2Part3Hyp (GaloisField 2 5))
    (h4 : XCTThm2Part4Char2Hyp (GaloisField 2 5)) :
    HasExactGirth (DGraph 51 (GaloisField 2 5)) 56 ∧
    HasExactGirth (DGraph 52 (GaloisField 2 5)) 56 := by
  let _ : Fintype (GaloisField 2 5) := Fintype.ofFinite _
  have hc32 : 4 ≤ Fintype.card (GaloisField 2 5) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 5 (by decide)]; decide
  simpa using cascade_char2_ray (GaloisField 2 5) hc32 h3 h4 3 (by omega)

/-! ### Part 4: Exact 19-Entry Count & Extended Pure-Kernel Unconditional `D(k, 3)` Girths -/

/-- Exact set of `19` newly determined `D(k, 3)` indices for `k ≤ 50` in `R19-4-2`. -/
def R19_4_2_new_k_set : Finset ℕ :=
  Finset.Icc 27 30 ∪ Finset.Icc 33 34 ∪ Finset.Icc 36 39 ∪ Finset.Icc 40 42 ∪ Finset.Icc 43 48

/-- Exact cardinality `19` of the newly determined `R19-4-2` set (correcting the internal `"23"`
prose slip in early records). -/
theorem R19_4_2_new_k_set_card : R19_4_2_new_k_set.card = 19 := by decide

/-- Exact girth lookup function for the `19` newly determined `R19-4-2` entries. -/
def R19_4_2_girth (k : ℕ) : ℕ :=
  if k ≤ 30 then 36
  else if k ≤ 34 then 40
  else if k ≤ 39 then 48
  else if k ≤ 42 then 50
  else 52

/-- Unified exact-girth theorem over all `19` elements of `R19_4_2_new_k_set`. -/
theorem R19_4_2_exact_table_19_entries (hbfs : R19_4_2_BFSLowerBounds) :
    ∀ k ∈ R19_4_2_new_k_set, HasExactGirth (DGraph k (ZMod 3)) (R19_4_2_girth k) := by
  rcases R19_4_2_exact_table_from_bfs hbfs with ⟨h1, h2, h3, h4, h5⟩
  intro k hk
  simp only [R19_4_2_new_k_set, Finset.mem_union, Finset.mem_Icc] at hk
  rcases hk with ((((hk | hk) | hk) | hk) | hk)
  · have hg : R19_4_2_girth k = 36 := by simp [R19_4_2_girth, hk.2]
    rw [hg]; exact h1 k hk.1 hk.2
  · have hg : R19_4_2_girth k = 40 := by
      simp [R19_4_2_girth, show ¬ k ≤ 30 by omega, hk.2]
    rw [hg]; exact h2 k hk.1 hk.2
  · have hg : R19_4_2_girth k = 48 := by
      simp [R19_4_2_girth, show ¬ k ≤ 30 by omega, show ¬ k ≤ 34 by omega, hk.2]
    rw [hg]; exact h3 k hk.1 hk.2
  · have hg : R19_4_2_girth k = 50 := by
      simp [R19_4_2_girth, show ¬ k ≤ 30 by omega, show ¬ k ≤ 34 by omega,
        show ¬ k ≤ 39 by omega, hk.2]
    rw [hg]; exact h4 k hk.1 hk.2
  · have hg : R19_4_2_girth k = 52 := by
      simp [R19_4_2_girth, show ¬ k ≤ 30 by omega, show ¬ k ≤ 34 by omega,
        show ¬ k ≤ 39 by omega, show ¬ k ≤ 42 by omega]
    rw [hg]; exact h5 k hk.1 hk.2

/-! #### Pure-Kernel Unconditional `D(k, 3)` Witnesses Completing 100% of Tight `k ≤ 51`
and Sharpening / Filling DS28 Table 4 Beyond `k = 51` -/

/-- Exact 36-cycle witness for `D(32, 3)` (`wit_D3_k8` tripled). -/
def wit_D3_k32 : List (ZMod 3) := wit_D3_k8 ++ wit_D3_k8 ++ wit_D3_k8

/-- Exact 54-cycle witness for `D(50, 3)` (`wit_D3_k14` tripled). -/
def wit_D3_k50 : List (ZMod 3) := wit_D3_k14 ++ wit_D3_k14 ++ wit_D3_k14

/-- Exact 56-cycle witness for `D(51, 3)` (Xu–Cheng–Tang doubling of `wit_D3_k24`). -/
def wit_D3_k51 : List (ZMod 3) :=
  [0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 2, 0, 1, 1, 0,
   0, 2, 1, 1, 0, 2, 1, 0, 0, 2, 1, 1, 0, 2, 1, 1, 0, 2, 1, 1, 0, 2, 1, 0, 0, 1, 1, 2]

/-- Exact 60-cycle witness for `D(56, 3)` (`wit_D3_k16` tripled). -/
def wit_D3_k56 : List (ZMod 3) := wit_D3_k16 ++ wit_D3_k16 ++ wit_D3_k16

/-- Exact 72-cycle witness for `D(67, 3)` (`wit_D3_k19` tripled). -/
def wit_D3_k67 : List (ZMod 3) := wit_D3_k19 ++ wit_D3_k19 ++ wit_D3_k19

/-- Exact 84-cycle witness for `D(80, 3)` (`wit_D3_k24` tripled). -/
def wit_D3_k80 : List (ZMod 3) := wit_D3_k24 ++ wit_D3_k24 ++ wit_D3_k24

/-- Exact 104-cycle witness for `D(99, 3)` (Xu–Cheng–Tang doubling of `wit_D3_k48`). -/
def wit_D3_k99 : List (ZMod 3) :=
  [0, 0, 1, 2, 0, 0, 1, 1, 0, 2, 1, 1, 0, 0, 1, 2, 0, 0, 1, 1, 0, 0, 1, 1, 0, 2,
   1, 0, 0, 2, 1, 1, 0, 2, 1, 1, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 1, 1, 0, 2, 1, 1,
   0, 2, 1, 0, 0, 2, 1, 1, 0, 0, 1, 1, 0, 2, 1, 0, 0, 2, 1, 1, 0, 2, 1, 1, 0, 0,
   1, 2, 0, 0, 1, 1, 0, 0, 1, 1, 0, 2, 1, 1, 0, 2, 1, 0, 0, 2, 1, 1, 0, 0, 1, 1]

/-- Exact 108-cycle witness for `D(104, 3)` (`wit_D3_k30` tripled). -/
def wit_D3_k104 : List (ZMod 3) := wit_D3_k30 ++ wit_D3_k30 ++ wit_D3_k30

theorem D3_k32_upper_36 : GirthAtMost (DGraph 32 (ZMod 3)) 36 :=
  girthAtMost_D3_of_checkWalkD3 32 wit_D3_k32 (by decide)

theorem D3_k31_k32_exact_36 :
    HasExactGirth (DGraph 31 (ZMod 3)) 36 ∧ HasExactGirth (DGraph 32 (ZMod 3)) 36 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 15) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k32_upper_36),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 16) (by omega) (ZMod 3)) D3_k32_upper_36⟩

theorem D3_k35_exact_40 : HasExactGirth (DGraph 35 (ZMod 3)) 40 :=
  hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 17) (by omega) (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 35 wit_D3_k34 (by decide))

theorem D3_k50_upper_54 : GirthAtMost (DGraph 50 (ZMod 3)) 54 :=
  girthAtMost_D3_of_checkWalkD3 50 wit_D3_k50 (by decide)

theorem D3_k49_k50_exact_54 :
    HasExactGirth (DGraph 49 (ZMod 3)) 54 ∧ HasExactGirth (DGraph 50 (ZMod 3)) 54 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 24) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k50_upper_54),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 25) (by omega) (ZMod 3)) D3_k50_upper_54⟩

theorem D3_k51_exact_56 : HasExactGirth (DGraph 51 (ZMod 3)) 56 :=
  hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 25) (by omega) (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 51 wit_D3_k51 (by decide))

theorem D3_k56_upper_60 : GirthAtMost (DGraph 56 (ZMod 3)) 60 :=
  girthAtMost_D3_of_checkWalkD3 56 wit_D3_k56 (by decide)

/-- Unconditional exact girth `D(55, 3) = D(56, 3) = 60` (sharpening DS28 Table 4's `55: ≤ 68`
to exact `60` and filling blank `56`). -/
theorem D3_k55_k56_exact_60 :
    HasExactGirth (DGraph 55 (ZMod 3)) 60 ∧ HasExactGirth (DGraph 56 (ZMod 3)) 60 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 27) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k56_upper_60),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 28) (by omega) (ZMod 3)) D3_k56_upper_60⟩

/-- Unconditional tightening of the first open case of DS28 Problem 47 (`k = 52`):
`56 ≤ girth D(52, 3) ≤ 60` (improved from `≤ 68`, leaving only `{56, 58, 60}`). -/
theorem D3_k52_bounds_56_60 :
    GirthAtLeast (DGraph 52 (ZMod 3)) 56 ∧ GirthAtMost (DGraph 52 (ZMod 3)) 60 :=
  ⟨D_even_girthAtLeast (k := 26) (by omega) (ZMod 3),
   girthAtMost_of_le (by omega) (by omega) D3_k56_upper_60⟩

theorem D3_k67_exact_72 : HasExactGirth (DGraph 67 (ZMod 3)) 72 :=
  hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 33) (by omega) (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 67 wit_D3_k67 (by decide))

theorem D3_k80_upper_84 : GirthAtMost (DGraph 80 (ZMod 3)) 84 :=
  girthAtMost_D3_of_checkWalkD3 80 wit_D3_k80 (by decide)

/-- Unconditional exact girth `D(79, 3) = D(80, 3) = 84` (sharpening DS28 Table 4's `79: ≤ 96`
to exact `84` and filling blank `80`). -/
theorem D3_k79_k80_exact_84 :
    HasExactGirth (DGraph 79 (ZMod 3)) 84 ∧ HasExactGirth (DGraph 80 (ZMod 3)) 84 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 39) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k80_upper_84),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 40) (by omega) (ZMod 3)) D3_k80_upper_84⟩

/-- **Genuinely New Unconditional Exact Girth `D(99, 3) = 104`** (enabled by our new `R19-4-2`
result `D(48, 3) = 52`; blank in DS28 Table 4 and XCT Table 1). -/
theorem D3_k99_exact_104 : HasExactGirth (DGraph 99 (ZMod 3)) 104 :=
  hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 49) (by omega) (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 99 wit_D3_k99 (by decide))

theorem D3_k104_upper_108 : GirthAtMost (DGraph 104 (ZMod 3)) 108 :=
  girthAtMost_D3_of_checkWalkD3 104 wit_D3_k104 (by decide)

theorem D3_k103_k104_exact_108 :
    HasExactGirth (DGraph 103 (ZMod 3)) 108 ∧ HasExactGirth (DGraph 104 (ZMod 3)) 108 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 51) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k104_upper_108),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 52) (by omega) (ZMod 3)) D3_k104_upper_108⟩

/-- DS28 Theorem 55 lift from our unconditional `D(35, 3) = 40`:
`girth D(115, 3) = 120` (filling blank `115` and sharpening `111: ≤ 136` to `≤ 120`). -/
theorem cascade_D3_115_exact_120 (h55 : DS28Thm55Hyp (ZMod 3) 3) :
    HasExactGirth (DGraph 115 (ZMod 3)) 120 ∧ GirthAtMost (DGraph 111 (ZMod 3)) 120 := by
  have hconj : Conjecture46At 35 (ZMod 3) := by
    have ho : Odd 35 := by decide
    simpa [Conjecture46At, ho] using D3_k35_exact_40
  have hlift := h55 35 (by omega) hconj
  have ho : Odd 35 := by decide
  have h115 : HasExactGirth (DGraph 115 (ZMod 3)) 120 := by
    simpa [ho] using hlift.1
  exact ⟨h115, girthAtMost_of_le (by omega) (by omega) h115.girthAtMost⟩

/-- New infinite characteristic-3 ray enabled by our unconditional `D(48, 3) = 52` under
`DS28Thm55Hyp (ZMod 3) 3`: for every `s : ℕ`,
`girth D(52 * 3^s - 5, 3) = girth D(52 * 3^s - 4, 3) = 52 * 3^s` (at `s = 1`: `151, 152 → 156`,
genuinely new and blank in DS28 Table 4, sharpening `143: ≤ 160` to `≤ 156`). -/
theorem cascade_D3_52_ray (h55 : DS28Thm55Hyp (ZMod 3) 3) :
    ∀ s : ℕ,
      HasExactGirth (DGraph (52 * 3 ^ s - 5) (ZMod 3)) (52 * 3 ^ s) ∧
      HasExactGirth (DGraph (52 * 3 ^ s - 4) (ZMod 3)) (52 * 3 ^ s) := by
  intro s
  induction s with
  | zero => simpa using D3_k47_k48_exact_52
  | succ s ih =>
    have hpow : 1 ≤ 3 ^ s := Nat.one_le_pow _ _ (by omega)
    let k := 52 * 3 ^ s - 4
    have hk3 : 3 ≤ k := by omega
    have hk_even : ¬ Odd k := by intro ⟨m, hm⟩; omega
    have hk_mod4 : k % 4 ≠ 3 := by omega
    have hconj : Conjecture46At k (ZMod 3) := by
      simp only [Conjecture46At, hk_even, ite_false]
      have heq : k + 4 = 52 * 3 ^ s := by omega
      rw [heq]; exact ih.2
    have hlift := h55 k hk3 hconj
    dsimp only at hlift
    have hif : (if Odd k then k + 5 else k + 4) = k + 4 := by simp [hk_even]
    have hg : k + 4 = 52 * 3 ^ s := by omega
    have h3g : 3 * (k + 4) = 52 * 3 ^ (s + 1) := by rw [hg, pow_succ]; ring
    rw [hif, h3g] at hlift
    exact ⟨hlift.1, hlift.2 hk_mod4⟩

end LazebnikUstimenko
