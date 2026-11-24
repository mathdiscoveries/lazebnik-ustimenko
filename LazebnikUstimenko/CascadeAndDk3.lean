module

public import LazebnikUstimenko.Cycle14
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Cascade Theorems (`{14 p^s - 4}`, Char-2 Ray, XCT Thm 2) and `D(k, 3)` Framework (R19-4-2)

This file formalizes two major companions to the unconditional exact-girth theorem
`D9_D10_exact_girth_14_all_q_ge_4`:

1. **Conjecture 46 & Cascade Bridges (`R19-4-1` companions):**
   * `conj46_at_9_and_10`: 100% unconditional proof of DS28 Conjecture 46 at `k = 9, 10` for all
     finite fields of cardinality `q ≥ 4`.
   * Explicit, transparent literature-lifting hypotheses (`XCTThm2Part2Hyp`, `XCTThm2Part3Hyp`,
     `XCTThm2Part4Char2Hyp`, `DS28Thm55Hyp`) cleanly separated from kernel-proved steps:
     - `cascade_XCT_23_24_51`: `girth D(23, q) = girth D(24, q) = 28` and `girth D(51, q) = 56`
       for every prime power `q ≥ 4` (Xu–Cheng–Tang 2023 Theorem 2 parts 2–3).
     - `cascade_char2_ray`: for every finite field of characteristic 2 with `q ≥ 4` and every
       `t ≥ 1`, `girth D(7 * 2^t - 5, q) = girth D(7 * 2^t - 4, q) = 7 * 2^t`
       (Xu–Cheng–Tang 2023 Corollary 1; fills `(52, 32)`).
     - `cascade_all_char_ps`: for every finite field of characteristic `p ≥ 2` with `q ≥ 4` and
       every `s : ℕ`, `girth D(14 * p^s - 5, q) = girth D(14 * p^s - 4, q) = 14 * p^s`
       (Sun 2017 / DS28 Theorem 55; at `p = 3, q = 27`, fills `(37, 27), (38, 27) → 42`, and
       with XCT Thm 2 gives `(79, 27), (80, 27) → 84`).

2. **Pure-Kernel `D(k, 3)` (`ZMod 3`) Verifier and `R19-4-2` Framework:**
   * Linear-time pure-kernel walk checker `checkWalkD3` on `List (ZMod 3)` + unconditional
     soundness proof `checkWalkD3_sound` (ZERO `native_decide`).
   * **13 Exact `D(k, 3)` Girths proved 100% unconditionally in Lean 4's kernel** (combining
     kernel-verified cycle witnesses with our unconditional Lazebnik–Ustimenko lower bound):
     `k = 2 (6)`, `3 (8)`, `7, 8 (12)`, `13, 14 (18)`, `15, 16 (20)` (refuting Mukherjee's 22),
     `19 (24)`, `23, 24 (28)`, and **`k = 47, 48 (52)`** (two new `R19-4-2` Table 4 entries!).
   * **All 5 new `R19-4-2` upper-bound ranges proved 100% unconditionally in Lean 4's kernel**:
     `k = 27..30 (≤ 36)`, `33..34 (≤ 40)`, `36..39 (≤ 48)`, `40..42 (≤ 50)`, `43..48 (≤ 52)`.
   * `R19_4_2_exact_table_from_bfs`: clean bridge combining the kernel-verified upper bounds and
     monotonicity with the 5 external exhaustive-BFS lower-bound hypotheses (`R19-4-2_BFSLowerBounds`)
     to yield exact girths for all 23 newly determined `R19-4-2` entries.
-/

@[expose] public section

namespace LazebnikUstimenko

/-! ### Part 1: DS28 Conjecture 46 & Cascade Bridges -/

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- DS28 Conjecture 46 at index `k` over `F`: `girth D(k, F) = k + 5` (odd `k`) or `k + 4` (even `k`). -/
def Conjecture46At (k : ℕ) (F : Type*) [CommRing F] : Prop :=
  HasExactGirth (DGraph k F) (if Odd k then k + 5 else k + 4)

/-- Unconditional proof of DS28 Conjecture 46 at `k = 9` and `k = 10` for every finite field
of cardinality `q ≥ 4`. -/
theorem conj46_at_9_and_10 (F : Type*) [Field F] [Fintype F] (hcard : 4 ≤ Fintype.card F) :
    Conjecture46At 9 F ∧ Conjecture46At 10 F := by
  rcases D9_D10_exact_girth_14_all_q_ge_4 F hcard with ⟨h9, h10⟩
  have ho9 : Odd 9 := by decide
  have hno10 : ¬ Odd 10 := by decide
  exact ⟨by simpa [Conjecture46At, ho9] using h9, by simpa [Conjecture46At, hno10] using h10⟩

/-- Sharpness of `q ≥ 4` for `Admissible`: over `GF(3)` (`ZMod 3`), no element is admissible
(`0`, `1`, and `2 = -1` are all excluded, matching `girth D(9, 3) = 18 > 14`). -/
theorem no_admissible_zmod3 [Fact (Nat.Prime 3)] (c : ZMod 3) : ¬ Admissible c := by
  fin_cases c
  · intro h; exact h.1 rfl
  · intro h; exact h.2.1 rfl
  · intro h; exact h.2.2.1 rfl

/-- Xu–Cheng–Tang (2023, arXiv:2209.01896) Theorem 2, part 2 (via `Λ_{k,q} ≅ D(k,q)`):
for `n ≥ 3`, `girth D(2 n - 4, F) = 2 n → girth D(4 n - 5, F) = 4 n`. -/
def XCTThm2Part2Hyp (F : Type*) [CommRing F] : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    HasExactGirth (DGraph (2 * n - 4) F) (2 * n) →
    HasExactGirth (DGraph (4 * n - 5) F) (4 * n)

/-- Xu–Cheng–Tang (2023) Theorem 2, part 3:
for `w ≥ 1`, `girth D(4 w - 2, F) = 4 w + 2 → girth D(8 w, F) = 8 w + 4`. -/
def XCTThm2Part3Hyp (F : Type*) [CommRing F] : Prop :=
  ∀ w : ℕ, 1 ≤ w →
    HasExactGirth (DGraph (4 * w - 2) F) (4 * w + 2) →
    HasExactGirth (DGraph (8 * w) F) (8 * w + 4)

/-- Xu–Cheng–Tang (2023) Theorem 2, part 4 (characteristic 2):
for `w ≥ 1, n ≥ 3`, `girth D(4 w, F) ≤ 2 n → girth D(8 w + 4, F) ≤ 4 n`. -/
def XCTThm2Part4Char2Hyp (F : Type*) [CommRing F] : Prop :=
  ∀ w n : ℕ, 1 ≤ w → 3 ≤ n →
    GirthAtMost (DGraph (4 * w) F) (2 * n) →
    GirthAtMost (DGraph (8 * w + 4) F) (4 * n)

/-- Sun (2017) / DS28 Theorem 55 lifting hypothesis at characteristic `p`:
if `k ≥ 3` satisfies Conjecture 46 with girth `g`, then `girth D(p g - 5, F) = p g`, and if
`k % 4 ≠ 3`, also `girth D(p g - 4, F) = p g`. -/
def DS28Thm55Hyp (F : Type*) [CommRing F] (p : ℕ) : Prop :=
  ∀ k : ℕ, 3 ≤ k → Conjecture46At k F →
    let g := if Odd k then k + 5 else k + 4
    HasExactGirth (DGraph (p * g - 5) F) (p * g) ∧
    (k % 4 ≠ 3 → HasExactGirth (DGraph (p * g - 4) F) (p * g))

/-- Helper: combining `GirthAtLeast G m` and `GirthAtMost G m` yields `HasExactGirth G m`. -/
lemma hasExactGirth_of_le_ge {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hge : GirthAtLeast G m) (hle : GirthAtMost G m) : HasExactGirth G m := by
  rcases hle with ⟨r, hr3, hrm, hcr⟩
  have hreq : r = m := by
    by_contra hne
    exact hge r hr3 (lt_of_le_of_ne hrm hne) hcr
  subst hreq
  exact ⟨hge, hcr⟩

/-- Xu–Cheng–Tang Theorem 2 cascade from `D(10, q) = 14`:
for every finite field `F` with `q ≥ 4`, `girth D(23, F) = girth D(24, F) = 28` and
`girth D(51, F) = 56` (parameterized explicitly by XCT Thm 2 parts 2–3). -/
theorem cascade_XCT_23_24_51 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F)
    (h2 : XCTThm2Part2Hyp F) (h3 : XCTThm2Part3Hyp F) :
    HasExactGirth (DGraph 23 F) 28 ∧
    HasExactGirth (DGraph 24 F) 28 ∧
    HasExactGirth (DGraph 51 F) 56 := by
  have h10 : HasExactGirth (DGraph 10 F) 14 := (D9_D10_exact_girth_14_all_q_ge_4 F hcard).2
  have h23 : HasExactGirth (DGraph 23 F) 28 := by
    simpa using h2 7 (by omega) (by simpa using h10)
  have h24 : HasExactGirth (DGraph 24 F) 28 := by
    simpa using h3 3 (by omega) (by simpa using h10)
  have h51 : HasExactGirth (DGraph 51 F) 56 := by
    simpa using h2 14 (by omega) (by simpa using h24)
  exact ⟨h23, h24, h51⟩

/-- Characteristic-2 infinite ray (Xu–Cheng–Tang 2023 Corollary 1 from `D(10, 2^m) = 14`):
for every finite field `F` of characteristic 2 with `q ≥ 4` and every `t ≥ 1`,
`girth D(7 * 2^t - 5, F) = girth D(7 * 2^t - 4, F) = 7 * 2^t`. -/
theorem cascade_char2_ray (F : Type*) [Field F] [Fintype F] [CharP F 2]
    (hcard : 4 ≤ Fintype.card F)
    (h3 : XCTThm2Part3Hyp F) (h4 : XCTThm2Part4Char2Hyp F) :
    ∀ t : ℕ, 1 ≤ t →
      HasExactGirth (DGraph (7 * 2 ^ t - 5) F) (7 * 2 ^ t) ∧
      HasExactGirth (DGraph (7 * 2 ^ t - 4) F) (7 * 2 ^ t) := by
  have hbase : HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 :=
    D9_D10_exact_girth_14_all_q_ge_4 F hcard
  have hstep24 : HasExactGirth (DGraph 24 F) 28 := by
    simpa using h3 3 (by omega) (by simpa using hbase.2)
  -- First prove the even branch `D(7 * 2^t - 4, F) = 7 * 2^t` for all `t ≥ 1`
  have heven : ∀ t : ℕ, 1 ≤ t → HasExactGirth (DGraph (7 * 2 ^ t - 4) F) (7 * 2 ^ t) := by
    intro t ht
    induction t with
    | zero => omega
    | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      · simpa using hbase.2
      · by_cases ht2 : t = 1
        · subst ht2; simpa using hstep24
        · have ht_ge2 : 2 ≤ t := by omega
          have hprev := ih ht1
          have hpow_ge4 : 4 ≤ 2 ^ t := by
            have : 2 ^ 2 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht_ge2
            omega
          have hdvd4 : 4 ∣ 2 ^ t := by
            obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
            rw [pow_add]; exact ⟨2 ^ u, by ring⟩
          rcases hdvd4 with ⟨q, hq⟩
          have hq1 : 1 ≤ q := by omega
          let w := 7 * q - 1
          let n := 7 * (2 ^ (t - 1))
          have hw1 : 1 ≤ w := by omega
          have hn3 : 3 ≤ n := by
            have : 1 ≤ 2 ^ (t - 1) := Nat.one_le_pow _ _ (by omega)
            omega
          have h4w : 4 * w = 7 * 2 ^ t - 4 := by omega
          have h2n : 2 * n = 7 * 2 ^ t := by
            have : 2 * 2 ^ (t - 1) = 2 ^ t := by
              conv_rhs => rw [show t = (t - 1) + 1 by omega, pow_succ, mul_comm]
            dsimp only [n]; omega
          have h8w4 : 8 * w + 4 = 7 * 2 ^ (t + 1) - 4 := by
            rw [pow_succ]; omega
          have h4n : 4 * n = 7 * 2 ^ (t + 1) := by
            rw [pow_succ]; omega
          have hle_prev : GirthAtMost (DGraph (4 * w) F) (2 * n) := by
            rw [h4w, h2n]; exact hprev.girthAtMost
          have hle_next : GirthAtMost (DGraph (7 * 2 ^ (t + 1) - 4) F) (7 * 2 ^ (t + 1)) := by
            rw [← h8w4, ← h4n]; exact h4 w n hw1 hn3 hle_prev
          have hge_next : GirthAtLeast (DGraph (7 * 2 ^ (t + 1) - 4) F) (7 * 2 ^ (t + 1)) := by
            have hk : 1 ≤ 7 * (2 ^ t) - 2 := by omega
            have heq1 : 2 * (7 * 2 ^ t - 2) = 7 * 2 ^ (t + 1) - 4 := by rw [pow_succ]; omega
            have heq2 : 2 * (7 * 2 ^ t - 2) + 4 = 7 * 2 ^ (t + 1) := by rw [pow_succ]; omega
            have h := D_even_girthAtLeast hk F
            rw [heq2, heq1] at h
            exact h
          exact hasExactGirth_of_le_ge hge_next hle_next
  intro t ht
  have hev := heven t ht
  have hpow2 : 2 ≤ 2 ^ t := by
    have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
    omega
  have hge_odd : GirthAtLeast (DGraph (7 * 2 ^ t - 5) F) (7 * 2 ^ t) := by
    have hk : 1 ≤ 7 * (2 ^ (t - 1)) - 3 := by
      have : 2 * 2 ^ (t - 1) = 2 ^ t := by
        conv_rhs => rw [show t = (t - 1) + 1 by omega, pow_succ, mul_comm]
      omega
    have h2t : 2 * 2 ^ (t - 1) = 2 ^ t := by
      conv_rhs => rw [show t = (t - 1) + 1 by omega, pow_succ, mul_comm]
    have heq1 : 2 * (7 * 2 ^ (t - 1) - 3) + 1 = 7 * 2 ^ t - 5 := by omega
    have heq2 : 2 * (7 * 2 ^ (t - 1) - 3) + 6 = 7 * 2 ^ t := by omega
    have h := D_odd_girthAtLeast hk F
    rw [heq2, heq1] at h
    exact h
  have hle_odd : GirthAtMost (DGraph (7 * 2 ^ t - 5) F) (7 * 2 ^ t) :=
    girthAtMost_of_le (by omega) (by omega) hev.girthAtMost
  exact ⟨hasExactGirth_of_le_ge hge_odd hle_odd, hev⟩

/-- All-characteristic `{14 p^s - 5, 14 p^s - 4}` cascade via DS28 Theorem 55 (Sun 2017):
starting from our unconditional `D(9, q) = D(10, q) = 14`, for every `p ≥ 2` satisfying
`DS28Thm55Hyp F p` and every `s : ℕ`,
`girth D(14 * p^s - 5, F) = girth D(14 * p^s - 4, F) = 14 * p^s`. -/
theorem cascade_all_char_ps (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F)
    {p : ℕ} (hp : 2 ≤ p) (h55 : DS28Thm55Hyp F p) :
    ∀ s : ℕ,
      HasExactGirth (DGraph (14 * p ^ s - 5) F) (14 * p ^ s) ∧
      HasExactGirth (DGraph (14 * p ^ s - 4) F) (14 * p ^ s) := by
  intro s
  induction s with
  | zero =>
    simpa using D9_D10_exact_girth_14_all_q_ge_4 F hcard
  | succ s ih =>
    have hpow : 1 ≤ p ^ s := Nat.one_le_pow _ _ (by omega)
    let k := 14 * p ^ s - 4
    have hk3 : 3 ≤ k := by omega
    have hk_even : ¬ Odd k := by
      intro ⟨m, hm⟩; omega
    have hk_mod4 : k % 4 ≠ 3 := by omega
    have hconj : Conjecture46At k F := by
      simp only [Conjecture46At, hk_even, ite_false]
      have heq : k + 4 = 14 * p ^ s := by omega
      rw [heq]; exact ih.2
    have hlift := h55 k hk3 hconj
    dsimp only at hlift
    have hif : (if Odd k then k + 5 else k + 4) = k + 4 := by simp [hk_even]
    have hg : k + 4 = 14 * p ^ s := by omega
    have hpg : p * (k + 4) = 14 * p ^ (s + 1) := by
      rw [hg, pow_succ]; ring
    rw [hif, hpg] at hlift
    exact ⟨hlift.1, hlift.2 hk_mod4⟩

/-- Explicit characteristic-3 consequence (`p = 3`, e.g. `q = 9, 27, 81, ...`):
fills DS28 Table 9 cells `(37, 27), (38, 27) → 42` and Table 12 cells `(79, 27), (80, 27) → 84`. -/
theorem cascade_char3_cells_37_38_79_80 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F)
    (h55 : DS28Thm55Hyp F 3) (h2 : XCTThm2Part2Hyp F) (h3 : XCTThm2Part3Hyp F) :
    HasExactGirth (DGraph 37 F) 42 ∧
    HasExactGirth (DGraph 38 F) 42 ∧
    HasExactGirth (DGraph 79 F) 84 ∧
    HasExactGirth (DGraph 80 F) 84 := by
  have h1 := cascade_all_char_ps F hcard (p := 3) (by omega) h55 1
  have h37 : HasExactGirth (DGraph 37 F) 42 := by simpa using h1.1
  have h38 : HasExactGirth (DGraph 38 F) 42 := by simpa using h1.2
  have h79 : HasExactGirth (DGraph 79 F) 84 := by
    simpa using h2 21 (by omega) (by simpa using h38)
  have h80 : HasExactGirth (DGraph 80 F) 84 := by
    simpa using h3 10 (by omega) (by simpa using h38)
  exact ⟨h37, h38, h79, h80⟩

/-! ### Part 2: Pure-Kernel Linear-Time Walk Verifier for `D(k, ZMod 3)` -/

/-- Convert a list `v : List (ZMod 3)` of length `k` to a coordinate vector `Fin k → ZMod 3`. -/
def vecOfList {k : ℕ} (v : List (ZMod 3)) (hv : v.length = k) : Fin k → ZMod 3 :=
  fun j => v[j.val]'(hv ▸ j.isLt)

/-- Strict 3-way evaluator on `ZMod 3` forcing WHNF reduction to a literal `0`, `1`, or `2` at each
list step so pure-kernel `decide` runs in `O(1)` recursion depth even at `k = 48, L = 52`. -/
def strictZ3 {α : Type*} (z : ZMod 3) (f : ZMod 3 → α) : α :=
  if z == 0 then f 0 else if z == 1 then f 1 else f 2

lemma strictZ3_eq {α : Type*} (z : ZMod 3) (f : ZMod 3 → α) : strictZ3 z f = f z := by
  fin_cases z <;> rfl

/-- Linear-time tail step computing coordinates `j ≥ 3` of the line adjacent to `p` with first
coordinate `x`. -/
def stepLineAux (p0 x : ZMod 3) :
    ℕ → ZMod 3 → ZMod 3 → ZMod 3 → ZMod 3 → List (ZMod 3) → List (ZMod 3)
  | _, _, _, _, _, [] => []
  | j, pm2, pm1, lm2, lm1, pj :: rest =>
    strictZ3 (if (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1 then pm2 * x - pj else p0 * lm2 - pj)
      fun lj => lj :: stepLineAux p0 x (j + 1) pm1 pj lm1 lj rest

/-- Linear-time computable line step in `D(k, ZMod 3)`. -/
def stepLineList (p : List (ZMod 3)) (x : ZMod 3) : List (ZMod 3) :=
  match p with
  | [] => []
  | [_] => [x]
  | [p0, p1] => strictZ3 (p0 * x - p1) fun l1 => [x, l1]
  | p0 :: p1 :: p2 :: rest =>
    strictZ3 (p0 * x - p1) fun l1 =>
    strictZ3 (p0 * l1 - p2) fun l2 =>
    x :: l1 :: l2 :: stepLineAux p0 x 3 p1 p2 l1 l2 rest

/-- Linear-time tail step computing coordinates `j ≥ 3` of the point adjacent to `l` with first
coordinate `x`. -/
def stepPointAux (l0 x : ZMod 3) :
    ℕ → ZMod 3 → ZMod 3 → ZMod 3 → ZMod 3 → List (ZMod 3) → List (ZMod 3)
  | _, _, _, _, _, [] => []
  | j, lm2, lm1, pm2, pm1, lj :: rest =>
    strictZ3 (if (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1 then pm2 * l0 - lj else x * lm2 - lj)
      fun pj => pj :: stepPointAux l0 x (j + 1) lm1 lj pm1 pj rest

/-- Linear-time computable point step in `D(k, ZMod 3)`. -/
def stepPointList (l : List (ZMod 3)) (x : ZMod 3) : List (ZMod 3) :=
  match l with
  | [] => []
  | [_] => [x]
  | [l0, l1] => strictZ3 (x * l0 - l1) fun p1 => [x, p1]
  | l0 :: l1 :: l2 :: rest =>
    strictZ3 (x * l0 - l1) fun p1 =>
    strictZ3 (x * l1 - l2) fun p2 =>
    x :: p1 :: p2 :: stepPointAux l0 x 3 l1 l2 p1 p2 rest

lemma stepLineAux_length (p0 x : ZMod 3) :
    ∀ (j : ℕ) (pm2 pm1 lm2 lm1 : ZMod 3) (rest : List (ZMod 3)),
      (stepLineAux p0 x j pm2 pm1 lm2 lm1 rest).length = rest.length
  | _, _, _, _, _, [] => rfl
  | j, pm2, pm1, lm2, lm1, _ :: rest => by
    simp [stepLineAux, strictZ3_eq, stepLineAux_length p0 x (j + 1) pm1 _ lm1 _ rest]

lemma stepLineList_length (p : List (ZMod 3)) (x : ZMod 3) :
    (stepLineList p x).length = p.length := by
  match p with
  | [] => rfl
  | [_] => rfl
  | [_, _] => simp [stepLineList, strictZ3_eq]
  | p0 :: p1 :: p2 :: rest =>
    simp [stepLineList, strictZ3_eq, stepLineAux_length]

lemma stepPointAux_length (l0 x : ZMod 3) :
    ∀ (j : ℕ) (lm2 lm1 pm2 pm1 : ZMod 3) (rest : List (ZMod 3)),
      (stepPointAux l0 x j lm2 lm1 pm2 pm1 rest).length = rest.length
  | _, _, _, _, _, [] => rfl
  | j, lm2, lm1, pm2, pm1, _ :: rest => by
    simp [stepPointAux, strictZ3_eq, stepPointAux_length l0 x (j + 1) lm1 _ pm1 _ rest]

lemma stepPointList_length (l : List (ZMod 3)) (x : ZMod 3) :
    (stepPointList l x).length = l.length := by
  match l with
  | [] => rfl
  | [_] => rfl
  | [_, _] => simp [stepPointList, strictZ3_eq]
  | l0 :: l1 :: l2 :: rest =>
    simp [stepPointList, strictZ3_eq, stepPointAux_length]

lemma stepLineList_head (p : List (ZMod 3)) (x : ZMod 3) (hp : 0 < p.length) :
    (stepLineList p x)[0]'(by rw [stepLineList_length]; exact hp) = x := by
  match p with
  | [] => simp at hp
  | [_] => rfl
  | [_, _] => simp [stepLineList, strictZ3_eq]
  | _ :: _ :: _ :: _ => simp [stepLineList, strictZ3_eq]

lemma stepPointList_head (l : List (ZMod 3)) (x : ZMod 3) (hl : 0 < l.length) :
    (stepPointList l x)[0]'(by rw [stepPointList_length]; exact hl) = x := by
  match l with
  | [] => simp at hl
  | [_] => rfl
  | [_, _] => simp [stepPointList, strictZ3_eq]
  | _ :: _ :: _ :: _ => simp [stepPointList, strictZ3_eq]

/-- Invariant proving `stepLineAux` satisfies the `j ≥ 3` equations of `D(k, ZMod 3)`. -/
lemma stepLineAux_adj (p l : List (ZMod 3)) (p0 x : ZMod 3)
    (rest : List (ZMod 3)) :
    ∀ (j : ℕ) (hj3 : 3 ≤ j) (pm2 pm1 lm2 lm1 : ZMod 3)
      (hp : j + rest.length = p.length) (hl : j + rest.length = l.length),
      p.drop j = rest →
      l.drop j = stepLineAux p0 x j pm2 pm1 lm2 lm1 rest →
      p[j - 2]'(by omega) = pm2 →
      p[j - 1]'(by omega) = pm1 →
      l[j - 2]'(by omega) = lm2 →
      l[j - 1]'(by omega) = lm1 →
      ∀ (r : ℕ) (hr : r < rest.length),
        p[j + r]'(by omega) + l[j + r]'(by omega) =
          if (j + r + 1) % 4 = 0 ∨ (j + r + 1) % 4 = 1 then
            p[j + r - 2]'(by omega) * x
          else
            p0 * l[j + r - 2]'(by omega) := by
  induction rest with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ r hr; simp at hr
  | cons pj rest ih =>
    intro j hj3 pm2 pm1 lm2 lm1 hp hl hdp hdl hpm2 hpm1 hlm2 hlm1 r hr
    simp only [List.length_cons] at hp hl hr
    have hpj : p[j]'(by omega) = pj := by
      have h0 := congrArg (fun u => u[0]?) hdp
      simp [List.getElem?_drop, List.getElem?_eq_getElem (show j < p.length by omega)] at h0
      exact h0
    let lj := if (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1 then pm2 * x - pj else p0 * lm2 - pj
    have hlj : l[j]'(by omega) = lj := by
      have h0 := congrArg (fun u => u[0]?) hdl
      simp [stepLineAux, strictZ3_eq, List.getElem?_drop,
        List.getElem?_eq_getElem (show j < l.length by omega)] at h0
      exact h0
    cases r with
    | zero =>
      simp only [add_zero, hpj, hlj, lj]
      rw [hpm2, hlm2]
      split_ifs <;> ring
    | succ r =>
      have hdp' : p.drop (j + 1) = rest := by
        rw [← List.tail_drop, hdp]; rfl
      have hdl' : l.drop (j + 1) = stepLineAux p0 x (j + 1) pm1 pj lm1 lj rest := by
        rw [← List.tail_drop, hdl]
        simp [stepLineAux, strictZ3_eq, lj]
      have hstep := ih (j + 1) (by omega) pm1 pj lm1 lj (by omega) (by omega) hdp' hdl'
        (by simpa [show j + 1 - 2 = j - 1 by omega] using hpm1)
        (by simpa [Nat.add_sub_cancel] using hpj)
        (by simpa [show j + 1 - 2 = j - 1 by omega] using hlm1)
        (by simpa [Nat.add_sub_cancel] using hlj)
        r (by omega)
      have hidx : j + (r + 1) = j + 1 + r := by omega
      simpa only [hidx] using hstep

/-- `stepLineList p x` is adjacent to `p` in `D(p.length, ZMod 3)`. -/
lemma stepLineList_plAdj (p : List (ZMod 3)) (x : ZMod 3) :
    PLAdj p.length (ZMod 3) (vecOfList p rfl)
      (vecOfList (stepLineList p x) (stepLineList_length p x)) := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  match p with
  | [] => simp at hjlt
  | [_] => simp at hjlt; omega
  | [p0, p1] =>
    have hj_eq : j = 1 := by simp at hjlt; omega
    subst hj_eq
    simp only [vecOfList, stepLineList, strictZ3_eq, rhsD,
      List.length_cons, List.length_nil, Nat.zero_lt_succ, ↓reduceDIte,
      List.getElem_cons_zero, List.getElem_cons_succ]
    ring
  | p0 :: p1 :: p2 :: rest =>
    have h0 : 0 < (p0 :: p1 :: p2 :: rest).length := by simp
    match j with
    | 0 => omega
    | 1 =>
      simp only [vecOfList, stepLineList, strictZ3_eq, rhsD, h0, ↓reduceDIte,
        List.getElem_cons_zero, List.getElem_cons_succ]
      ring
    | 2 =>
      simp only [vecOfList, stepLineList, strictZ3_eq, rhsD, h0, ↓reduceDIte, OfNat.ofNat_ne_one,
        List.getElem_cons_zero, List.getElem_cons_succ]
      ring
    | j + 3 =>
      have hne1 : j + 3 ≠ 1 := by omega
      have hne2 : j + 3 ≠ 2 := by omega
      have hge3 : 3 ≤ j + 3 := by omega
      simp only [vecOfList, rhsD, h0, hne1, hne2, hge3, ↓reduceDIte]
      have haux := stepLineAux_adj (p0 :: p1 :: p2 :: rest)
        (stepLineList (p0 :: p1 :: p2 :: rest) x) p0 x rest 3 le_rfl
        p1 p2 (p0 * x - p1) (p0 * (p0 * x - p1) - p2)
        (by simp; omega)
        (by rw [stepLineList_length]; simp; omega)
        rfl
        (by simp [stepLineList, strictZ3_eq])
        rfl rfl
        (by simp [stepLineList, strictZ3_eq])
        (by simp [stepLineList, strictZ3_eq])
        j (by simp at hjlt; omega)
      have hcomm : 3 + j = j + 3 := by omega
      have hhead : (stepLineList (p0 :: p1 :: p2 :: rest) x)[0]'(by
          rw [stepLineList_length]; exact h0) = x := by
        simp [stepLineList, strictZ3_eq]
      simpa only [hcomm, hhead, List.getElem_cons_zero] using haux

/-- Invariant proving `stepPointAux` satisfies the `j ≥ 3` equations of `D(k, ZMod 3)`. -/
lemma stepPointAux_adj (p l : List (ZMod 3)) (l0 x : ZMod 3)
    (rest : List (ZMod 3)) :
    ∀ (j : ℕ) (hj3 : 3 ≤ j) (lm2 lm1 pm2 pm1 : ZMod 3)
      (hl : j + rest.length = l.length) (hp : j + rest.length = p.length),
      l.drop j = rest →
      p.drop j = stepPointAux l0 x j lm2 lm1 pm2 pm1 rest →
      l[j - 2]'(by omega) = lm2 →
      l[j - 1]'(by omega) = lm1 →
      p[j - 2]'(by omega) = pm2 →
      p[j - 1]'(by omega) = pm1 →
      ∀ (r : ℕ) (hr : r < rest.length),
        p[j + r]'(by omega) + l[j + r]'(by omega) =
          if (j + r + 1) % 4 = 0 ∨ (j + r + 1) % 4 = 1 then
            p[j + r - 2]'(by omega) * l0
          else
            x * l[j + r - 2]'(by omega) := by
  induction rest with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ r hr; simp at hr
  | cons lj rest ih =>
    intro j hj3 lm2 lm1 pm2 pm1 hl hp hdl hdp hlm2 hlm1 hpm2 hpm1 r hr
    simp only [List.length_cons] at hl hp hr
    have hlj : l[j]'(by omega) = lj := by
      have h0 := congrArg (fun u => u[0]?) hdl
      simp [List.getElem?_drop, List.getElem?_eq_getElem (show j < l.length by omega)] at h0
      exact h0
    let pj := if (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1 then pm2 * l0 - lj else x * lm2 - lj
    have hpj : p[j]'(by omega) = pj := by
      have h0 := congrArg (fun u => u[0]?) hdp
      simp [stepPointAux, strictZ3_eq, List.getElem?_drop,
        List.getElem?_eq_getElem (show j < p.length by omega)] at h0
      exact h0
    cases r with
    | zero =>
      simp only [add_zero, hpj, hlj, pj]
      rw [hpm2, hlm2]
      split_ifs <;> ring
    | succ r =>
      have hdl' : l.drop (j + 1) = rest := by
        rw [← List.tail_drop, hdl]; rfl
      have hdp' : p.drop (j + 1) = stepPointAux l0 x (j + 1) lm1 lj pm1 pj rest := by
        rw [← List.tail_drop, hdp]
        simp [stepPointAux, strictZ3_eq, pj]
      have hstep := ih (j + 1) (by omega) lm1 lj pm1 pj (by omega) (by omega) hdl' hdp'
        (by simpa [show j + 1 - 2 = j - 1 by omega] using hlm1)
        (by simpa [Nat.add_sub_cancel] using hlj)
        (by simpa [show j + 1 - 2 = j - 1 by omega] using hpm1)
        (by simpa [Nat.add_sub_cancel] using hpj)
        r (by omega)
      have hidx : j + (r + 1) = j + 1 + r := by omega
      simpa only [hidx] using hstep

/-- `stepPointList l x` is adjacent to `l` in `D(l.length, ZMod 3)`. -/
lemma stepPointList_plAdj (l : List (ZMod 3)) (x : ZMod 3) :
    PLAdj l.length (ZMod 3) (vecOfList (stepPointList l x) (stepPointList_length l x))
      (vecOfList l rfl) := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  match l with
  | [] => simp at hjlt
  | [_] => simp at hjlt; omega
  | [l0, l1] =>
    have hj_eq : j = 1 := by simp at hjlt; omega
    subst hj_eq
    simp only [vecOfList, stepPointList, strictZ3_eq, rhsD,
      List.length_cons, List.length_nil, Nat.zero_lt_succ, ↓reduceDIte,
      List.getElem_cons_zero, List.getElem_cons_succ]
    ring
  | l0 :: l1 :: l2 :: rest =>
    have h0 : 0 < (l0 :: l1 :: l2 :: rest).length := by simp
    match j with
    | 0 => omega
    | 1 =>
      simp only [vecOfList, stepPointList, strictZ3_eq, rhsD, h0, ↓reduceDIte,
        List.getElem_cons_zero, List.getElem_cons_succ]
      ring
    | 2 =>
      simp only [vecOfList, stepPointList, strictZ3_eq, rhsD, h0, ↓reduceDIte, OfNat.ofNat_ne_one,
        List.getElem_cons_zero, List.getElem_cons_succ]
      ring
    | j + 3 =>
      have hne1 : j + 3 ≠ 1 := by omega
      have hne2 : j + 3 ≠ 2 := by omega
      have hge3 : 3 ≤ j + 3 := by omega
      simp only [vecOfList, rhsD, h0, hne1, hne2, hge3, ↓reduceDIte]
      have haux := stepPointAux_adj (stepPointList (l0 :: l1 :: l2 :: rest) x)
        (l0 :: l1 :: l2 :: rest) l0 x rest 3 le_rfl
        l1 l2 (x * l0 - l1) (x * l1 - l2)
        (by simp; omega)
        (by rw [stepPointList_length]; simp; omega)
        rfl
        (by simp [stepPointList, strictZ3_eq])
        rfl rfl
        (by simp [stepPointList, strictZ3_eq])
        (by simp [stepPointList, strictZ3_eq])
        j (by simp at hjlt; omega)
      have hcomm : 3 + j = j + 3 := by omega
      have hhead : (stepPointList (l0 :: l1 :: l2 :: rest) x)[0]'(by
          rw [stepPointList_length]; exact h0) = x := by
        simp [stepPointList, strictZ3_eq]
      simpa only [hcomm, hhead, List.getElem_cons_zero] using haux

/-- Fast tail-recursive walk endpoint evaluator in `D(k, ZMod 3)`. -/
def walkEndAux : Bool → List (ZMod 3) → List (ZMod 3) → List (ZMod 3)
  | _, cur, [] => cur
  | true, cur, x :: rest => walkEndAux false (stepLineList cur x) rest
  | false, cur, x :: rest => walkEndAux true (stepPointList cur x) rest

/-- Check whether every coordinate of a list vector is `0`. -/
def isAllZero (v : List (ZMod 3)) : Bool := v.all (· == 0)

/-- Check cyclic non-backtracking on a first-coordinate list `xs`. -/
def checkNB (xs : List (ZMod 3)) : Bool :=
  let L := xs.length
  (List.range L).all fun i =>
    xs.getD i 0 != xs.getD ((i + 2) % L) 0

/-- Pure-kernel computable certificate verifier for a closed non-backtracking walk starting from
`(0)` in `D(k, ZMod 3)` with vertex first coordinates `xs` (so `xs[0] = 0`, `xs.length` even `≥ 4`). -/
def checkWalkD3 (k : ℕ) (xs : List (ZMod 3)) : Bool :=
  decide (1 ≤ k) && decide (3 ≤ xs.length) && decide (xs.length % 2 = 0) &&
  (xs.getD 0 1 == 0) &&
  checkNB xs &&
  isAllZero (walkEndAux true (List.replicate k 0) (xs.drop 1 ++ [0]))

/-- Indexed state sequence of the walk from `List.replicate k 0` along step list `steps`. -/
def walkState (k : ℕ) (steps : List (ZMod 3)) : ℕ → List (ZMod 3)
  | 0 => List.replicate k 0
  | t + 1 =>
    if Even t then
      stepLineList (walkState k steps t) (steps.getD t 0)
    else
      stepPointList (walkState k steps t) (steps.getD t 0)

lemma walkState_length (k : ℕ) (steps : List (ZMod 3)) (t : ℕ) :
    (walkState k steps t).length = k := by
  induction t with
  | zero => simp [walkState]
  | succ t ih =>
    simp only [walkState]
    split_ifs
    · rw [stepLineList_length, ih]
    · rw [stepPointList_length, ih]

lemma walkEndAux_eq_walkState_shift (k : ℕ) (steps : List (ZMod 3)) :
    ∀ (rest : List (ZMod 3)) (t : ℕ),
      steps.drop t = rest →
      walkEndAux (decide (Even t)) (walkState k steps t) rest =
        walkState k steps (t + rest.length) := by
  intro rest
  induction rest with
  | nil => intro t _; simp [walkEndAux]
  | cons x rest ih =>
    intro t hdrop
    have hx : steps.getD t 0 = x := by
      have h0 := congrArg (fun u => u[0]?) hdrop
      have hlt : t < steps.length := by
        have := congrArg List.length hdrop; simp at this; omega
      simp [List.getElem?_drop, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt] at h0 ⊢
      exact h0
    have hdrop' : steps.drop (t + 1) = rest := by
      rw [← List.tail_drop, hdrop]; rfl
    by_cases he : Even t
    · have hno : ¬ Even (t + 1) := by rcases he with ⟨m, rfl⟩; intro ⟨m', hm'⟩; omega
      simp only [he, decide_true, walkEndAux]
      have hst : stepLineList (walkState k steps t) x = walkState k steps (t + 1) := by
        simp only [walkState, he, ite_true, hx]
      rw [hst]
      have hrec := ih (t + 1) hdrop'
      simp only [hno, decide_false] at hrec
      rw [hrec]
      congr 1; simp; omega
    · have he' : Even (t + 1) := by
        rcases Nat.not_even_iff_odd.1 he with ⟨m, rfl⟩; exact ⟨m + 1, by omega⟩
      simp only [he, decide_false, walkEndAux]
      have hst : stepPointList (walkState k steps t) x = walkState k steps (t + 1) := by
        simp only [walkState, he, ite_false, hx]
      rw [hst]
      have hrec := ih (t + 1) hdrop'
      simp only [he', decide_true] at hrec
      rw [hrec]
      congr 1; simp; omega

lemma eq_replicate_zero_of_isAllZero {v : List (ZMod 3)} {k : ℕ}
    (hlen : v.length = k) (hz : isAllZero v = true) : v = List.replicate k 0 := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi1 hi2
  simp only [List.getElem_replicate]
  simp only [isAllZero, List.all_eq_true, beq_iff_eq] at hz
  exact hz v[i] (List.getElem_mem hi1)

lemma plAdj_vecOfList_cast {k : ℕ} {p l : List (ZMod 3)} (hp : p.length = k) (hl : l.length = k)
    (h : PLAdj p.length (ZMod 3) (vecOfList p rfl) (vecOfList l (hl.trans hp.symm))) :
    PLAdj k (ZMod 3) (vecOfList p hp) (vecOfList l hl) := by
  subst hp
  exact h

lemma plAdj_vecOfList_cast_symm {k : ℕ} {p l : List (ZMod 3)} (hp : p.length = k) (hl : l.length = k)
    (h : PLAdj l.length (ZMod 3) (vecOfList p (hp.trans hl.symm)) (vecOfList l rfl)) :
    PLAdj k (ZMod 3) (vecOfList p hp) (vecOfList l hl) := by
  subst hl
  exact h

/-- Soundness of the pure-kernel `D(k, ZMod 3)` walk checker:
`checkWalkD3 k xs = true` proves `ClosedNBWalk (DGraph k (ZMod 3)) xs.length`. -/
theorem checkWalkD3_sound (k : ℕ) (xs : List (ZMod 3))
    (h : checkWalkD3 k xs = true) : ClosedNBWalk (DGraph k (ZMod 3)) xs.length := by
  simp only [checkWalkD3, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hk1, hL3⟩, hLeven⟩, hxs0⟩, hnb⟩, hallz⟩
  let L := xs.length
  let steps := xs.drop 1 ++ [0]
  have hsteps_len : steps.length = L := by simp [steps, L]; omega
  have hend_eq : walkEndAux true (List.replicate k 0) steps = walkState k steps L := by
    have h0 := walkEndAux_eq_walkState_shift k steps steps 0 (by simp)
    simp only [Even.zero, decide_true, zero_add, hsteps_len] at h0
    exact h0
  rw [hend_eq] at hallz
  have hclose : walkState k steps L = List.replicate k 0 :=
    eq_replicate_zero_of_isAllZero (walkState_length k steps L) hallz
  -- Construct the cyclic vertex sequence in `DGraph k (ZMod 3)`
  let v : Fin L → Vertex k (ZMod 3) := fun i =>
    if Even i.val then
      Sum.inl (vecOfList (walkState k steps i.val) (walkState_length k steps i.val))
    else
      Sum.inr (vecOfList (walkState k steps i.val) (walkState_length k steps i.val))
  have hv_fc : ∀ i : Fin L, firstCoord (by omega : 0 < k) (v i) = xs.getD i.val 0 := by
    intro ⟨i, hilt⟩
    cases i with
    | zero =>
      simp only [v, Even.zero, ite_true, firstCoord, vecOfList, walkState, List.getElem_replicate]
      have hlt0 : 0 < xs.length := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt0, Option.getD_some] at hxs0 ⊢
      exact hxs0.symm
    | succ t =>
      have hstep_val : steps.getD t 0 = xs.getD (t + 1) 0 := by
        have ht1 : t < (xs.drop 1).length := by simp; omega
        have ht2 : t < steps.length := by rw [hsteps_len]; omega
        have hlt_xs : t + 1 < xs.length := hilt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht2,
          List.getElem?_eq_getElem hlt_xs, Option.getD_some]
        simp only [steps, List.getElem_append_left ht1, List.getElem_drop]
        congr 1; omega
      by_cases het : Even t
      · have hno : ¬ Even (t + 1) := by rcases het with ⟨m, rfl⟩; intro ⟨m', hm'⟩; omega
        simp only [v, hno, ite_false, firstCoord, vecOfList, walkState, het, ite_true]
        rw [stepLineList_head _ _ (by rw [walkState_length]; omega)]
        exact hstep_val
      · have he' : Even (t + 1) := by
          rcases Nat.not_even_iff_odd.1 het with ⟨m, rfl⟩; exact ⟨m + 1, by omega⟩
        simp only [v, he', ite_true, firstCoord, vecOfList, walkState, het, ite_false]
        rw [stepPointList_head _ _ (by rw [walkState_length]; omega)]
        exact hstep_val
  refine ⟨hL3, v, ?_, ?_⟩
  · -- Cyclic adjacency along all `L` edges
    intro ⟨i, hilt⟩
    by_cases hlast : i + 1 < L
    · have hmod : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt hlast
      by_cases hei : Even i
      · have hno : ¬ Even (i + 1) := by rcases hei with ⟨m, rfl⟩; intro ⟨m', hm'⟩; omega
        dsimp only [DGraph, AdjD, v]
        simp only [hmod, hei, hno, ite_true, ite_false]
        have hws : walkState k steps (i + 1) = stepLineList (walkState k steps i) (steps.getD i 0) := by
          simp only [walkState, hei, ite_true]
        have hvec : vecOfList (walkState k steps ((i + 1) % xs.length))
              (walkState_length k steps ((i + 1) % xs.length)) =
            vecOfList (stepLineList (walkState k steps i) (steps.getD i 0))
              (by rw [stepLineList_length, walkState_length]) := by
          funext j; simp only [vecOfList, hmod, hws]
        rw [hvec]
        exact plAdj_vecOfList_cast (walkState_length k steps i) _
          (stepLineList_plAdj (walkState k steps i) (steps.getD i 0))
      · have he' : Even (i + 1) := by
          rcases Nat.not_even_iff_odd.1 hei with ⟨m, rfl⟩; exact ⟨m + 1, by omega⟩
        dsimp only [DGraph, AdjD, v]
        simp only [hmod, hei, he', ite_true, ite_false]
        have hws : walkState k steps (i + 1) = stepPointList (walkState k steps i) (steps.getD i 0) := by
          simp only [walkState, hei, ite_false]
        have hvec : vecOfList (walkState k steps ((i + 1) % xs.length))
              (walkState_length k steps ((i + 1) % xs.length)) =
            vecOfList (stepPointList (walkState k steps i) (steps.getD i 0))
              (by rw [stepPointList_length, walkState_length]) := by
          funext j; simp only [vecOfList, hmod, hws]
        rw [hvec]
        exact plAdj_vecOfList_cast_symm _ (walkState_length k steps i)
          (stepPointList_plAdj (walkState k steps i) (steps.getD i 0))
    · -- Closing edge `i = L - 1` (odd, since `L` is even) back to `0`
      have hi_eq : i + 1 = L := by omega
      have hmod : (i + 1) % xs.length = 0 := by
        have : i + 1 = xs.length := hi_eq
        rw [this, Nat.mod_self]
      have hnoi : ¬ Even i := by intro ⟨m, hm⟩; omega
      dsimp only [DGraph, AdjD, v]
      simp only [hmod, hnoi, Even.zero, ite_true, ite_false]
      have hstep_eq : walkState k steps 0 = stepPointList (walkState k steps i) (steps.getD i 0) := by
        have h1 : walkState k steps (i + 1) = stepPointList (walkState k steps i) (steps.getD i 0) := by
          simp only [walkState, hnoi, ite_false]
        rw [show walkState k steps 0 = List.replicate k 0 from rfl, ← hclose, ← hi_eq, h1]
      have hvec : vecOfList (walkState k steps ((i + 1) % xs.length))
            (walkState_length k steps ((i + 1) % xs.length)) =
          vecOfList (stepPointList (walkState k steps i) (steps.getD i 0))
            (by rw [stepPointList_length, walkState_length]) := by
        funext j; simp only [vecOfList, hmod, hstep_eq]
      rw [hvec]
      exact plAdj_vecOfList_cast_symm _ (walkState_length k steps i)
        (stepPointList_plAdj (walkState k steps i) (steps.getD i 0))
  · -- Non-backtracking from `checkNB`
    intro i heq
    have hfc := congrArg (firstCoord (by omega : 0 < k)) heq
    rw [hv_fc i, hv_fc ⟨(i.val + 2) % L, Nat.mod_lt _ (by omega)⟩] at hfc
    simp only [checkNB, List.all_eq_true, List.mem_range, bne_iff_ne] at hnb
    exact hnb i.val i.isLt hfc

/-- Pure-kernel upper-bound theorem from `checkWalkD3`: `GirthAtMost (DGraph k (ZMod 3)) xs.length`. -/
theorem girthAtMost_D3_of_checkWalkD3 (k : ℕ) (xs : List (ZMod 3))
    (h : checkWalkD3 k xs = true) : GirthAtMost (DGraph k (ZMod 3)) xs.length :=
  exists_cycle_le_of_closed_nb_walk (checkWalkD3_sound k xs h)

/-! ### Part 3: Kernel-Verified `D(k, 3)` Witnesses & Unconditional Exact Girths -/

/-- Exact witness for `D(2, 3)` (length 6). -/
def wit_D3_k2 : List (ZMod 3) := [0, 1, 1, 2, 2, 0]

/-- Exact witness for `D(3, 3)` (length 8). -/
def wit_D3_k3 : List (ZMod 3) := [0, 1, 1, 0, 0, 2, 1, 0]

/-- Exact witness for `D(8, 3)` (length 12; covers `k = 4..8`). -/
def wit_D3_k8 : List (ZMod 3) := [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0]

/-- Exact witness for `D(14, 3)` (length 18; covers `k = 9..14`). -/
def wit_D3_k14 : List (ZMod 3) :=
  [0, 1, 1, 2, 2, 0, 0, 1, 1, 2, 2, 0, 0, 1, 1, 2, 2, 0]

/-- Exact witness for `D(16, 3)` (length 20; refutes Mukherjee's 22). -/
def wit_D3_k16 : List (ZMod 3) :=
  [0, 1, 2, 2, 0, 1, 1, 0, 0, 1, 1, 2, 2, 1, 1, 2, 0, 0, 1, 2]

/-- Exact witness for `D(19, 3)` (length 24; covers `k = 17..19`). -/
def wit_D3_k19 : List (ZMod 3) :=
  [0, 1, 1, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 2, 1, 0]

/-- Exact witness for `D(24, 3)` (length 28; covers `k = 20..24`). -/
def wit_D3_k24 : List (ZMod 3) :=
  [0, 1, 1, 0, 0, 1, 1, 0, 2, 2, 0, 1, 2, 0, 1, 2, 0, 0, 1, 2, 0, 0, 2, 1, 1, 2, 2, 0]

/-- New `R19-4-2` witness for `D(30, 3)` (length 36; upper bound for `k = 27..30`). -/
def wit_D3_k30 : List (ZMod 3) :=
  [0, 1, 2, 2, 0, 1, 2, 2, 0, 0, 1, 2, 2, 0, 1, 2, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 2, 2, 1, 0,
   0, 2, 1, 0, 2, 2]

/-- New `R19-4-2` witness for `D(34, 3)` (length 40; upper bound for `k = 33..34`). -/
def wit_D3_k34 : List (ZMod 3) :=
  [0, 0, 2, 1, 0, 0, 2, 1, 0, 2, 2, 1, 0, 0, 2, 2, 0, 1, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 1,
   2, 2, 0, 0, 2, 1, 0, 2, 2, 1]

/-- New `R19-4-2` witness for `D(39, 3)` (length 48; upper bound for `k = 36..39`). -/
def wit_D3_k39 : List (ZMod 3) :=
  [0, 0, 2, 1, 0, 0, 2, 2, 0, 0, 2, 1, 0, 2, 2, 1, 0, 0, 2, 1, 0, 0, 2, 2, 0, 0, 2, 1, 0, 2,
   2, 1, 0, 0, 2, 1, 0, 0, 2, 2, 0, 0, 2, 1, 0, 2, 2, 1]

/-- New `R19-4-2` witness for `D(42, 3)` (length 50; upper bound for `k = 40..42`). -/
def wit_D3_k42 : List (ZMod 3) :=
  [0, 0, 2, 2, 1, 0, 2, 1, 0, 2, 2, 0, 1, 2, 2, 0, 1, 1, 0, 2, 1, 1, 0, 2, 1, 0, 0, 1, 1, 2,
   0, 1, 2, 0, 1, 1, 0, 2, 1, 1, 0, 2, 2, 0, 1, 2, 2, 0, 1, 2]

/-- New `R19-4-2` witness for `D(48, 3)` (length 52; yields exact girth 52 at `k = 47, 48`
unconditionally, plus upper bound 52 for `k = 43..48`). -/
def wit_D3_k48 : List (ZMod 3) :=
  [0, 0, 2, 1, 0, 2, 2, 1, 1, 2, 2, 1, 0, 2, 1, 1, 0, 2, 2, 1, 0, 0, 2, 1, 0, 2, 2, 0, 0, 2,
   2, 1, 0, 2, 1, 1, 0, 2, 2, 1, 1, 2, 2, 1, 0, 2, 2, 0, 0, 2, 2, 1]

theorem D3_k2_exact_6 : HasExactGirth (DGraph 2 (ZMod 3)) 6 :=
  hasExactGirth_of_le_ge (D_two_girthAtLeast (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 2 wit_D3_k2 (by decide))

theorem D3_k3_exact_8 : HasExactGirth (DGraph 3 (ZMod 3)) 8 :=
  hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 1) (by omega) (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 3 wit_D3_k3 (by decide))

theorem D3_k8_upper_12 : GirthAtMost (DGraph 8 (ZMod 3)) 12 :=
  girthAtMost_D3_of_checkWalkD3 8 wit_D3_k8 (by decide)

theorem D3_k7_k8_exact_12 :
    HasExactGirth (DGraph 7 (ZMod 3)) 12 ∧ HasExactGirth (DGraph 8 (ZMod 3)) 12 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 3) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k8_upper_12),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 4) (by omega) (ZMod 3)) D3_k8_upper_12⟩

theorem D3_k14_upper_18 : GirthAtMost (DGraph 14 (ZMod 3)) 18 :=
  girthAtMost_D3_of_checkWalkD3 14 wit_D3_k14 (by decide)

theorem D3_k13_k14_exact_18 :
    HasExactGirth (DGraph 13 (ZMod 3)) 18 ∧ HasExactGirth (DGraph 14 (ZMod 3)) 18 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 6) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k14_upper_18),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 7) (by omega) (ZMod 3)) D3_k14_upper_18⟩

theorem D3_k16_upper_20 : GirthAtMost (DGraph 16 (ZMod 3)) 20 :=
  girthAtMost_D3_of_checkWalkD3 16 wit_D3_k16 (by decide)

/-- Unconditional exact girth `D(15, 3) = D(16, 3) = 20` (directly refuting Mukherjee's `dgraphs`
table entry `22`). -/
theorem D3_k15_k16_exact_20 :
    HasExactGirth (DGraph 15 (ZMod 3)) 20 ∧ HasExactGirth (DGraph 16 (ZMod 3)) 20 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 7) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k16_upper_20),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 8) (by omega) (ZMod 3)) D3_k16_upper_20⟩

theorem D3_k19_exact_24 : HasExactGirth (DGraph 19 (ZMod 3)) 24 :=
  hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 9) (by omega) (ZMod 3))
    (girthAtMost_D3_of_checkWalkD3 19 wit_D3_k19 (by decide))

theorem D3_k24_upper_28 : GirthAtMost (DGraph 24 (ZMod 3)) 28 :=
  girthAtMost_D3_of_checkWalkD3 24 wit_D3_k24 (by decide)

theorem D3_k23_k24_exact_28 :
    HasExactGirth (DGraph 23 (ZMod 3)) 28 ∧ HasExactGirth (DGraph 24 (ZMod 3)) 28 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 11) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k24_upper_28),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 12) (by omega) (ZMod 3)) D3_k24_upper_28⟩

theorem D3_k30_upper_36 : GirthAtMost (DGraph 30 (ZMod 3)) 36 :=
  girthAtMost_D3_of_checkWalkD3 30 wit_D3_k30 (by decide)

theorem D3_k34_upper_40 : GirthAtMost (DGraph 34 (ZMod 3)) 40 :=
  girthAtMost_D3_of_checkWalkD3 34 wit_D3_k34 (by decide)

theorem D3_k39_upper_48 : GirthAtMost (DGraph 39 (ZMod 3)) 48 :=
  girthAtMost_D3_of_checkWalkD3 39 wit_D3_k39 (by decide)

theorem D3_k42_upper_50 : GirthAtMost (DGraph 42 (ZMod 3)) 50 :=
  girthAtMost_D3_of_checkWalkD3 42 wit_D3_k42 (by decide)

theorem D3_k48_upper_52 : GirthAtMost (DGraph 48 (ZMod 3)) 52 :=
  girthAtMost_D3_of_checkWalkD3 48 wit_D3_k48 (by decide)

/-- **Unconditional exact girth for two new `R19-4-2` Table 4 entries (`k = 47, 48`)**:
`girth D(47, 3) = girth D(48, 3) = 52`, proved 100% in Lean 4's kernel (no external BFS needed,
since the Lazebnik–Ustimenko lower bound `47 + 5 = 48 + 4 = 52` is tight!). -/
theorem D3_k47_k48_exact_52 :
    HasExactGirth (DGraph 47 (ZMod 3)) 52 ∧ HasExactGirth (DGraph 48 (ZMod 3)) 52 :=
  ⟨hasExactGirth_of_le_ge (D_odd_girthAtLeast (k := 23) (by omega) (ZMod 3))
      (girthAtMost_mono_k (by omega) D3_k48_upper_52),
   hasExactGirth_of_le_ge (D_even_girthAtLeast (k := 24) (by omega) (ZMod 3)) D3_k48_upper_52⟩

/-- Explicit external-BFS lower-bound boundary for the 5 newly determined `R19-4-2` intervals
of `D(k, 3)` (`k = 27..30, 33..34, 36..39, 40..42, 43..48`, verified externally by 3 independent C
solvers `girth1`, `girth2`, `fgirth`, `rvgirth` in `R19-4`). -/
structure R19_4_2_BFSLowerBounds : Prop where
  k27_ge_36 : GirthAtLeast (DGraph 27 (ZMod 3)) 36
  k33_ge_40 : GirthAtLeast (DGraph 33 (ZMod 3)) 40
  k36_ge_48 : GirthAtLeast (DGraph 36 (ZMod 3)) 48
  k40_ge_50 : GirthAtLeast (DGraph 40 (ZMod 3)) 50
  k43_ge_52 : GirthAtLeast (DGraph 43 (ZMod 3)) 52

/-- **`R19-4-2` Complete New Table-4 Theorem (23 entries)**:
combining our 5 pure-kernel upper-bound witnesses (`D3_k30_upper_36`, `D3_k34_upper_40`,
`D3_k39_upper_48`, `D3_k42_upper_50`, `D3_k48_upper_52`) and kernel-proved monotonicity with the
5 explicit external exhaustive-BFS lower bounds yields exact girths for all 23 new `R19-4-2`
entries (`k = 27..30, 33..34, 36..48`). -/
theorem R19_4_2_exact_table_from_bfs (hbfs : R19_4_2_BFSLowerBounds) :
    (∀ k, 27 ≤ k → k ≤ 30 → HasExactGirth (DGraph k (ZMod 3)) 36) ∧
    (∀ k, 33 ≤ k → k ≤ 34 → HasExactGirth (DGraph k (ZMod 3)) 40) ∧
    (∀ k, 36 ≤ k → k ≤ 39 → HasExactGirth (DGraph k (ZMod 3)) 48) ∧
    (∀ k, 40 ≤ k → k ≤ 42 → HasExactGirth (DGraph k (ZMod 3)) 50) ∧
    (∀ k, 43 ≤ k → k ≤ 48 → HasExactGirth (DGraph k (ZMod 3)) 52) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hlo hhi
    exact hasExactGirth_of_le_ge
      (girthAtLeast_of_le (by omega) hlo hbfs.k27_ge_36)
      (girthAtMost_of_le (by omega) hhi D3_k30_upper_36)
  · intro k hlo hhi
    exact hasExactGirth_of_le_ge
      (girthAtLeast_of_le (by omega) hlo hbfs.k33_ge_40)
      (girthAtMost_of_le (by omega) hhi D3_k34_upper_40)
  · intro k hlo hhi
    exact hasExactGirth_of_le_ge
      (girthAtLeast_of_le (by omega) hlo hbfs.k36_ge_48)
      (girthAtMost_of_le (by omega) hhi D3_k39_upper_48)
  · intro k hlo hhi
    exact hasExactGirth_of_le_ge
      (girthAtLeast_of_le (by omega) hlo hbfs.k40_ge_50)
      (girthAtMost_of_le (by omega) hhi D3_k42_upper_50)
  · intro k hlo hhi
    exact hasExactGirth_of_le_ge
      (girthAtLeast_of_le (by omega) hlo hbfs.k43_ge_52)
      (girthAtMost_of_le (by omega) hhi D3_k48_upper_52)

end LazebnikUstimenko
