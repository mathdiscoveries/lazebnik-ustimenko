module

public import LazebnikUstimenko.LowerBound
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Unconditional 1-Parameter 14-Cycle in `D(9, F)` and `D(10, F)` (DS28 Conjecture 46)

For any field `F` and any admissible parameter `c : F` (`c ≠ 0`, `c ≠ 1`, `c + 1 ≠ 0`,
`c ^ 2 + 2 * c - 1 ≠ 0`), put
`a = (1 - c) / (1 + c)`, `b = (c - 1) / (c ^ 2 + 2 * c - 1)`, `d = 2 * c / (c ^ 2 + 2 * c - 1)`.

This file constructs the explicit 14-vertex closed non-backtracking walk in `D(10, F)` with
first coordinates `[0, 0, 1, a, b, c, d, a, b, c, 0, 0, 1, 1]` (starting at the zero point `(0)`),
proves all 14 adjacency equations and all 14 non-backtracking inequalities unconditionally in
**every** characteristic (including characteristic 2 and characteristic 3), verifies that the
analogous walk in `D(11, F)` fails to close with exact residue `c * (c - 1) / (c ^ 2 + 2 * c - 1)`,
proves that an admissible `c` exists in every finite field of cardinality `≥ 4` and in every
infinite field, and combines this with the unconditional Lazebnik–Ustimenko lower bound
(`LowerBound.lean`) to prove **100% unconditionally**:
`HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14`.
-/

@[expose] public section

namespace LazebnikUstimenko

/-- Admissibility condition on the free parameter `c : F` for the 14-cycle family. -/
def Admissible {F : Type*} [Field F] (c : F) : Prop :=
  c ≠ 0 ∧ c ≠ 1 ∧ c + 1 ≠ 0 ∧ c ^ 2 + 2 * c - 1 ≠ 0

lemma Admissible.sub_one_ne_zero {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    c - 1 ≠ 0 := sub_ne_zero.2 hc.2.1

lemma Admissible.one_sub_ne_zero {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    1 - c ≠ 0 := sub_ne_zero.2 hc.2.1.symm

lemma Admissible.one_add_ne_zero {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    1 + c ≠ 0 := by rw [add_comm]; exact hc.2.2.1

/-! ### Explicit 14 Vertices of the 1-Parameter Walk in `D(10, F)` -/

/-- Vertex `v₀` (Point): `(0, ..., 0)`. -/
def w14_0 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Vertex `v₁` (Line): `[0, ..., 0]`. -/
def w14_1 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Vertex `v₂` (Point): `(1, 0, ..., 0)`. -/
def w14_2 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Vertex `v₃` (Line): first coordinate `a = (1 - c) / (c + 1)`. -/
def w14_3 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  let q1 := c + 1
  ![(1 - c) / q1, (1 - c) / q1, (1 - c) / q1, 0, 0, 0, 0, 0, 0, 0]

/-- Vertex `v₄` (Point): first coordinate `b = (c - 1) / (c ^ 2 + 2 * c - 1)`. -/
def w14_4 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  let q1 := c + 1
  let q2 := c ^ 2 + 2 * c - 1
  ![(c - 1) / q2, c * (c - 1) / q2, c * (c - 1) / q2,
    -c * (c - 1) ^ 2 / (q1 * q2), -c * (c - 1) ^ 2 / (q1 * q2), 0, 0, 0, 0, 0]

/-- Vertex `v₅` (Line): first coordinate `c`. -/
def w14_5 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  let q1 := c + 1
  let q2 := c ^ 2 + 2 * c - 1
  ![c, 0, -c * (c - 1) / q2, c * (c - 1) / q1, c * (c - 1) / q1,
    c * (c - 1) ^ 2 / (q1 * q2), c * (c - 1) ^ 2 / (q1 * q2), 0, 0, 0]

/-- Vertex `v₆` (Point): first coordinate `d = 2 * c / (c ^ 2 + 2 * c - 1)`. -/
def w14_6 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  let q1 := c + 1
  let q2 := c ^ 2 + 2 * c - 1
  ![2 * c / q2, 2 * c ^ 2 / q2, c * (c - 1) / q2,
    c * (c ^ 3 + c ^ 2 + 3 * c - 1) / (q1 * q2), -c * (c - 1) ^ 2 / (q1 * q2),
    c * (c - 1) / q2, c * (c - 1) / q2, c ^ 2 * (c - 1) / q2, c ^ 2 * (c - 1) / q2, 0]

/-- Vertex `v₇` (Line): first coordinate `a = (1 - c) / (c + 1)`. -/
def w14_7 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  let q1 := c + 1
  let q2 := c ^ 2 + 2 * c - 1
  ![(1 - c) / q1, -2 * c / q1, -c * (c ^ 2 + 4 * c - 1) / (q1 * q2),
    -c, 0, -c * (3 * c - 1) / q2, -c * (c - 1) / q2,
    -c * (c - 1) / q1, -c * (c - 1) / q1, -2 * c ^ 2 * (c - 1) / (q1 * q2)]

/-- Vertex `v₈` (Point): first coordinate `b = (c - 1) / (c ^ 2 + 2 * c - 1)`. -/
def w14_8 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  let q2 := c ^ 2 + 2 * c - 1
  ![(c - 1) / q2, (c + 1) * (2 * c - 1) / q2, c * (c + 1) / q2,
    (c ^ 3 + 2 * c - 1) / q2, -c * (c - 1) / q2, 2 * c ^ 2 / q2,
    c * (c - 1) / q2, c * (c - 1) ^ 2 / q2, c ^ 2 * (c - 1) / q2, c * (c - 1) / q2]

/-- Vertex `v₉` (Line): first coordinate `c`. -/
def w14_9 {F : Type*} [Field F] (c : F) : Fin 10 → F :=
  ![c, -1, -1, c - 1, c, -1, 0, c, 0, 0]

/-- Vertex `v₁₀` (Point): first coordinate `0`. -/
def w14_10 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0]

/-- Vertex `v₁₁` (Line): first coordinate `0`. -/
def w14_11 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![0, -1, -1, -1, 0, -1, 0, 0, 0, 0]

/-- Vertex `v₁₂` (Point): first coordinate `1`. -/
def w14_12 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0]

/-- Vertex `v₁₃` (Line): first coordinate `1`. -/
def w14_13 {F : Type*} [Field F] (_c : F) : Fin 10 → F :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The 14-vertex closed walk in `D(10, F)` parameterized by `c : F`. -/
def walk14 {F : Type*} [Field F] (c : F) : Fin 14 → Vertex 10 F
  | ⟨0, _⟩ => Sum.inl (w14_0 c)
  | ⟨1, _⟩ => Sum.inr (w14_1 c)
  | ⟨2, _⟩ => Sum.inl (w14_2 c)
  | ⟨3, _⟩ => Sum.inr (w14_3 c)
  | ⟨4, _⟩ => Sum.inl (w14_4 c)
  | ⟨5, _⟩ => Sum.inr (w14_5 c)
  | ⟨6, _⟩ => Sum.inl (w14_6 c)
  | ⟨7, _⟩ => Sum.inr (w14_7 c)
  | ⟨8, _⟩ => Sum.inl (w14_8 c)
  | ⟨9, _⟩ => Sum.inr (w14_9 c)
  | ⟨10, _⟩ => Sum.inl (w14_10 c)
  | ⟨11, _⟩ => Sum.inr (w14_11 c)
  | ⟨12, _⟩ => Sum.inl (w14_12 c)
  | ⟨13, _⟩ => Sum.inr (w14_13 c)

/-! ### Algebraic Verification of All 14 Edges in `D(10, F)` -/

lemma walk14_edge_0_1 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_0 c) (w14_1 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_0, w14_1, rhsD]

lemma walk14_edge_2_1 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_2 c) (w14_1 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_2, w14_1, rhsD]

lemma walk14_edge_2_3 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_2 c) (w14_3 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_2, w14_3, rhsD]

lemma walk14_edge_4_3 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    PLAdj 10 F (w14_4 c) (w14_3 c) := by
  have h1 : c + 1 ≠ 0 := hc.2.2.1
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [w14_4, w14_3, rhsD]
  all_goals simp only [div_eq_mul_inv, mul_inv]; grind

lemma walk14_edge_4_5 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    PLAdj 10 F (w14_4 c) (w14_5 c) := by
  have h1 : c + 1 ≠ 0 := hc.2.2.1
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [w14_4, w14_5, rhsD]
  all_goals simp only [div_eq_mul_inv, mul_inv]; grind

lemma walk14_edge_6_5 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    PLAdj 10 F (w14_6 c) (w14_5 c) := by
  have h1 : c + 1 ≠ 0 := hc.2.2.1
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [w14_6, w14_5, rhsD]
  all_goals simp only [div_eq_mul_inv, mul_inv]; grind

lemma walk14_edge_6_7 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    PLAdj 10 F (w14_6 c) (w14_7 c) := by
  have h1 : c + 1 ≠ 0 := hc.2.2.1
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [w14_6, w14_7, rhsD]
  all_goals simp only [div_eq_mul_inv, mul_inv]; grind

lemma walk14_edge_8_7 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    PLAdj 10 F (w14_8 c) (w14_7 c) := by
  have h1 : c + 1 ≠ 0 := hc.2.2.1
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [w14_8, w14_7, rhsD]
  all_goals simp only [div_eq_mul_inv, mul_inv]; grind

lemma walk14_edge_8_9 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    PLAdj 10 F (w14_8 c) (w14_9 c) := by
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro j hj
  fin_cases j
  · simp at hj
  all_goals simp [w14_8, w14_9, rhsD]
  all_goals grind

lemma walk14_edge_10_9 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_10 c) (w14_9 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_10, w14_9, rhsD]

lemma walk14_edge_10_11 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_10 c) (w14_11 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_10, w14_11, rhsD]

lemma walk14_edge_12_11 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_12 c) (w14_11 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_12, w14_11, rhsD]

lemma walk14_edge_12_13 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_12 c) (w14_13 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_12, w14_13, rhsD]

lemma walk14_edge_0_13 {F : Type*} [Field F] (c : F) : PLAdj 10 F (w14_0 c) (w14_13 c) := by
  intro j hj; fin_cases j <;> simp_all [w14_0, w14_13, rhsD]

/-- All 14 cyclic edges of `walk14 c` hold in `D(10, F)` for every admissible `c`. -/
lemma walk14_adj {F : Type*} [Field F] {c : F} (hc : Admissible c) (i : Fin 14) :
    (DGraph 10 F).Adj (walk14 c i) (walk14 c ⟨(i.val + 1) % 14, Nat.mod_lt _ (by omega)⟩) := by
  fin_cases i
  · exact walk14_edge_0_1 c
  · exact walk14_edge_2_1 c
  · exact walk14_edge_2_3 c
  · exact walk14_edge_4_3 hc
  · exact walk14_edge_4_5 hc
  · exact walk14_edge_6_5 hc
  · exact walk14_edge_6_7 hc
  · exact walk14_edge_8_7 hc
  · exact walk14_edge_8_9 hc
  · exact walk14_edge_10_9 c
  · exact walk14_edge_10_11 c
  · exact walk14_edge_12_11 c
  · exact walk14_edge_12_13 c
  · exact walk14_edge_0_13 c

/-- Non-backtracking of `walk14 c`: for every `i : Fin 14`, `walk14 c i ≠ walk14 c (i + 2 mod 14)`
(checked via the 14 first-coordinate differences, valid in every characteristic). -/
lemma walk14_nb {F : Type*} [Field F] {c : F} (hc : Admissible c) (i : Fin 14) :
    walk14 c i ≠ walk14 c ⟨(i.val + 2) % 14, Nat.mod_lt _ (by omega)⟩ := by
  have hc0 : c ≠ 0 := hc.1
  have hc1 : c - 1 ≠ 0 := hc.sub_one_ne_zero
  have h1c : 1 - c ≠ 0 := hc.one_sub_ne_zero
  have hq1 : c + 1 ≠ 0 := hc.2.2.1
  have hq2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  intro heq
  have hfc : firstCoord (by omega : 0 < 10) (walk14 c i) =
      firstCoord (by omega : 0 < 10) (walk14 c ⟨(i.val + 2) % 14, Nat.mod_lt _ (by omega)⟩) :=
    congrArg (firstCoord (by omega : 0 < 10)) heq
  fin_cases i <;>
    simp only [walk14, firstCoord, w14_0, w14_1, w14_2, w14_3, w14_4, w14_5, w14_6, w14_7, w14_8,
      w14_9, w14_10, w14_11, w14_12, w14_13, Fin.zero_eta, Matrix.cons_val_zero] at hfc
  · exact zero_ne_one hfc
  · exact div_ne_zero h1c hq1 hfc.symm
  · have hdiff : (1 : F) - (c - 1) / (c ^ 2 + 2 * c - 1) =
        c * (c + 1) / (c ^ 2 + 2 * c - 1) := by grind
    have hz : c * (c + 1) / (c ^ 2 + 2 * c - 1) = 0 := by rw [← hdiff]; exact sub_eq_zero.2 hfc
    exact div_ne_zero (mul_ne_zero hc0 hq1) hq2 hz
  · have hdiff : (1 - c) / (c + 1) - c = -(c ^ 2 + 2 * c - 1) / (c + 1) := by grind
    have hz : -(c ^ 2 + 2 * c - 1) / (c + 1) = 0 := by rw [← hdiff]; exact sub_eq_zero.2 hfc
    exact div_ne_zero (neg_ne_zero.2 hq2) hq1 hz
  · have hdiff : (c - 1) / (c ^ 2 + 2 * c - 1) - 2 * c / (c ^ 2 + 2 * c - 1) =
        -(c + 1) / (c ^ 2 + 2 * c - 1) := by grind
    have hz : -(c + 1) / (c ^ 2 + 2 * c - 1) = 0 := by rw [← hdiff]; exact sub_eq_zero.2 hfc
    exact div_ne_zero (neg_ne_zero.2 hq1) hq2 hz
  · have hdiff : c - (1 - c) / (c + 1) = (c ^ 2 + 2 * c - 1) / (c + 1) := by grind
    have hz : (c ^ 2 + 2 * c - 1) / (c + 1) = 0 := by rw [← hdiff]; exact sub_eq_zero.2 hfc
    exact div_ne_zero hq2 hq1 hz
  · have hdiff : 2 * c / (c ^ 2 + 2 * c - 1) - (c - 1) / (c ^ 2 + 2 * c - 1) =
        (c + 1) / (c ^ 2 + 2 * c - 1) := by grind
    have hz : (c + 1) / (c ^ 2 + 2 * c - 1) = 0 := by rw [← hdiff]; exact sub_eq_zero.2 hfc
    exact div_ne_zero hq1 hq2 hz
  · have hdiff : (1 - c) / (c + 1) - c = -(c ^ 2 + 2 * c - 1) / (c + 1) := by grind
    have hz : -(c ^ 2 + 2 * c - 1) / (c + 1) = 0 := by rw [← hdiff]; exact sub_eq_zero.2 hfc
    exact div_ne_zero (neg_ne_zero.2 hq2) hq1 hz
  · exact div_ne_zero hc1 hq2 hfc
  · exact hc0 hfc
  · exact zero_ne_one hfc
  · exact zero_ne_one hfc
  · exact one_ne_zero hfc
  · exact one_ne_zero hfc

/-- For every field `F` and admissible `c : F`, `walk14 c` is a closed non-backtracking walk of
length 14 in `D(10, F)`. -/
theorem walk14_closedNBWalk_D10 {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    ClosedNBWalk (DGraph 10 F) 14 :=
  ⟨by omega, walk14 c, walk14_adj hc, walk14_nb hc⟩

/-! ### Exact Girth 14 for Any Field with an Admissible Parameter -/

/-- Unconditional exact girth 14 for `D(10, F)` whenever `F` contains an admissible `c`. -/
theorem D10_exact_girth_14_of_admissible {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    HasExactGirth (DGraph 10 F) 14 :=
  hasExactGirth_of_closed_nb_walk_of_girthAtLeast (D10_girthAtLeast_14 F)
    (walk14_closedNBWalk_D10 hc)

/-- Unconditional exact girth 14 for `D(9, F)` whenever `F` contains an admissible `c`. -/
theorem D9_exact_girth_14_of_admissible {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    HasExactGirth (DGraph 9 F) 14 := by
  have hge : GirthAtLeast (DGraph 9 F) 14 := D9_girthAtLeast_14 F
  have hle : GirthAtMost (DGraph 9 F) 14 :=
    girthAtMost_mono_k (by omega) (D10_exact_girth_14_of_admissible hc).girthAtMost
  rcases hle with ⟨r, hr3, hr14, hcr⟩
  have hreq : r = 14 := by
    by_contra hne
    exact hge r hr3 (lt_of_le_of_ne hr14 hne) hcr
  subst hreq
  exact ⟨hge, hcr⟩

/-! ### Sharpness at `k = 11`: Exact Nonzero Residue `c (c - 1) / (c² + 2 c - 1)` -/

lemma stepLine_eq_of_plAdj {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k)
    {p l : Fin k → F} {x : F} (hadj : PLAdj k F p l) (hx : l ⟨0, hk⟩ = x) :
    stepLine p x = l :=
  unique_line_of_firstCoord hk (stepLine_adj p x) hadj ((stepLine_zero hk p x).trans hx.symm)

lemma stepPoint_eq_of_plAdj {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k)
    {p l : Fin k → F} {x : F} (hadj : PLAdj k F p l) (hx : p ⟨0, hk⟩ = x) :
    stepPoint l x = p :=
  unique_point_of_firstCoord hk (stepPoint_adj l x) hadj ((stepPoint_zero hk l x).trans hx.symm)

lemma truncVec_stepLine {k₁ k₂ : ℕ} {F : Type*} [CommRing F] (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂)
    (p : Fin k₂ → F) (x : F) :
    truncVec hle (stepLine p x) = stepLine (truncVec hle p) x :=
  (stepLine_eq_of_plAdj hk₁ (truncVec_plAdj hle (stepLine_adj p x))
    (stepLine_zero (lt_of_lt_of_le hk₁ hle) p x)).symm

lemma truncVec_stepPoint {k₁ k₂ : ℕ} {F : Type*} [CommRing F] (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂)
    (l : Fin k₂ → F) (x : F) :
    truncVec hle (stepPoint l x) = stepPoint (truncVec hle l) x :=
  (stepPoint_eq_of_plAdj hk₁ (truncVec_plAdj hle (stepPoint_adj l x))
    (stepPoint_zero (lt_of_lt_of_le hk₁ hle) l x)).symm

lemma stepLine_D11_val10 {F : Type*} [CommRing F] (p : Fin 11 → F) (x : F) :
    stepLine p x ⟨10, by omega⟩ =
      p ⟨0, by omega⟩ * (stepLine p x ⟨8, by omega⟩) - p ⟨10, by omega⟩ := by
  simp [stepLine, stepLineCoord]

lemma stepPoint_D11_val10 {F : Type*} [CommRing F] (l : Fin 11 → F) (x : F) :
    stepPoint l x ⟨10, by omega⟩ =
      x * l ⟨8, by omega⟩ - l ⟨10, by omega⟩ := by
  simp [stepPoint, stepPointCoord]

/-- Lifting the 14-step walk from `(0)` in `D(11, F)` with the exact same first-coordinate sequence
`[0, 1, a, b, c, d, a, b, c, 0, 0, 1, 1, 0]` ends at a point whose 11th coordinate (index 10) is
`c * (c - 1) / (c ^ 2 + 2 * c - 1) ≠ 0`, so the walk fails to close in `D(11, F)`. -/
theorem walk14_D11_fails_closure {F : Type*} [Field F] {c : F} (hc : Admissible c) :
    let a := (1 - c) / (1 + c)
    let b := (c - 1) / (c ^ 2 + 2 * c - 1)
    let d := 2 * c / (c ^ 2 + 2 * c - 1)
    let p0 : Fin 11 → F := 0
    let l1 := stepLine p0 0
    let p2 := stepPoint l1 1
    let l3 := stepLine p2 a
    let p4 := stepPoint l3 b
    let l5 := stepLine p4 c
    let p6 := stepPoint l5 d
    let l7 := stepLine p6 a
    let p8 := stepPoint l7 b
    let l9 := stepLine p8 c
    let p10 := stepPoint l9 0
    let l11 := stepLine p10 0
    let p12 := stepPoint l11 1
    let l13 := stepLine p12 1
    let p14 := stepPoint l13 0
    p14 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) ∧ p14 ≠ 0 := by
  let a := (1 - c) / (1 + c)
  let b := (c - 1) / (c ^ 2 + 2 * c - 1)
  let d := 2 * c / (c ^ 2 + 2 * c - 1)
  let p0 : Fin 11 → F := 0
  let l1 := stepLine p0 0
  let p2 := stepPoint l1 1
  let l3 := stepLine p2 a
  let p4 := stepPoint l3 b
  let l5 := stepLine p4 c
  let p6 := stepPoint l5 d
  let l7 := stepLine p6 a
  let p8 := stepPoint l7 b
  let l9 := stepLine p8 c
  let p10 := stepPoint l9 0
  let l11 := stepLine p10 0
  let p12 := stepPoint l11 1
  let l13 := stepLine p12 1
  let p14 := stepPoint l13 0
  change p14 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) ∧ p14 ≠ 0
  have h1 : c + 1 ≠ 0 := hc.2.2.1
  have h2 : c ^ 2 + 2 * c - 1 ≠ 0 := hc.2.2.2
  have hk10 : 0 < 10 := by omega
  have hle : 10 ≤ 11 := by omega
  have ha : a = (1 - c) / (c + 1) := by dsimp [a]; rw [add_comm]
  have ht0 : truncVec hle p0 = w14_0 c := by
    ext j; fin_cases j <;> rfl
  have ht1 : truncVec hle l1 = w14_1 c := by
    dsimp only [l1]; rw [truncVec_stepLine hk10 hle, ht0]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_0_1 c) rfl
  have ht2 : truncVec hle p2 = w14_2 c := by
    dsimp only [p2]; rw [truncVec_stepPoint hk10 hle, ht1]
    exact stepPoint_eq_of_plAdj hk10 (walk14_edge_2_1 c) rfl
  have ht3 : truncVec hle l3 = w14_3 c := by
    dsimp only [l3]; rw [truncVec_stepLine hk10 hle, ht2, ha]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_2_3 c) rfl
  have ht4 : truncVec hle p4 = w14_4 c := by
    dsimp only [p4]; rw [truncVec_stepPoint hk10 hle, ht3]
    exact stepPoint_eq_of_plAdj hk10 (walk14_edge_4_3 hc) rfl
  have ht5 : truncVec hle l5 = w14_5 c := by
    dsimp only [l5]; rw [truncVec_stepLine hk10 hle, ht4]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_4_5 hc) rfl
  have ht6 : truncVec hle p6 = w14_6 c := by
    dsimp only [p6]; rw [truncVec_stepPoint hk10 hle, ht5]
    exact stepPoint_eq_of_plAdj hk10 (walk14_edge_6_5 hc) rfl
  have ht7 : truncVec hle l7 = w14_7 c := by
    dsimp only [l7]; rw [truncVec_stepLine hk10 hle, ht6, ha]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_6_7 hc) rfl
  have ht8 : truncVec hle p8 = w14_8 c := by
    dsimp only [p8]; rw [truncVec_stepPoint hk10 hle, ht7]
    exact stepPoint_eq_of_plAdj hk10 (walk14_edge_8_7 hc) rfl
  have ht9 : truncVec hle l9 = w14_9 c := by
    dsimp only [l9]; rw [truncVec_stepLine hk10 hle, ht8]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_8_9 hc) rfl
  have ht10 : truncVec hle p10 = w14_10 c := by
    dsimp only [p10]; rw [truncVec_stepPoint hk10 hle, ht9]
    exact stepPoint_eq_of_plAdj hk10 (walk14_edge_10_9 c) rfl
  have ht11 : truncVec hle l11 = w14_11 c := by
    dsimp only [l11]; rw [truncVec_stepLine hk10 hle, ht10]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_10_11 c) rfl
  have ht12 : truncVec hle p12 = w14_12 c := by
    dsimp only [p12]; rw [truncVec_stepPoint hk10 hle, ht11]
    exact stepPoint_eq_of_plAdj hk10 (walk14_edge_12_11 c) rfl
  have ht13 : truncVec hle l13 = w14_13 c := by
    dsimp only [l13]; rw [truncVec_stepLine hk10 hle, ht12]
    exact stepLine_eq_of_plAdj hk10 (walk14_edge_12_13 c) rfl
  -- Extract coordinates 0 and 8 via `truncVec` + kernel `rfl`
  have hl1_8 : stepLine p0 0 ⟨8, by omega⟩ = 0 := (congrFun ht1 ⟨8, by omega⟩).trans rfl
  have hl3_8 : stepLine p2 a ⟨8, by omega⟩ = 0 := (congrFun ht3 ⟨8, by omega⟩).trans rfl
  have hl5_8 : stepLine p4 c ⟨8, by omega⟩ = 0 := (congrFun ht5 ⟨8, by omega⟩).trans rfl
  have hp6_0 : p6 ⟨0, by omega⟩ = 2 * c / (c ^ 2 + 2 * c - 1) :=
    (congrFun ht6 ⟨0, by omega⟩).trans rfl
  have hl7_8 : stepLine p6 a ⟨8, by omega⟩ = -c * (c - 1) / (c + 1) :=
    (congrFun ht7 ⟨8, by omega⟩).trans rfl
  have hl9_8 : stepLine p8 c ⟨8, by omega⟩ = 0 := (congrFun ht9 ⟨8, by omega⟩).trans rfl
  have hl11_8 : stepLine p10 0 ⟨8, by omega⟩ = 0 := (congrFun ht11 ⟨8, by omega⟩).trans rfl
  have hl13_8 : stepLine p12 1 ⟨8, by omega⟩ = 0 := (congrFun ht13 ⟨8, by omega⟩).trans rfl
  -- Evaluate coordinate 10 step by step along the 14 edges
  have hp0_10 : p0 ⟨10, by omega⟩ = 0 := rfl
  have hl1_10 : l1 ⟨10, by omega⟩ = 0 := by
    dsimp only [l1]; rw [stepLine_D11_val10, hl1_8, hp0_10]; ring
  have hp2_10 : p2 ⟨10, by omega⟩ = 0 := by
    dsimp only [p2]; rw [stepPoint_D11_val10]; dsimp only [l1]; rw [hl1_8]; change 1 * 0 - l1 ⟨10, by omega⟩ = 0; rw [hl1_10]; ring
  have hl3_10 : l3 ⟨10, by omega⟩ = 0 := by
    dsimp only [l3]; rw [stepLine_D11_val10, hl3_8, hp2_10]; ring
  have hp4_10 : p4 ⟨10, by omega⟩ = 0 := by
    dsimp only [p4]; rw [stepPoint_D11_val10]; dsimp only [l3]; rw [hl3_8]; change b * 0 - l3 ⟨10, by omega⟩ = 0; rw [hl3_10]; ring
  have hl5_10 : l5 ⟨10, by omega⟩ = 0 := by
    dsimp only [l5]; rw [stepLine_D11_val10, hl5_8, hp4_10]; ring
  have hp6_10 : p6 ⟨10, by omega⟩ = 0 := by
    dsimp only [p6]; rw [stepPoint_D11_val10]; dsimp only [l5]; rw [hl5_8]; change d * 0 - l5 ⟨10, by omega⟩ = 0; rw [hl5_10]; ring
  have hl7_10 : l7 ⟨10, by omega⟩ = -2 * c ^ 2 * (c - 1) / ((c + 1) * (c ^ 2 + 2 * c - 1)) := by
    dsimp only [l7]; rw [stepLine_D11_val10, hp6_0, hl7_8, hp6_10]
    simp only [div_eq_mul_inv, mul_inv]; ring
  have hp8_10 : p8 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) := by
    dsimp only [p8]; rw [stepPoint_D11_val10]
    have h78 : l7 ⟨8, by omega⟩ = -c * (c - 1) / (c + 1) := hl7_8
    rw [h78, hl7_10]; dsimp only [b]
    have hinv1 : (c + 1) * (c + 1)⁻¹ = 1 := mul_inv_cancel₀ h1
    simp only [div_eq_mul_inv, mul_inv]
    linear_combination (c * (c - 1) * (c ^ 2 + 2 * c - 1)⁻¹) * hinv1
  have hl9_10 : l9 ⟨10, by omega⟩ = -(c * (c - 1) / (c ^ 2 + 2 * c - 1)) := by
    dsimp only [l9]; rw [stepLine_D11_val10, hl9_8, hp8_10]; ring
  have hp10_10 : p10 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) := by
    dsimp only [p10]; rw [stepPoint_D11_val10, hl9_10]; ring
  have hl11_10 : l11 ⟨10, by omega⟩ = -(c * (c - 1) / (c ^ 2 + 2 * c - 1)) := by
    dsimp only [l11]; rw [stepLine_D11_val10, hl11_8, hp10_10]; ring
  have hp12_10 : p12 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) := by
    dsimp only [p12]; rw [stepPoint_D11_val10]
    have h118 : l11 ⟨8, by omega⟩ = 0 := hl11_8
    rw [h118, hl11_10]; ring
  have hl13_10 : l13 ⟨10, by omega⟩ = -(c * (c - 1) / (c ^ 2 + 2 * c - 1)) := by
    dsimp only [l13]; rw [stepLine_D11_val10, hl13_8, hp12_10]; ring
  have hval : p14 ⟨10, by omega⟩ = c * (c - 1) / (c ^ 2 + 2 * c - 1) := by
    dsimp only [p14]; rw [stepPoint_D11_val10, hl13_10]; ring
  refine ⟨hval, ?_⟩
  intro hzero
  have hz : p14 ⟨10, by omega⟩ = 0 := by
    simpa only [Pi.zero_apply] using congrFun hzero ⟨10, by omega⟩
  rw [hval] at hz
  exact div_ne_zero (mul_ne_zero hc.1 hc.sub_one_ne_zero) h2 hz

/-! ### Existence of an Admissible Parameter `c` in Every Field with `|F| ≥ 4` -/

open Polynomial in
/-- The degree-5 exclusion polynomial `X (X - 1) (X + 1) (X² + 2 X - 1)`. -/
noncomputable def exclPoly (F : Type*) [Field F] : Polynomial F :=
  X * (X - 1) * (X + 1) * (X ^ 2 + C 2 * X - 1)

open Polynomial in
lemma exclPoly_ne_zero (F : Type*) [Field F] : exclPoly F ≠ 0 := by
  unfold exclPoly
  have h1 : (X : Polynomial F) ≠ 0 := X_ne_zero
  have h2 : (X - 1 : Polynomial F) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 1) h
    simp [coeff_one] at this
  have h3 : (X + 1 : Polynomial F) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 1) h
    simp [coeff_one] at this
  have h4 : (X ^ 2 + C 2 * X - 1 : Polynomial F) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.coeff 2) h
    simp [coeff_X_pow, coeff_one] at this
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4

open Polynomial in
lemma exclPoly_natDegree_le (F : Type*) [Field F] : (exclPoly F).natDegree ≤ 5 := by
  unfold exclPoly
  have d1 : (X : Polynomial F).natDegree ≤ 1 := natDegree_X_le
  have d2 : (X - 1 : Polynomial F).natDegree ≤ 1 := by
    calc (X - 1 : Polynomial F).natDegree
      _ ≤ max (X : Polynomial F).natDegree (1 : Polynomial F).natDegree := natDegree_sub_le _ _
      _ ≤ 1 := by simp
  have d3 : (X + 1 : Polynomial F).natDegree ≤ 1 := by
    calc (X + 1 : Polynomial F).natDegree
      _ ≤ max (X : Polynomial F).natDegree (1 : Polynomial F).natDegree := natDegree_add_le _ _
      _ ≤ 1 := by simp
  have d4 : (X ^ 2 + C 2 * X - 1 : Polynomial F).natDegree ≤ 2 := by
    have da : (X ^ 2 + C 2 * X : Polynomial F).natDegree ≤ 2 := by
      calc (X ^ 2 + C 2 * X : Polynomial F).natDegree
        _ ≤ max (X ^ 2 : Polynomial F).natDegree (C 2 * X : Polynomial F).natDegree :=
            natDegree_add_le _ _
        _ ≤ 2 := by
            apply max_le
            · simp
            · exact le_trans (natDegree_C_mul_le _ _) (by simp)
    calc (X ^ 2 + C 2 * X - 1 : Polynomial F).natDegree
      _ ≤ max (X ^ 2 + C 2 * X : Polynomial F).natDegree (1 : Polynomial F).natDegree :=
          natDegree_sub_le _ _
      _ ≤ 2 := max_le da (by simp)
  calc (X * (X - 1) * (X + 1) * (X ^ 2 + C 2 * X - 1) : Polynomial F).natDegree
    _ ≤ (X * (X - 1) * (X + 1) : Polynomial F).natDegree +
        (X ^ 2 + C 2 * X - 1 : Polynomial F).natDegree := natDegree_mul_le
    _ ≤ (X * (X - 1) : Polynomial F).natDegree + (X + 1 : Polynomial F).natDegree +
        (X ^ 2 + C 2 * X - 1 : Polynomial F).natDegree := by
          gcongr; exact natDegree_mul_le
    _ ≤ (X : Polynomial F).natDegree + (X - 1 : Polynomial F).natDegree +
        (X + 1 : Polynomial F).natDegree + (X ^ 2 + C 2 * X - 1 : Polynomial F).natDegree := by
          gcongr; exact natDegree_mul_le
    _ ≤ 1 + 1 + 1 + 2 := by omega
    _ = 5 := rfl

open Polynomial in
lemma admissible_of_exclPoly_eval_ne_zero {F : Type*} [Field F] {c : F}
    (h : (exclPoly F).eval c ≠ 0) : Admissible c := by
  simp only [exclPoly, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_one, eval_C] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc0; exact h (by simp [hc0])
  · intro hc1; exact h (by simp [hc1])
  · intro hcp1; exact h (by simp [hcp1])
  · intro hcq; exact h (by simp [hcq])

/-- Every finite field `F` with `4 ≤ Fintype.card F` contains an admissible parameter `c : F`. -/
theorem exists_admissible_of_card_ge_four (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) : ∃ c : F, Admissible c := by
  classical
  by_cases h2 : (2 : F) = 0
  · -- Characteristic 2: only `{0, 1}` are excluded
    let bad : Finset F := {0, 1}
    have hbad : bad.card ≤ 2 := Finset.card_le_two
    have hlt : bad.card < (Finset.univ : Finset F).card := by
      rw [Finset.card_univ]; omega
    rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨c, _, hcnot⟩
    have hc0 : c ≠ 0 := fun h => hcnot (by simp [bad, h])
    have hc1 : c ≠ 1 := fun h => hcnot (by simp [bad, h])
    refine ⟨c, hc0, hc1, ?_, ?_⟩
    · intro hcp1
      apply hc1
      have : c + 1 = c - 1 := by linear_combination h2
      rw [this] at hcp1
      exact sub_eq_zero.1 hcp1
    · intro hcq
      have hsq : (c - 1) * (c - 1) = 0 := by
        linear_combination hcq + (1 - 2 * c) * h2
      exact hc1 (sub_eq_zero.1 (mul_self_eq_zero.1 hsq))
  · -- Odd characteristic (`2 ≠ 0`)
    by_cases h6 : 6 ≤ Fintype.card F
    · -- General case `|F| ≥ 6`: the degree-5 polynomial `exclPoly F` has at most 5 roots
      let roots : Finset F := (exclPoly F).roots.toFinset
      have hroots : roots.card ≤ 5 := by
        calc roots.card
          _ ≤ (exclPoly F).roots.card := Multiset.toFinset_card_le _
          _ ≤ (exclPoly F).natDegree := Polynomial.card_roots' _
          _ ≤ 5 := exclPoly_natDegree_le F
      have hlt : roots.card < (Finset.univ : Finset F).card := by
        rw [Finset.card_univ]; omega
      rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨c, _, hcnot⟩
      refine ⟨c, admissible_of_exclPoly_eval_ne_zero ?_⟩
      intro heval
      apply hcnot
      simp only [roots, Multiset.mem_toFinset, Polynomial.mem_roots (exclPoly_ne_zero F),
        Polynomial.IsRoot.def]
      exact heval
    · -- Remaining small sizes with `2 ≠ 0`: `|F| ∈ {4, 5}`
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
              rw [hzero, zero_dvd_iff] at hdvd
              omega
            · have hsub : ((a.val - b.val : ℕ) : F) = 0 := by
                rw [Nat.cast_sub (le_of_lt hgt), hab, sub_self]
              have hdvd : ringChar F ∣ (a.val - b.val) := (ringChar.spec F _).1 hsub
              rw [hzero, zero_dvd_iff] at hdvd
              omega
          have hle := Fintype.card_le_of_injective _ hinj
          simp only [Fintype.card_fin] at hle
          omega
        exact (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right h0
      have hdvd : ringChar F ∣ Fintype.card F := by
        have hord : addOrderOf (1 : F) = ringChar F := by
          rw [addOrderOf_eq_iff hchar_prime.pos]
          refine ⟨by simp, fun m hm hpos hm0 => ?_⟩
          have hns : (m : F) = 0 := by simpa using hm0
          have hdv := (ringChar.spec F m).1 hns
          exact Nat.not_lt_of_ge (Nat.le_of_dvd hpos hdv) hm
        rw [← hord]
        exact addOrderOf_dvd_card (x := (1 : F))
      have hcard45 : Fintype.card F = 4 ∨ Fintype.card F = 5 := by omega
      rcases hcard45 with h4 | h5
      · -- `|F| = 4` forces `char F = 2`, contradicting `2 ≠ 0`
        rw [h4] at hdvd
        have hp2 : ringChar F = 2 := by
          have hle : ringChar F ≤ 4 := Nat.le_of_dvd (by omega) hdvd
          have hge2 := hchar_prime.two_le
          interval_cases h : ringChar F
          · rfl
          · omega
          · exfalso; exact (by decide : ¬ Nat.Prime 4) (h ▸ hchar_prime)
        exfalso
        have hcast : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
        rw [hp2] at hcast
        norm_num at hcast
        exact h2 hcast
      · -- `|F| = 5` forces `char F = 5`; take `c = 2`
        rw [h5] at hdvd
        have hp5 : ringChar F = 5 := (Nat.prime_dvd_prime_iff_eq hchar_prime (by decide)).1 hdvd
        have h5zero : (5 : F) = 0 := by
          have hcast : ((ringChar F : ℕ) : F) = 0 := ringChar.Nat.cast_ringChar
          rw [hp5] at hcast
          simpa using hcast
        refine ⟨(2 : F), h2, ?_, ?_, ?_⟩
        · intro h21
          exact one_ne_zero (by linear_combination h21 : (1 : F) = 0)
        · intro h3
          exact h2 (by linear_combination h5zero - h3 : (2 : F) = 0)
        · intro h7
          exact h2 (by linear_combination h7 - h5zero : (2 : F) = 0)

/-- Every infinite field `F` contains an admissible parameter `c : F`. -/
theorem exists_admissible_of_infinite (F : Type*) [Field F] [Infinite F] :
    ∃ c : F, Admissible c := by
  classical
  let roots : Finset F := (exclPoly F).roots.toFinset
  rcases Infinite.exists_notMem_finset roots with ⟨c, hcnot⟩
  refine ⟨c, admissible_of_exclPoly_eval_ne_zero ?_⟩
  intro heval
  apply hcnot
  simp only [roots, Multiset.mem_toFinset, Polynomial.mem_roots (exclPoly_ne_zero F),
    Polynomial.IsRoot.def]
  exact heval

/-! ### Headline Unconditional Theorems (R19-4-1 / DS28 Conjecture 46 at `k = 9, 10`) -/

/-- **Main Theorem (R19-4-1 / DS28 Conjecture 46 at `k = 9, 10`)**:
For **every** finite field `F` of cardinality `q ≥ 4` (every prime power `q ≥ 4`, including
characteristics 2 and 3), the Lazebnik–Ustimenko graphs `D(9, F)` and `D(10, F)` both have
exact girth 14 — proved 100% unconditionally in Lean 4. -/
theorem D9_D10_exact_girth_14_all_q_ge_4 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 := by
  rcases exists_admissible_of_card_ge_four F hcard with ⟨c, hc⟩
  exact ⟨D9_exact_girth_14_of_admissible hc, D10_exact_girth_14_of_admissible hc⟩

/-- Unconditional exact girth 14 for `D(9, F)` and `D(10, F)` over every infinite field `F`. -/
theorem D9_D10_exact_girth_14_infinite (F : Type*) [Field F] [Infinite F] :
    HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 := by
  rcases exists_admissible_of_infinite F with ⟨c, hc⟩
  exact ⟨D9_exact_girth_14_of_admissible hc, D10_exact_girth_14_of_admissible hc⟩

/-- Same unconditional exact girth 14 theorem for the original DS28 minus-sign representation
`DGraphOrig 9 F` and `DGraphOrig 10 F` (via DS28 Prop. 38 isomorphism). -/
theorem D9_D10_orig_exact_girth_14_all_q_ge_4 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraphOrig 9 F) 14 ∧ HasExactGirth (DGraphOrig 10 F) 14 := by
  rcases D9_D10_exact_girth_14_all_q_ge_4 F hcard with ⟨h9, h10⟩
  exact ⟨h9.of_iso (DGraph_iso_DGraphOrig 9 F), h10.of_iso (DGraph_iso_DGraphOrig 10 F)⟩

/-- Explicit closure of characteristic 2 (`q = 2^m ≥ 4`, e.g., `q = 4, 8, 16, 32, ...`). -/
theorem D9_D10_exact_girth_14_char2 (F : Type*) [Field F] [Fintype F] [CharP F 2]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 :=
  D9_D10_exact_girth_14_all_q_ge_4 F hcard

/-- Explicit closure of characteristic 3 (`q = 3^m ≥ 9`, e.g., `q = 9, 27, 81, ...`). -/
theorem D9_D10_exact_girth_14_char3 (F : Type*) [Field F] [Fintype F] [CharP F 3]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 :=
  D9_D10_exact_girth_14_all_q_ge_4 F hcard

end LazebnikUstimenko
