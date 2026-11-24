module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Palomar Challenge: Exact Girths of Lazebnik–Ustimenko Graphs `D(k, q)`

Self-contained Lean 4 + Mathlib statements (zero `by` tactic blocks inside any
definition; zero `sorry` in `Solution`, zero `native_decide`, standard axioms
only):

1. **Girth 14 in dimensions 9 and 10 over all fields with `|F| ≥ 4`**
   (`D9_D10_exact_girth_14_all_q_ge_4`, `D9_D10_orig_exact_girth_14_all_q_ge_4`,
   `D9_D10_exact_girth_14_galoisField`, `DS28_table7_blank_cells_27_32`,
   `card_admissible_ge_two_of_card_ge_four`), closing characteristics 2 and 3.
2. **Complete binary girth law `girth D(k, 2) = 2^s` and refutation of the
   `2^{k-3} C_16` claim** (`D2_exact_girth_law`, `D2_exact_girth_orig_law`,
   `D2_girth_gt_16_of_ge_13`).
3. **Unconditional kernel-verified ternary girths `D(k, 3)` and first open case
   tightening** (`D3_exact_girths_highlights`, `D3_k52_bounds_56_60`).
-/

@[expose] public section

namespace LazebnikUstimenkoChallenge

/-- Vertices of `D(k, F)`: `Sum.inl p` is a point and `Sum.inr l` is a line. -/
abbrev Vertex (k : ℕ) (F : Type*) := (Fin k → F) ⊕ (Fin k → F)

/-- Right-hand side `fᵢ(p, l)` of the DS28 Section 6.1 working equations for `D(k, F)`. -/
def rhsD {k : ℕ} {F : Type*} [CommRing F] (p l : Fin k → F) (j : Fin k) : F :=
  if h0 : 0 < k then
    if _h1 : j.val = 1 then
      p ⟨0, h0⟩ * l ⟨0, h0⟩
    else if h2 : j.val = 2 then
      p ⟨0, h0⟩ * l ⟨1, Nat.lt_trans Nat.one_lt_two (h2 ▸ j.isLt)⟩
    else if _h3 : 3 ≤ j.val then
      if (j.val + 1) % 4 = 0 ∨ (j.val + 1) % 4 = 1 then
        p ⟨j.val - 2, Nat.lt_of_le_of_lt (Nat.sub_le j.val 2) j.isLt⟩ * l ⟨0, h0⟩
      else
        p ⟨0, h0⟩ * l ⟨j.val - 2, Nat.lt_of_le_of_lt (Nat.sub_le j.val 2) j.isLt⟩
    else
      0
  else
    0

/-- Point-line adjacency in `D(k, F)`. -/
def PLAdj (k : ℕ) (F : Type*) [CommRing F] (p l : Fin k → F) : Prop :=
  ∀ (j : Fin k), 1 ≤ j.val → p j + l j = rhsD p l j

/-- Bipartite adjacency relation of `D(k, F)`. -/
def AdjD (k : ℕ) (F : Type*) [CommRing F] : Vertex k F → Vertex k F → Prop
  | Sum.inl p, Sum.inr l => PLAdj k F p l
  | Sum.inr l, Sum.inl p => PLAdj k F p l
  | _, _ => False

/-- The Lazebnik–Ustimenko bipartite graph `D(k, F)` (working equations). -/
def DGraph (k : ℕ) (F : Type*) [CommRing F] : SimpleGraph (Vertex k F) where
  Adj := AdjD k F
  symm := ⟨fun u v h => match u, v, h with
    | Sum.inl _, Sum.inr _, h => h
    | Sum.inr _, Sum.inl _, h => h⟩
  loopless := ⟨fun u h => match u, h with
    | Sum.inl _, h => h
    | Sum.inr _, h => h⟩

/-- Right-hand side of the original DS28 minus-sign equations for `D(k, F)`. -/
def rhsDOrig {k : ℕ} {F : Type*} [CommRing F] (p l : Fin k → F) (j : Fin k) : F :=
  if h0 : 0 < k then
    if _h1 : j.val = 1 then
      p ⟨0, h0⟩ * l ⟨0, h0⟩
    else if h2 : j.val = 2 then
      p ⟨0, h0⟩ * l ⟨1, Nat.lt_trans Nat.one_lt_two (h2 ▸ j.isLt)⟩
    else if _h3 : 3 ≤ j.val then
      if (j.val + 1) % 4 = 0 ∨ (j.val + 1) % 4 = 1 then
        -(p ⟨j.val - 2, Nat.lt_of_le_of_lt (Nat.sub_le j.val 2) j.isLt⟩ * l ⟨0, h0⟩)
      else
        p ⟨0, h0⟩ * l ⟨j.val - 2, Nat.lt_of_le_of_lt (Nat.sub_le j.val 2) j.isLt⟩
    else
      0
  else
    0

/-- Point-line adjacency in the original minus-sign representation of `D(k, F)`. -/
def PLAdjOrig (k : ℕ) (F : Type*) [CommRing F] (p l : Fin k → F) : Prop :=
  ∀ (j : Fin k), 1 ≤ j.val → p j + l j = rhsDOrig p l j

/-- Bipartite adjacency relation of the original minus-sign representation. -/
def AdjDOrig (k : ℕ) (F : Type*) [CommRing F] : Vertex k F → Vertex k F → Prop
  | Sum.inl p, Sum.inr l => PLAdjOrig k F p l
  | Sum.inr l, Sum.inl p => PLAdjOrig k F p l
  | _, _ => False

/-- The original minus-sign Lazebnik–Ustimenko graph as a `SimpleGraph`. -/
def DGraphOrig (k : ℕ) (F : Type*) [CommRing F] : SimpleGraph (Vertex k F) where
  Adj := AdjDOrig k F
  symm := ⟨fun u v h => match u, v, h with
    | Sum.inl _, Sum.inr _, h => h
    | Sum.inr _, Sum.inl _, h => h⟩
  loopless := ⟨fun u h => match u, h with
    | Sum.inl _, h => h
    | Sum.inr _, h => h⟩

/-- `HasCycleOfLen G m` asserts that `G` contains a simple cycle of exact length `m ≥ 3`. -/
def HasCycleOfLen {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (hm : 3 ≤ m) (v : Fin m → V), Function.Injective v ∧
    ∀ i : Fin m, G.Adj (v i) (v ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hm)⟩)

/-- `GirthAtMost G m` asserts `G` contains a simple cycle of length `r` with `3 ≤ r ≤ m`. -/
def GirthAtMost {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ r, 3 ≤ r ∧ r ≤ m ∧ HasCycleOfLen G r

/-- `GirthAtLeast G m` asserts `G` has no simple cycle of length strictly less than `m`. -/
def GirthAtLeast {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ r, 3 ≤ r → r < m → ¬ HasCycleOfLen G r

/-- `HasExactGirth G m` asserts the girth of `G` is exactly `m`. -/
def HasExactGirth {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  GirthAtLeast G m ∧ HasCycleOfLen G m

/-- Admissible cycle parameter `c ∈ F` for the universal 14-cycle in `D(9, F)` and `D(10, F)`. -/
def Admissible {F : Type*} [Field F] (c : F) : Prop :=
  c ≠ 0 ∧ c ≠ 1 ∧ c + 1 ≠ 0 ∧ c ^ 2 + 2 * c - 1 ≠ 0

/-- **Exact Girth 14 for `D(9, F)` and `D(10, F)` over every finite field with `|F| ≥ 4`**
(including characteristics 2 and 3). -/
theorem D9_D10_exact_girth_14_all_q_ge_4 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 := by
  sorry

/-- **Same girth-14 theorem in the original DS28 minus-sign model `DGraphOrig`.** -/
theorem D9_D10_orig_exact_girth_14_all_q_ge_4 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraphOrig 9 F) 14 ∧ HasExactGirth (DGraphOrig 10 F) 14 := by
  sorry

/-- **Direct `GaloisField p n` instantiation for every prime power `p^n ≥ 4`.** -/
theorem D9_D10_exact_girth_14_galoisField (p n : ℕ) [Fact p.Prime]
    (hn : n ≠ 0) (hq : 4 ≤ p ^ n) :
    HasExactGirth (DGraph 9 (GaloisField p n)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField p n)) 14 := by
  sorry

/-- **Explicit closure of the four empty DS28 Table 7 cells `(9, 27), (10, 27), (9, 32), (10, 32)`.** -/
theorem DS28_table7_blank_cells_27_32 :
    HasExactGirth (DGraph 9 (GaloisField 3 3)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField 3 3)) 14 ∧
    HasExactGirth (DGraph 9 (GaloisField 2 5)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField 2 5)) 14 := by
  sorry

/-- **At least two admissible 14-cycle parameters exist in every finite field with `|F| ≥ 4`.** -/
theorem card_admissible_ge_two_of_card_ge_four (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    2 ≤ Nat.card {c : F // Admissible c} := by
  sorry

/-- **Complete Binary Girth Law**: `girth D(k, 2) = 2^s` for every `s ≥ 3` and every `k ≥ 2`
with `2^(s-1) - 4 < k ≤ 2^s - 4`. -/
theorem D2_exact_girth_law {s k : ℕ} (hs : 3 ≤ s) (hk2 : 2 ≤ k)
    (hlo : 2 ^ (s - 1) - 4 < k) (hhi : k ≤ 2 ^ s - 4) :
    HasExactGirth (DGraph k (ZMod 2)) (2 ^ s) := by
  sorry

/-- **Complete Binary Girth Law in the original minus-sign model `DGraphOrig`.** -/
theorem D2_exact_girth_orig_law {s k : ℕ} (hs : 3 ≤ s) (hk2 : 2 ≤ k)
    (hlo : 2 ^ (s - 1) - 4 < k) (hhi : k ≤ 2 ^ s - 4) :
    HasExactGirth (DGraphOrig k (ZMod 2)) (2 ^ s) := by
  sorry

/-- **Refutation of the LSW (2017) / DS28 (2026) `2^{k-3} C_16` claim**:
for every `k ≥ 13`, `D(k, 2)` has girth at least `32` and contains no 16-cycle. -/
theorem D2_girth_gt_16_of_ge_13 {k : ℕ} (hk : 13 ≤ k) :
    GirthAtLeast (DGraph k (ZMod 2)) 32 ∧ ¬ HasCycleOfLen (DGraph k (ZMod 2)) 16 := by
  sorry

/-- **Unconditional Kernel-Verified Exact Ternary Girths `D(k, 3)`**:
exact girths at `k ∈ {15, 16}` (20, refuting Mukherjee's 22), `{47, 48}` (52),
`{55, 56}` (60), `{79, 80}` (84), `99` (104), and `{103, 104}` (108). -/
theorem D3_exact_girths_highlights :
    HasExactGirth (DGraph 15 (ZMod 3)) 20 ∧ HasExactGirth (DGraph 16 (ZMod 3)) 20 ∧
    HasExactGirth (DGraph 47 (ZMod 3)) 52 ∧ HasExactGirth (DGraph 48 (ZMod 3)) 52 ∧
    HasExactGirth (DGraph 55 (ZMod 3)) 60 ∧ HasExactGirth (DGraph 56 (ZMod 3)) 60 ∧
    HasExactGirth (DGraph 79 (ZMod 3)) 84 ∧ HasExactGirth (DGraph 80 (ZMod 3)) 84 ∧
    HasExactGirth (DGraph 99 (ZMod 3)) 104 ∧
    HasExactGirth (DGraph 103 (ZMod 3)) 108 ∧ HasExactGirth (DGraph 104 (ZMod 3)) 108 := by
  sorry

/-- **Unconditional tightening of the first open ternary case `k = 52`**:
`56 ≤ girth D(52, 3) ≤ 60`. -/
theorem D3_k52_bounds_56_60 :
    GirthAtLeast (DGraph 52 (ZMod 3)) 56 ∧ GirthAtMost (DGraph 52 (ZMod 3)) 60 := by
  sorry

end LazebnikUstimenkoChallenge
