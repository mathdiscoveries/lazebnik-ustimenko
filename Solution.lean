module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.SetTheory.Cardinal.Finite
import LazebnikUstimenko

/-!
# Palomar Solution: Exact Girths of Lazebnik–Ustimenko Graphs `D(k, q)`

Discharges every theorem in `Challenge.lean` (`LazebnikUstimenkoChallenge`)
unconditionally from `LazebnikUstimenko`, with zero `sorry`, zero
`native_decide`, and standard axioms only (`propext`, `Quot.sound`,
`Classical.choice`).
-/

@[expose] public section

namespace LazebnikUstimenkoChallenge

abbrev Vertex (k : ℕ) (F : Type*) := (Fin k → F) ⊕ (Fin k → F)

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

def PLAdj (k : ℕ) (F : Type*) [CommRing F] (p l : Fin k → F) : Prop :=
  ∀ (j : Fin k), 1 ≤ j.val → p j + l j = rhsD p l j

def AdjD (k : ℕ) (F : Type*) [CommRing F] : Vertex k F → Vertex k F → Prop
  | Sum.inl p, Sum.inr l => PLAdj k F p l
  | Sum.inr l, Sum.inl p => PLAdj k F p l
  | _, _ => False

def DGraph (k : ℕ) (F : Type*) [CommRing F] : SimpleGraph (Vertex k F) where
  Adj := AdjD k F
  symm := ⟨fun u v h => match u, v, h with
    | Sum.inl _, Sum.inr _, h => h
    | Sum.inr _, Sum.inl _, h => h⟩
  loopless := ⟨fun u h => match u, h with
    | Sum.inl _, h => h
    | Sum.inr _, h => h⟩

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

def PLAdjOrig (k : ℕ) (F : Type*) [CommRing F] (p l : Fin k → F) : Prop :=
  ∀ (j : Fin k), 1 ≤ j.val → p j + l j = rhsDOrig p l j

def AdjDOrig (k : ℕ) (F : Type*) [CommRing F] : Vertex k F → Vertex k F → Prop
  | Sum.inl p, Sum.inr l => PLAdjOrig k F p l
  | Sum.inr l, Sum.inl p => PLAdjOrig k F p l
  | _, _ => False

def DGraphOrig (k : ℕ) (F : Type*) [CommRing F] : SimpleGraph (Vertex k F) where
  Adj := AdjDOrig k F
  symm := ⟨fun u v h => match u, v, h with
    | Sum.inl _, Sum.inr _, h => h
    | Sum.inr _, Sum.inl _, h => h⟩
  loopless := ⟨fun u h => match u, h with
    | Sum.inl _, h => h
    | Sum.inr _, h => h⟩

def HasCycleOfLen {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (hm : 3 ≤ m) (v : Fin m → V), Function.Injective v ∧
    ∀ i : Fin m, G.Adj (v i) (v ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hm)⟩)

def GirthAtMost {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ r, 3 ≤ r ∧ r ≤ m ∧ HasCycleOfLen G r

def GirthAtLeast {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ r, 3 ≤ r → r < m → ¬ HasCycleOfLen G r

def HasExactGirth {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  GirthAtLeast G m ∧ HasCycleOfLen G m

def Admissible {F : Type*} [Field F] (c : F) : Prop :=
  c ≠ 0 ∧ c ≠ 1 ∧ c + 1 ≠ 0 ∧ c ^ 2 + 2 * c - 1 ≠ 0

/-! ### Definitional bridges to `LazebnikUstimenko` -/

private lemma DGraph_eq (k : ℕ) (F : Type*) [CommRing F] :
    DGraph k F = LazebnikUstimenko.DGraph k F := by
  ext u v
  cases u <;> cases v <;> rfl

private lemma DGraphOrig_eq (k : ℕ) (F : Type*) [CommRing F] :
    DGraphOrig k F = LazebnikUstimenko.DGraphOrig k F := by
  ext u v
  cases u <;> cases v <;> rfl

/-! ### Principal theorems matching `Challenge.lean` -/

theorem D9_D10_exact_girth_14_all_q_ge_4 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraph 9 F) 14 ∧ HasExactGirth (DGraph 10 F) 14 := by
  rw [DGraph_eq, DGraph_eq]
  exact LazebnikUstimenko.D9_D10_exact_girth_14_all_q_ge_4 F hcard

theorem D9_D10_orig_exact_girth_14_all_q_ge_4 (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    HasExactGirth (DGraphOrig 9 F) 14 ∧ HasExactGirth (DGraphOrig 10 F) 14 := by
  rw [DGraphOrig_eq, DGraphOrig_eq]
  exact LazebnikUstimenko.D9_D10_orig_exact_girth_14_all_q_ge_4 F hcard

theorem D9_D10_exact_girth_14_galoisField (p n : ℕ) [Fact p.Prime]
    (hn : n ≠ 0) (hq : 4 ≤ p ^ n) :
    HasExactGirth (DGraph 9 (GaloisField p n)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField p n)) 14 := by
  rw [DGraph_eq, DGraph_eq]
  exact LazebnikUstimenko.D9_D10_exact_girth_14_galoisField p n hn hq

theorem DS28_table7_blank_cells_27_32 :
    HasExactGirth (DGraph 9 (GaloisField 3 3)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField 3 3)) 14 ∧
    HasExactGirth (DGraph 9 (GaloisField 2 5)) 14 ∧
    HasExactGirth (DGraph 10 (GaloisField 2 5)) 14 := by
  rw [DGraph_eq, DGraph_eq, DGraph_eq, DGraph_eq]
  exact LazebnikUstimenko.DS28_table7_blank_cells_27_32

theorem card_admissible_ge_two_of_card_ge_four (F : Type*) [Field F] [Fintype F]
    (hcard : 4 ≤ Fintype.card F) :
    2 ≤ Nat.card {c : F // Admissible c} := by
  exact LazebnikUstimenko.card_admissible_ge_two_of_card_ge_four F hcard

theorem D2_exact_girth_law {s k : ℕ} (hs : 3 ≤ s) (hk2 : 2 ≤ k)
    (hlo : 2 ^ (s - 1) - 4 < k) (hhi : k ≤ 2 ^ s - 4) :
    HasExactGirth (DGraph k (ZMod 2)) (2 ^ s) := by
  rw [DGraph_eq]
  exact LazebnikUstimenko.D2_exact_girth_law hs hk2 hlo hhi

theorem D2_exact_girth_orig_law {s k : ℕ} (hs : 3 ≤ s) (hk2 : 2 ≤ k)
    (hlo : 2 ^ (s - 1) - 4 < k) (hhi : k ≤ 2 ^ s - 4) :
    HasExactGirth (DGraphOrig k (ZMod 2)) (2 ^ s) := by
  rw [DGraphOrig_eq]
  exact LazebnikUstimenko.D2_exact_girth_orig_law hs hk2 hlo hhi

theorem D2_girth_gt_16_of_ge_13 {k : ℕ} (hk : 13 ≤ k) :
    GirthAtLeast (DGraph k (ZMod 2)) 32 ∧ ¬ HasCycleOfLen (DGraph k (ZMod 2)) 16 := by
  rw [DGraph_eq]
  exact LazebnikUstimenko.D2_girth_gt_16_of_ge_13 hk

theorem D3_exact_girths_highlights :
    HasExactGirth (DGraph 15 (ZMod 3)) 20 ∧ HasExactGirth (DGraph 16 (ZMod 3)) 20 ∧
    HasExactGirth (DGraph 47 (ZMod 3)) 52 ∧ HasExactGirth (DGraph 48 (ZMod 3)) 52 ∧
    HasExactGirth (DGraph 55 (ZMod 3)) 60 ∧ HasExactGirth (DGraph 56 (ZMod 3)) 60 ∧
    HasExactGirth (DGraph 79 (ZMod 3)) 84 ∧ HasExactGirth (DGraph 80 (ZMod 3)) 84 ∧
    HasExactGirth (DGraph 99 (ZMod 3)) 104 ∧
    HasExactGirth (DGraph 103 (ZMod 3)) 108 ∧ HasExactGirth (DGraph 104 (ZMod 3)) 108 := by
  rw [DGraph_eq, DGraph_eq, DGraph_eq, DGraph_eq, DGraph_eq, DGraph_eq,
      DGraph_eq, DGraph_eq, DGraph_eq, DGraph_eq, DGraph_eq]
  exact ⟨LazebnikUstimenko.D3_k15_k16_exact_20.1,
         LazebnikUstimenko.D3_k15_k16_exact_20.2,
         LazebnikUstimenko.D3_k47_k48_exact_52.1,
         LazebnikUstimenko.D3_k47_k48_exact_52.2,
         LazebnikUstimenko.D3_k55_k56_exact_60.1,
         LazebnikUstimenko.D3_k55_k56_exact_60.2,
         LazebnikUstimenko.D3_k79_k80_exact_84.1,
         LazebnikUstimenko.D3_k79_k80_exact_84.2,
         LazebnikUstimenko.D3_k99_exact_104,
         LazebnikUstimenko.D3_k103_k104_exact_108.1,
         LazebnikUstimenko.D3_k103_k104_exact_108.2⟩

theorem D3_k52_bounds_56_60 :
    GirthAtLeast (DGraph 52 (ZMod 3)) 56 ∧ GirthAtMost (DGraph 52 (ZMod 3)) 60 := by
  rw [DGraph_eq]
  exact LazebnikUstimenko.D3_k52_bounds_56_60

end LazebnikUstimenkoChallenge
