module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Lazebnik–Ustimenko Graphs `D(k, F)`: Faithful Definitions, Exact Cycles, and Projections

This file defines the Lazebnik–Ustimenko algebraically defined bipartite graphs `D(k, F)` over
an arbitrary commutative ring `F` (following the DS28 Section 6.1 working representation),
proves the graph isomorphism with the original DS28 minus-sign representation (DS28 Prop. 38),
defines exact simple cycles and exact girth on any `SimpleGraph`, establishes the unique-neighbor
property by first coordinate, proves the general closed non-backtracking walk reduction to simple
cycles, and establishes girth monotonicity under the covering projections `D(k + 1, F) → D(k, F)`.
-/

@[expose] public section

namespace LazebnikUstimenko

/-- Vertices of `D(k, F)`: `Sum.inl p` is a point `(p₁, ..., pₖ)` and `Sum.inr l` is a line
`[l₁, ..., lₖ]` (0-indexed via `Fin k`). -/
abbrev Vertex (k : ℕ) (F : Type*) := (Fin k → F) ⊕ (Fin k → F)

/-- Right-hand side `fᵢ(p, l)` of the DS28 Section 6.1 working equations for `D(k, F)` at 0-based
coordinate `j` (`i = j + 1 ≥ 2`):
* `j = 1` (`i = 2`): `p₁ l₁`
* `j = 2` (`i = 3`): `p₁ l₂`
* `j ≥ 3`, `(j + 1) % 4 ∈ {0, 1}`: `pᵢ₋₂ l₁`
* `j ≥ 3`, `(j + 1) % 4 ∈ {2, 3}`: `p₁ lᵢ₋₂`. -/
def rhsD {k : ℕ} {F : Type*} [CommRing F] (p l : Fin k → F) (j : Fin k) : F :=
  if h0 : 0 < k then
    if h1 : j.val = 1 then
      p ⟨0, h0⟩ * l ⟨0, h0⟩
    else if h2 : j.val = 2 then
      p ⟨0, h0⟩ * l ⟨1, by omega⟩
    else if h3 : 3 ≤ j.val then
      if (j.val + 1) % 4 = 0 ∨ (j.val + 1) % 4 = 1 then
        p ⟨j.val - 2, by omega⟩ * l ⟨0, h0⟩
      else
        p ⟨0, h0⟩ * l ⟨j.val - 2, by omega⟩
    else
      0
  else
    0

/-- Point-line adjacency in `D(k, F)`: for every 0-based `j ≥ 1` (`i = j + 1 ∈ {2, ..., k}`),
`pⱼ + lⱼ = rhsD p l j`. -/
def PLAdj (k : ℕ) (F : Type*) [CommRing F] (p l : Fin k → F) : Prop :=
  ∀ (j : Fin k), 1 ≤ j.val → p j + l j = rhsD p l j

/-- Bipartite adjacency relation of `D(k, F)` on `Vertex k F`. -/
def AdjD (k : ℕ) (F : Type*) [CommRing F] : Vertex k F → Vertex k F → Prop
  | Sum.inl p, Sum.inr l => PLAdj k F p l
  | Sum.inr l, Sum.inl p => PLAdj k F p l
  | _, _ => False

/-- The Lazebnik–Ustimenko bipartite graph `D(k, F)` as a `SimpleGraph`. -/
def DGraph (k : ℕ) (F : Type*) [CommRing F] : SimpleGraph (Vertex k F) where
  Adj := AdjD k F
  symm := ⟨by rintro (p | l) (p' | l') h <;> exact h⟩
  loopless := ⟨by rintro (p | l) h <;> exact h⟩

/-! ### Original DS28 Minus-Sign Model and Graph Isomorphism (DS28 Prop. 38) -/

/-- Original DS28 Section 6 equations with minus signs on `i ≡ 0, 1 (mod 4)` (`i ≥ 4`). -/
def rhsDOrig {k : ℕ} {F : Type*} [CommRing F] (p l : Fin k → F) (j : Fin k) : F :=
  if h0 : 0 < k then
    if h1 : j.val = 1 then
      p ⟨0, h0⟩ * l ⟨0, h0⟩
    else if h2 : j.val = 2 then
      p ⟨0, h0⟩ * l ⟨1, by omega⟩
    else if h3 : 3 ≤ j.val then
      if (j.val + 1) % 4 = 0 ∨ (j.val + 1) % 4 = 1 then
        -(p ⟨j.val - 2, by omega⟩ * l ⟨0, h0⟩)
      else
        p ⟨0, h0⟩ * l ⟨j.val - 2, by omega⟩
    else
      0
  else
    0

/-- Point-line adjacency in the original minus-sign representation of `D(k, F)`. -/
def PLAdjOrig (k : ℕ) (F : Type*) [CommRing F] (p l : Fin k → F) : Prop :=
  ∀ (j : Fin k), 1 ≤ j.val → p j + l j = rhsDOrig p l j

/-- Bipartite adjacency relation of the original minus-sign representation of `D(k, F)`. -/
def AdjDOrig (k : ℕ) (F : Type*) [CommRing F] : Vertex k F → Vertex k F → Prop
  | Sum.inl p, Sum.inr l => PLAdjOrig k F p l
  | Sum.inr l, Sum.inl p => PLAdjOrig k F p l
  | _, _ => False

/-- The original minus-sign Lazebnik–Ustimenko graph as a `SimpleGraph`. -/
def DGraphOrig (k : ℕ) (F : Type*) [CommRing F] : SimpleGraph (Vertex k F) where
  Adj := AdjDOrig k F
  symm := ⟨by rintro (p | l) (p' | l') h <;> exact h⟩
  loopless := ⟨by rintro (p | l) h <;> exact h⟩

/-- Sign factor `(-1) ^ ((j + 1) / 4)` realizing DS28 Proposition 38 between the working and
original minus-sign representations. -/
def signFactor (F : Type*) [CommRing F] (j : ℕ) : F :=
  (-1 : F) ^ ((j + 1) / 4)

lemma signFactor_sq (F : Type*) [CommRing F] (j : ℕ) :
    signFactor F j * signFactor F j = 1 := by
  unfold signFactor
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

lemma signFactor_zero (F : Type*) [CommRing F] : signFactor F 0 = 1 := by
  simp [signFactor]

lemma signFactor_one (F : Type*) [CommRing F] : signFactor F 1 = 1 := by
  simp [signFactor]

lemma signFactor_two (F : Type*) [CommRing F] : signFactor F 2 = 1 := by
  simp [signFactor]

lemma signFactor_step_neg (F : Type*) [CommRing F] {j : ℕ}
    (h3 : 3 ≤ j) (hm : (j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1) :
    signFactor F j = -signFactor F (j - 2) := by
  unfold signFactor
  have hdiv : (j + 1) / 4 = (j - 2 + 1) / 4 + 1 := by omega
  rw [hdiv, pow_succ]
  ring

lemma signFactor_step_pos (F : Type*) [CommRing F] {j : ℕ}
    (h3 : 3 ≤ j) (hm : ¬ ((j + 1) % 4 = 0 ∨ (j + 1) % 4 = 1)) :
    signFactor F j = signFactor F (j - 2) := by
  unfold signFactor
  have hdiv : (j + 1) / 4 = (j - 2 + 1) / 4 := by omega
  rw [hdiv]

/-- Coordinatewise sign flip `v ↦ (j ↦ signFactor F j * v j)`. -/
def signFlipVec {k : ℕ} {F : Type*} [CommRing F] (v : Fin k → F) : Fin k → F :=
  fun j => signFactor F j.val * v j

lemma signFlipVec_involutive {k : ℕ} {F : Type*} [CommRing F] (v : Fin k → F) :
    signFlipVec (signFlipVec v) = v := by
  funext j
  simp only [signFlipVec, ← mul_assoc, signFactor_sq, one_mul]

lemma plAdj_iff_plAdjOrig_signFlip {k : ℕ} {F : Type*} [CommRing F] (p l : Fin k → F) :
    PLAdj k F p l ↔ PLAdjOrig k F (signFlipVec p) (signFlipVec l) := by
  constructor
  · intro h j hj
    have h0 : 0 < k := by omega
    have heq := h j hj
    simp only [signFlipVec, rhsDOrig, h0, ↓reduceDIte]
    simp only [rhsD, h0, ↓reduceDIte] at heq
    by_cases h1 : j.val = 1
    · simp only [h1, ↓reduceDIte, signFactor_zero, signFactor_one, one_mul] at heq ⊢
      exact heq
    · by_cases h2 : j.val = 2
      · simp only [h2, ↓reduceDIte, signFactor_zero, signFactor_one,
          signFactor_two, one_mul] at heq ⊢
        exact heq
      · have h3 : 3 ≤ j.val := by omega
        simp only [h1, h2, h3, ↓reduceDIte] at heq ⊢
        by_cases hm : (j.val + 1) % 4 = 0 ∨ (j.val + 1) % 4 = 1
        · simp only [hm, ite_true] at heq ⊢
          rw [signFactor_zero, one_mul, signFactor_step_neg F h3 hm]
          linear_combination (-signFactor F (j.val - 2)) * heq
        · simp only [hm, ite_false] at heq ⊢
          rw [signFactor_zero, one_mul, signFactor_step_pos F h3 hm]
          linear_combination (signFactor F (j.val - 2)) * heq
  · intro h j hj
    have h0 : 0 < k := by omega
    have heq := h j hj
    simp only [signFlipVec, rhsDOrig, h0, ↓reduceDIte] at heq
    simp only [rhsD, h0, ↓reduceDIte]
    by_cases h1 : j.val = 1
    · simp only [h1, ↓reduceDIte, signFactor_zero, signFactor_one, one_mul] at heq ⊢
      exact heq
    · by_cases h2 : j.val = 2
      · simp only [h2, ↓reduceDIte, signFactor_zero, signFactor_one,
          signFactor_two, one_mul] at heq ⊢
        exact heq
      · have h3 : 3 ≤ j.val := by omega
        simp only [h1, h2, h3, ↓reduceDIte] at heq ⊢
        by_cases hm : (j.val + 1) % 4 = 0 ∨ (j.val + 1) % 4 = 1
        · simp only [hm, ite_true] at heq ⊢
          rw [signFactor_zero, one_mul, signFactor_step_neg F h3 hm] at heq
          have hsq := signFactor_sq F (j.val - 2)
          linear_combination (-signFactor F (j.val - 2)) * heq -
            (p j + l j - p ⟨j.val - 2, by omega⟩ * l ⟨0, h0⟩) * hsq
        · simp only [hm, ite_false] at heq ⊢
          rw [signFactor_zero, one_mul, signFactor_step_pos F h3 hm] at heq
          have hsq := signFactor_sq F (j.val - 2)
          linear_combination (signFactor F (j.val - 2)) * heq -
            (p j + l j - p ⟨0, h0⟩ * l ⟨j.val - 2, by omega⟩) * hsq

/-- DS28 Proposition 38: the working representation `DGraph k F` is graph-isomorphic to the
original minus-sign representation `DGraphOrig k F` over every commutative ring `F`. -/
def DGraph_iso_DGraphOrig (k : ℕ) (F : Type*) [CommRing F] :
    DGraph k F ≃g DGraphOrig k F where
  toFun := Sum.map signFlipVec signFlipVec
  invFun := Sum.map signFlipVec signFlipVec
  left_inv := by rintro (p | l) <;> simp [signFlipVec_involutive]
  right_inv := by rintro (p | l) <;> simp [signFlipVec_involutive]
  map_rel_iff' := by
    rintro (p | l) (p' | l')
    · simp [DGraph, DGraphOrig, AdjD, AdjDOrig]
    · simp [DGraph, DGraphOrig, AdjD, AdjDOrig, plAdj_iff_plAdjOrig_signFlip]
    · simp [DGraph, DGraphOrig, AdjD, AdjDOrig, plAdj_iff_plAdjOrig_signFlip]
    · simp [DGraph, DGraphOrig, AdjD, AdjDOrig]

/-! ### Exact Simple Cycles, Closed Non-Backtracking Walks, and Girth -/

/-- `HasCycleOfLen G m` asserts that `G` contains a simple cycle of exact length `m ≥ 3`:
an injective sequence of `m` vertices with cyclic adjacency. -/
def HasCycleOfLen {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (hm : 3 ≤ m) (v : Fin m → V), Function.Injective v ∧
    ∀ i : Fin m, G.Adj (v i) (v ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)

/-- `GirthAtMost G m` asserts that `G` contains a simple cycle of length `r` with `3 ≤ r ≤ m`. -/
def GirthAtMost {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ r, 3 ≤ r ∧ r ≤ m ∧ HasCycleOfLen G r

/-- `GirthAtLeast G m` asserts that `G` has no simple cycle of length strictly less than `m`. -/
def GirthAtLeast {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ r, 3 ≤ r → r < m → ¬ HasCycleOfLen G r

/-- `HasExactGirth G m` asserts that the girth of `G` is exactly `m`: `G` has a simple cycle of
length `m` and no shorter simple cycle. -/
def HasExactGirth {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  GirthAtLeast G m ∧ HasCycleOfLen G m

/-- A closed non-backtracking walk of length `m ≥ 3` in `G`. -/
def ClosedNBWalk {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (hm : 3 ≤ m) (v : Fin m → V),
    (∀ i : Fin m, G.Adj (v i) (v ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) ∧
    (∀ i : Fin m, v i ≠ v ⟨(i.val + 2) % m, Nat.mod_lt _ (by omega)⟩)

lemma HasExactGirth.girthAtMost {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (h : HasExactGirth G m) : GirthAtMost G m :=
  ⟨m, h.2.1, le_rfl, h.2⟩

lemma HasExactGirth.unique {V : Type*} {G : SimpleGraph V} {m₁ m₂ : ℕ}
    (h1 : HasExactGirth G m₁) (h2 : HasExactGirth G m₂) : m₁ = m₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h2.1 m₁ h1.2.1 hlt h1.2
  · exact h1.1 m₂ h2.2.1 hgt h2.2

lemma HasCycleOfLen.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {m : ℕ} (h : HasCycleOfLen G m) : HasCycleOfLen H m := by
  rcases h with ⟨hm, v, hinj, hadj⟩
  refine ⟨hm, e ∘ v, e.injective.comp hinj, fun i => ?_⟩
  exact (e.map_rel_iff).2 (hadj i)

lemma GirthAtLeast.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {m : ℕ} (h : GirthAtLeast G m) : GirthAtLeast H m := by
  intro r hr hlt hc
  exact h r hr hlt (hc.of_iso e.symm)

lemma GirthAtMost.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {m : ℕ} (h : GirthAtMost G m) : GirthAtMost H m := by
  rcases h with ⟨r, hr, hle, hc⟩
  exact ⟨r, hr, hle, hc.of_iso e⟩

lemma HasExactGirth.of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {m : ℕ} (h : HasExactGirth G m) : HasExactGirth H m :=
  ⟨h.1.of_iso e, h.2.of_iso e⟩

/-- Every cycle in a bipartite graph (whose edges only cross `Sum.inl ↔ Sum.inr`) has even length. -/
lemma even_cycle_len_of_bipartite {A B : Type*} (G : SimpleGraph (A ⊕ B))
    (hbip : ∀ u v, G.Adj u v → (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft))
    {m : ℕ} (hc : HasCycleOfLen G m) : Even m := by
  rcases hc with ⟨hm, v, _, hadj⟩
  have hstep : ∀ t : ℕ, t ≤ m →
      (v ⟨t % m, Nat.mod_lt _ (by omega)⟩).isLeft =
        if Even t then (v ⟨0, by omega⟩).isLeft else !(v ⟨0, by omega⟩).isLeft := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have hprev := ih (by omega)
      have hi : G.Adj (v ⟨t % m, Nat.mod_lt _ (by omega)⟩)
          (v ⟨((t % m) + 1) % m, Nat.mod_lt _ (by omega)⟩) := hadj ⟨t % m, Nat.mod_lt _ (by omega)⟩
      have hfin : (⟨((t % m) + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) =
          ⟨(t + 1) % m, Nat.mod_lt _ (by omega)⟩ :=
        Fin.ext (by dsimp only; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod])
      have hflip : (v ⟨(t + 1) % m, Nat.mod_lt _ (by omega)⟩).isLeft =
          !(v ⟨t % m, Nat.mod_lt _ (by omega)⟩).isLeft := by
        have hlr := hbip _ _ hi
        rw [hfin] at hlr
        cases hu : v ⟨t % m, Nat.mod_lt _ (by omega)⟩ <;>
        cases hv : v ⟨(t + 1) % m, Nat.mod_lt _ (by omega)⟩ <;> simp_all
      rw [hflip, hprev]
      by_cases he : Even t
      · have ho : ¬ Even (t + 1) := by
          rcases he with ⟨k, rfl⟩
          intro ⟨k', hk'⟩; omega
        simp [he, ho]
      · have he' : Even (t + 1) := by
          have : Odd t := Nat.not_even_iff_odd.1 he
          rcases this with ⟨k, rfl⟩
          exact ⟨k + 1, by omega⟩
        simp [he, he']
  have hm0 := hstep m le_rfl
  simp only [Nat.mod_self] at hm0
  by_contra hodd
  simp only [hodd, ite_false] at hm0
  cases h0 : (v ⟨0, by omega⟩).isLeft <;> simp [h0] at hm0

/-- Every cycle in `DGraph k F` has even length. -/
lemma even_cycle_len_D {k : ℕ} {F : Type*} [CommRing F] {m : ℕ}
    (hc : HasCycleOfLen (DGraph k F) m) : Even m :=
  even_cycle_len_of_bipartite (DGraph k F) (by
    rintro (p | l) (p' | l') h
    · exact False.elim h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact False.elim h) hc

/-- Every closed non-backtracking walk of length `m ≥ 3` in a simple graph contains a simple
cycle of length `r` with `3 ≤ r ≤ m`. -/
theorem exists_cycle_le_of_closed_nb_walk {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hw : ClosedNBWalk G m) : GirthAtMost G m := by
  classical
  rcases hw with ⟨hm, v, hadj, hnb⟩
  let P : ℕ → Prop := fun d =>
    1 ≤ d ∧ d ≤ m ∧ ∃ a : Fin m, v a = v ⟨(a.val + d) % m, Nat.mod_lt _ (by omega)⟩
  have hex : ∃ d, P d := ⟨m, by omega, le_rfl, ⟨0, by omega⟩, by simp⟩
  let d := Nat.find hex
  have hd : P d := Nat.find_spec hex
  have hmin : ∀ d', d' < d → ¬ P d' := fun d' hlt => Nat.find_min hex hlt
  rcases hd with ⟨hd1, hdm, a, ha⟩
  have hd_ne1 : d ≠ 1 := by
    intro h1
    have hfin : (⟨(a.val + d) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) =
        ⟨(a.val + 1) % m, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by rw [h1])
    rw [hfin] at ha
    have hloop := hadj a
    rw [← ha] at hloop
    exact G.loopless.irrefl (v a) hloop
  have hd_ne2 : d ≠ 2 := by
    intro h2
    have hfin : (⟨(a.val + d) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) =
        ⟨(a.val + 2) % m, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by rw [h2])
    rw [hfin] at ha
    exact hnb a ha
  have hd3 : 3 ≤ d := by omega
  refine ⟨d, hd3, hdm, hd3, fun t => v ⟨(a.val + t.val) % m, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
  · intro t₁ t₂ heq
    have hcontra : ∀ (u₁ u₂ : Fin d), u₁.val < u₂.val →
        v ⟨(a.val + u₁.val) % m, Nat.mod_lt _ (by omega)⟩ =
        v ⟨(a.val + u₂.val) % m, Nat.mod_lt _ (by omega)⟩ → False := by
      intro u₁ u₂ hlt hveq
      have hdiff_pos : 1 ≤ u₂.val - u₁.val := by omega
      have hdiff_lt : u₂.val - u₁.val < d := by omega
      have hdiff_le : u₂.val - u₁.val ≤ m := by omega
      have hmod_eq : (((a.val + u₁.val) % m) + (u₂.val - u₁.val)) % m = (a.val + u₂.val) % m := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      have hp : P (u₂.val - u₁.val) := by
        refine ⟨hdiff_pos, hdiff_le, ⟨(a.val + u₁.val) % m, Nat.mod_lt _ (by omega)⟩, ?_⟩
        simpa only [hmod_eq] using hveq
      exact hmin _ hdiff_lt hp
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hcontra t₁ t₂ hlt heq
    · exact hcontra t₂ t₁ hlt heq.symm
  · intro t
    by_cases hlast : t.val + 1 < d
    · have hmod_t : (t.val + 1) % d = t.val + 1 := Nat.mod_eq_of_lt hlast
      have hmod_m : (((a.val + t.val) % m) + 1) % m = (a.val + (t.val + 1)) % m := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      have hstep := hadj ⟨(a.val + t.val) % m, Nat.mod_lt _ (by omega)⟩
      simpa only [hmod_t, hmod_m] using hstep
    · have ht_eq : t.val + 1 = d := by omega
      have hmod_t : (t.val + 1) % d = 0 := by rw [ht_eq, Nat.mod_self]
      have hmod_m : (((a.val + t.val) % m) + 1) % m = (a.val + d) % m := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      have hstep := hadj ⟨(a.val + t.val) % m, Nat.mod_lt _ (by omega)⟩
      simp only [hmod_t, add_zero, Nat.mod_eq_of_lt a.isLt]
      rw [ha]
      simpa only [hmod_m] using hstep

/-- If `G` has girth at least `m` and admits a closed non-backtracking walk of length `m`, then
`G` has a simple cycle of length `m` (hence exact girth `m`). -/
theorem hasExactGirth_of_closed_nb_walk_of_girthAtLeast {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hge : GirthAtLeast G m) (hw : ClosedNBWalk G m) : HasExactGirth G m := by
  rcases exists_cycle_le_of_closed_nb_walk hw with ⟨r, hr3, hrm, hcr⟩
  have hreq : r = m := by
    by_contra hne
    exact hge r hr3 (lt_of_le_of_ne hrm hne) hcr
  subst hreq
  exact ⟨hge, hcr⟩

/-! ### Unique Neighbor by First Coordinate in `D(k, F)` -/

/-- Recursive coordinate solver for the unique line with first coordinate `x` adjacent to `p`. -/
def stepLineCoord {k : ℕ} {F : Type*} [CommRing F] (p : Fin k → F) (x : F) :
    ∀ j : ℕ, j < k → F
  | 0, _ => x
  | 1, hk => p ⟨0, by omega⟩ * x - p ⟨1, hk⟩
  | 2, hk => p ⟨0, by omega⟩ * stepLineCoord p x 1 (by omega) - p ⟨2, hk⟩
  | j + 3, hk =>
    if ((j + 3) + 1) % 4 = 0 ∨ ((j + 3) + 1) % 4 = 1 then
      p ⟨j + 1, by omega⟩ * x - p ⟨j + 3, hk⟩
    else
      p ⟨0, by omega⟩ * stepLineCoord p x (j + 1) (by omega) - p ⟨j + 3, hk⟩

/-- The unique line with first coordinate `x` adjacent to point `p` in `D(k, F)`. -/
def stepLine {k : ℕ} {F : Type*} [CommRing F] (p : Fin k → F) (x : F) : Fin k → F :=
  fun j => stepLineCoord p x j.val j.isLt

/-- Recursive coordinate solver for the unique point with first coordinate `x` adjacent to `l`. -/
def stepPointCoord {k : ℕ} {F : Type*} [CommRing F] (l : Fin k → F) (x : F) :
    ∀ j : ℕ, j < k → F
  | 0, _ => x
  | 1, hk => x * l ⟨0, by omega⟩ - l ⟨1, hk⟩
  | 2, hk => x * l ⟨1, by omega⟩ - l ⟨2, hk⟩
  | j + 3, hk =>
    if ((j + 3) + 1) % 4 = 0 ∨ ((j + 3) + 1) % 4 = 1 then
      stepPointCoord l x (j + 1) (by omega) * l ⟨0, by omega⟩ - l ⟨j + 3, hk⟩
    else
      x * l ⟨j + 1, by omega⟩ - l ⟨j + 3, hk⟩

/-- The unique point with first coordinate `x` adjacent to line `l` in `D(k, F)`. -/
def stepPoint {k : ℕ} {F : Type*} [CommRing F] (l : Fin k → F) (x : F) : Fin k → F :=
  fun j => stepPointCoord l x j.val j.isLt

lemma stepLine_zero {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k) (p : Fin k → F) (x : F) :
    stepLine p x ⟨0, hk⟩ = x := rfl

lemma stepPoint_zero {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k) (l : Fin k → F) (x : F) :
    stepPoint l x ⟨0, hk⟩ = x := rfl

lemma stepLine_adj {k : ℕ} {F : Type*} [CommRing F] (p : Fin k → F) (x : F) :
    PLAdj k F p (stepLine p x) := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  have h0 : 0 < k := by omega
  match j with
  | 0 => omega
  | 1 =>
    simp only [stepLine, stepLineCoord, rhsD, h0, ↓reduceDIte]
    ring
  | 2 =>
    simp only [stepLine, stepLineCoord, rhsD, h0, ↓reduceDIte]
    norm_num
  | j + 3 =>
    simp only [stepLine, stepLineCoord, rhsD, h0, ↓reduceDIte]
    have hne1 : j + 3 ≠ 1 := by omega
    have hne2 : j + 3 ≠ 2 := by omega
    have hge3 : 3 ≤ j + 3 := by omega
    have hsub : j + 3 - 2 = j + 1 := by omega
    simp only [hne1, hne2, hge3, ↓reduceDIte, hsub]
    split_ifs <;> ring

lemma stepPoint_adj {k : ℕ} {F : Type*} [CommRing F] (l : Fin k → F) (x : F) :
    PLAdj k F (stepPoint l x) l := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  have h0 : 0 < k := by omega
  match j with
  | 0 => omega
  | 1 =>
    simp only [stepPoint, stepPointCoord, rhsD, h0, ↓reduceDIte]
    ring
  | 2 =>
    simp only [stepPoint, stepPointCoord, rhsD, h0, ↓reduceDIte]
    norm_num
  | j + 3 =>
    simp only [stepPoint, stepPointCoord, rhsD, h0, ↓reduceDIte]
    have hne1 : j + 3 ≠ 1 := by omega
    have hne2 : j + 3 ≠ 2 := by omega
    have hge3 : 3 ≤ j + 3 := by omega
    have hsub : j + 3 - 2 = j + 1 := by omega
    simp only [hne1, hne2, hge3, ↓reduceDIte, hsub]
    split_ifs <;> ring

/-- Uniqueness of an adjacent line given its first coordinate. -/
lemma unique_line_of_firstCoord {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k)
    {p l₁ l₂ : Fin k → F}
    (h1 : PLAdj k F p l₁) (h2 : PLAdj k F p l₂)
    (h0 : l₁ ⟨0, hk⟩ = l₂ ⟨0, hk⟩) : l₁ = l₂ := by
  funext ⟨j, hjlt⟩
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · exact h0
    · have e1 := h1 ⟨j, hjlt⟩ hj1
      have e2 := h2 ⟨j, hjlt⟩ hj1
      have hrhs : rhsD p l₁ ⟨j, hjlt⟩ = rhsD p l₂ ⟨j, hjlt⟩ := by
        simp only [rhsD, hk, ↓reduceDIte]
        by_cases h1j : j = 1
        · simp only [h1j, ↓reduceDIte, h0]
        · by_cases h2j : j = 2
          · subst h2j
            simp only [↓reduceDIte, OfNat.ofNat_ne_one]
            rw [ih 1 (by omega) (by omega)]
          · have h3j : 3 ≤ j := by omega
            simp only [h1j, h2j, h3j, ↓reduceDIte]
            split_ifs
            · rw [h0]
            · rw [ih (j - 2) (by omega) (by omega)]
      rw [hrhs] at e1
      linear_combination e1 - e2

/-- Uniqueness of an adjacent point given its first coordinate. -/
lemma unique_point_of_firstCoord {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k)
    {p₁ p₂ l : Fin k → F}
    (h1 : PLAdj k F p₁ l) (h2 : PLAdj k F p₂ l)
    (h0 : p₁ ⟨0, hk⟩ = p₂ ⟨0, hk⟩) : p₁ = p₂ := by
  funext ⟨j, hjlt⟩
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · exact h0
    · have e1 := h1 ⟨j, hjlt⟩ hj1
      have e2 := h2 ⟨j, hjlt⟩ hj1
      have hrhs : rhsD p₁ l ⟨j, hjlt⟩ = rhsD p₂ l ⟨j, hjlt⟩ := by
        simp only [rhsD, hk, ↓reduceDIte]
        by_cases h1j : j = 1
        · simp only [h1j, ↓reduceDIte, h0]
        · by_cases h2j : j = 2
          · subst h2j
            simp only [↓reduceDIte, OfNat.ofNat_ne_one, h0]
          · have h3j : 3 ≤ j := by omega
            simp only [h1j, h2j, h3j, ↓reduceDIte]
            split_ifs
            · rw [ih (j - 2) (by omega) (by omega)]
            · rw [h0]
      rw [hrhs] at e1
      linear_combination e1 - e2

/-- First coordinate of a vertex in `D(k, F)` (for `0 < k`). -/
def firstCoord {k : ℕ} {F : Type*} (hk : 0 < k) : Vertex k F → F
  | Sum.inl p => p ⟨0, hk⟩
  | Sum.inr l => l ⟨0, hk⟩

/-- Two neighbors of a vertex in `D(k, F)` with the same first coordinate must be equal. -/
lemma unique_neighbor_of_firstCoord {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k)
    {u v₁ v₂ : Vertex k F}
    (h1 : (DGraph k F).Adj u v₁) (h2 : (DGraph k F).Adj u v₂)
    (hfc : firstCoord hk v₁ = firstCoord hk v₂) : v₁ = v₂ := by
  rcases u with p | l
  · rcases v₁ with p₁ | l₁
    · exact False.elim h1
    · rcases v₂ with p₂ | l₂
      · exact False.elim h2
      · exact congrArg Sum.inr (unique_line_of_firstCoord hk h1 h2 hfc)
  · rcases v₁ with p₁ | l₁
    · rcases v₂ with p₂ | l₂
      · exact congrArg Sum.inl (unique_point_of_firstCoord hk h1 h2 hfc)
      · exact False.elim h2
    · exact False.elim h1

/-! ### Covering Projections `D(k₂, F) → D(k₁, F)` and Girth Monotonicity -/

/-- Truncation map `Fin k₂ → F` to `Fin k₁ → F` for `k₁ ≤ k₂`. -/
def truncVec {k₁ k₂ : ℕ} {F : Type*} (hle : k₁ ≤ k₂) (v : Fin k₂ → F) : Fin k₁ → F :=
  fun j => v ⟨j.val, lt_of_lt_of_le j.isLt hle⟩

/-- Covering projection `D(k₂, F) → D(k₁, F)` for `k₁ ≤ k₂`. -/
def projD {k₁ k₂ : ℕ} {F : Type*} (hle : k₁ ≤ k₂) : Vertex k₂ F → Vertex k₁ F :=
  Sum.map (truncVec hle) (truncVec hle)

lemma projD_firstCoord {k₁ k₂ : ℕ} {F : Type*} (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂)
    (v : Vertex k₂ F) :
    firstCoord hk₁ (projD hle v) = firstCoord (lt_of_lt_of_le hk₁ hle) v := by
  rcases v with p | l <;> rfl

lemma truncVec_plAdj {k₁ k₂ : ℕ} {F : Type*} [CommRing F] (hle : k₁ ≤ k₂)
    {p l : Fin k₂ → F} (h : PLAdj k₂ F p l) :
    PLAdj k₁ F (truncVec hle p) (truncVec hle l) := by
  intro j hj1
  have h1 : 0 < k₁ := by omega
  have h2 : 0 < k₂ := by omega
  have heq := h ⟨j.val, lt_of_lt_of_le j.isLt hle⟩ hj1
  simp only [truncVec]
  simp only [rhsD, h1, h2, ↓reduceDIte] at heq ⊢
  exact heq

lemma projD_adj {k₁ k₂ : ℕ} {F : Type*} [CommRing F] (hle : k₁ ≤ k₂)
    {u v : Vertex k₂ F} (h : (DGraph k₂ F).Adj u v) :
    (DGraph k₁ F).Adj (projD hle u) (projD hle v) := by
  rcases u with p | l <;> rcases v with p' | l'
  · exact False.elim h
  · exact truncVec_plAdj hle h
  · exact truncVec_plAdj hle h
  · exact False.elim h

/-- Covering projection maps any simple cycle in `D(k₂, F)` to a closed non-backtracking walk of
the same length in `D(k₁, F)` (for `1 ≤ k₁ ≤ k₂`). -/
lemma closed_nb_walk_projD_of_cycle {k₁ k₂ : ℕ} {F : Type*} [CommRing F]
    (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂) {m : ℕ}
    (hc : HasCycleOfLen (DGraph k₂ F) m) : ClosedNBWalk (DGraph k₁ F) m := by
  rcases hc with ⟨hm, v, hinj, hadj⟩
  refine ⟨hm, fun i => projD hle (v i), fun i => projD_adj hle (hadj i), fun i heq => ?_⟩
  dsimp only at heq
  have hfc : firstCoord (lt_of_lt_of_le hk₁ hle) (v i) =
      firstCoord (lt_of_lt_of_le hk₁ hle) (v ⟨(i.val + 2) % m, Nat.mod_lt _ (by omega)⟩) := by
    rw [← projD_firstCoord hk₁ hle, ← projD_firstCoord hk₁ hle, heq]
  have h1 : (DGraph k₂ F).Adj (v ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩) (v i) :=
    (DGraph k₂ F).adj_symm (hadj i)
  have h2 : (DGraph k₂ F).Adj (v ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)
      (v ⟨(i.val + 2) % m, Nat.mod_lt _ (by omega)⟩) := by
    have hmod : (((i.val + 1) % m) + 1) % m = (i.val + 2) % m := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    simpa only [hmod] using hadj ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩
  have hv_eq := unique_neighbor_of_firstCoord (lt_of_lt_of_le hk₁ hle) h1 h2 hfc
  have hi_eq := hinj hv_eq
  have hval : i.val = (i.val + 2) % m := congrArg Fin.val hi_eq
  have hilt : i.val < m := i.isLt
  by_cases hlt2 : i.val + 2 < m
  · rw [Nat.mod_eq_of_lt hlt2] at hval; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega

/-- Girth monotonicity (upper bound): if `1 ≤ k₁ ≤ k₂`, then `girth D(k₁, F) ≤ girth D(k₂, F)`. -/
theorem girthAtMost_of_le {k₁ k₂ : ℕ} {F : Type*} [CommRing F]
    (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂) {m : ℕ}
    (h : GirthAtMost (DGraph k₂ F) m) : GirthAtMost (DGraph k₁ F) m := by
  rcases h with ⟨r, hr3, hrm, hcr⟩
  rcases exists_cycle_le_of_closed_nb_walk (closed_nb_walk_projD_of_cycle hk₁ hle hcr) with
    ⟨r', hr'3, hr'r, hcr'⟩
  exact ⟨r', hr'3, le_trans hr'r hrm, hcr'⟩

/-- Girth monotonicity (lower bound): if `1 ≤ k₁ ≤ k₂`, then `girth D(k₁, F) ≥ m` implies
`girth D(k₂, F) ≥ m`. -/
theorem girthAtLeast_of_le {k₁ k₂ : ℕ} {F : Type*} [CommRing F]
    (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂) {m : ℕ}
    (h : GirthAtLeast (DGraph k₁ F) m) : GirthAtLeast (DGraph k₂ F) m := by
  intro r hr3 hrm hcr
  rcases exists_cycle_le_of_closed_nb_walk (closed_nb_walk_projD_of_cycle hk₁ hle hcr) with
    ⟨r', hr'3, hr'r, hcr'⟩
  exact h r' hr'3 (lt_of_le_of_lt hr'r hrm) hcr'

/-- One-step girth monotonicity: `GirthAtMost (DGraph (k + 1) F) m → GirthAtMost (DGraph k F) m`. -/
theorem girthAtMost_mono_k {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k) {m : ℕ}
    (h : GirthAtMost (DGraph (k + 1) F) m) : GirthAtMost (DGraph k F) m :=
  girthAtMost_of_le hk (Nat.le_succ k) h

/-- One-step girth monotonicity: `GirthAtLeast (DGraph k F) m → GirthAtLeast (DGraph (k + 1) F) m`. -/
theorem girthAtLeast_mono_k {k : ℕ} {F : Type*} [CommRing F] (hk : 0 < k) {m : ℕ}
    (h : GirthAtLeast (DGraph k F) m) : GirthAtLeast (DGraph (k + 1) F) m :=
  girthAtLeast_of_le hk (Nat.le_succ k) h

end LazebnikUstimenko
