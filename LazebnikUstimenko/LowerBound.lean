module

public import LazebnikUstimenko.Defs
public import Mathlib.Algebra.Ring.Parity

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Unconditional Lazebnik–Ustimenko Lower Bound (`girth D(k, F) ≥ k + 5` odd / `k + 4` even)

This file gives a 100% unconditional, self-contained proof of Lazebnik–Ustimenko (1995) Theorem 45
(DS28 Section 6.3) over **every integral domain** `F` (`[CommRing F] [IsDomain F]`):
* `girth D(m, F) ≥ m + 5` for every odd `m ≥ 3`;
* `girth D(m, F) ≥ m + 4` for every even `m ≥ 2`.
-/

@[expose] public section

namespace LazebnikUstimenko

/-! ### Part 1: Ustimenko's Graph `A(n, F)` and Meet-in-the-Middle Lower Bound -/

/-- Point-line adjacency in Ustimenko's graph `A(n, F)` (DS28 Section 6.3):
at 0-based index `j ≥ 1` (`i = j + 1`):
* `Odd j` (`i` even): `p j + l j = p (j - 1) * l 0`
* `Even j` (`i` odd): `p j + l j = p 0 * l (j - 1)`. -/
def PLAdjA (n : ℕ) (F : Type*) [CommRing F] (p l : Fin n → F) : Prop :=
  ∀ (j : Fin n) (_hj : 1 ≤ j.val),
    p j + l j =
      if Odd j.val then
        p ⟨j.val - 1, by omega⟩ * l ⟨0, by omega⟩
      else
        p ⟨0, by omega⟩ * l ⟨j.val - 1, by omega⟩

/-- A line adjacent to the zero point in `A(n, F)` vanishes on all coordinates `j ≥ 1`. -/
lemma walkA_step1 {n : ℕ} {F : Type*} [CommRing F] {l : Fin n → F}
    (h : PLAdjA n F 0 l) : ∀ (j : Fin n), 1 ≤ j.val → l j = 0 := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  have heq := h ⟨j, hjlt⟩ hj1
  simp only [Pi.zero_apply, zero_add] at heq
  split_ifs at heq
  · simpa using heq
  · simpa using heq

/-- Core support & leading-term invariant for a non-backtracking walk starting from `0` in
`A(n, F)` over an integral domain `F`. -/
lemma walkA_invariant {n r : ℕ} {F : Type*} [CommRing F] [IsDomain F]
    (hn : 0 < n) (hrn : r ≤ n)
    (w : ℕ → Fin n → F)
    (h0 : w 0 = 0)
    (hadj : ∀ t, t < r →
      if Even t then PLAdjA n F (w t) (w (t + 1)) else PLAdjA n F (w (t + 1)) (w t))
    (hnb : ∀ t, t + 2 ≤ r → w (t + 2) ⟨0, hn⟩ ≠ w t ⟨0, hn⟩) :
    ∀ t (ht2 : 2 ≤ t) (htr : t ≤ r),
      w t ⟨t - 2, by omega⟩ ≠ 0 ∧
      w t ⟨t - 1, by omega⟩ = w t ⟨t - 2, by omega⟩ * w (t - 1) ⟨0, hn⟩ ∧
      (∀ j : Fin n, t ≤ j.val → w t j = 0) := by
  have hw1 : 1 ≤ r → ∀ j : Fin n, 1 ≤ j.val → w 1 j = 0 := by
    intro hr1
    have h01 := hadj 0 (by omega)
    simp only [Even.zero, ite_true, h0] at h01
    exact walkA_step1 h01
  intro t ht2 htr
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht1 : t = 1
    · subst ht1
      have h12 := hadj 1 (by omega)
      simp only [Nat.not_even_one, ite_false] at h12
      have hw1_zero : ∀ j : Fin n, 1 ≤ j.val → w 1 j = 0 := hw1 (by omega)
      refine ⟨?_, ?_, ?_⟩
      · have hnb0 := hnb 0 (by omega)
        simpa [h0] using hnb0
      · have heq := h12 ⟨1, by omega⟩ (by dsimp only; omega)
        simp only [odd_one, ite_true] at heq
        have hz := hw1_zero ⟨1, by omega⟩ (by dsimp only; omega)
        rw [hz, add_zero] at heq
        exact heq
      · intro ⟨j, hjlt⟩ hj2
        dsimp only at hj2
        induction j using Nat.strong_induction_on with
        | h j ihj =>
          have heq := h12 ⟨j, hjlt⟩ (by dsimp only; omega)
          have hzj := hw1_zero ⟨j, hjlt⟩ (by dsimp only; omega)
          rw [hzj, add_zero] at heq
          split_ifs at heq with ho
          · have hprev := ihj (j - 1) (by omega) (by omega) (by
              rcases ho with ⟨m, hm⟩; dsimp only at hm; omega)
            rw [hprev, zero_mul] at heq
            exact heq
          · have hprev := hw1_zero ⟨j - 1, by omega⟩ (by dsimp only; omega)
            rw [hprev, mul_zero] at heq
            exact heq
    · have ht2' : 2 ≤ t := by omega
      rcases ih ht2' (by omega) with ⟨hne, hlead, hvan⟩
      have hstep := hadj t (by omega)
      have hnb_step : w (t + 1) ⟨0, hn⟩ ≠ w (t - 1) ⟨0, hn⟩ := by
        have h := hnb (t - 1) (by omega)
        have heq1 : t - 1 + 2 = t + 1 := by omega
        simpa only [heq1] using h
      by_cases he : Even t
      · simp only [he, ite_true] at hstep
        have ho_tm1 : Odd (t - 1) := by
          rcases he with ⟨m, rfl⟩
          exact ⟨m - 1, by omega⟩
        have hne_next : w (t + 1) ⟨t - 1, by omega⟩ ≠ 0 := by
          have heq := hstep ⟨t - 1, by omega⟩ (by dsimp only; omega)
          simp only [ho_tm1, ite_true] at heq
          have hsub : t - 1 - 1 = t - 2 := by omega
          have hval : w (t + 1) ⟨t - 1, by omega⟩ =
              w t ⟨t - 2, by omega⟩ * (w (t + 1) ⟨0, hn⟩ - w (t - 1) ⟨0, hn⟩) := by
            have heq' : w t ⟨t - 1, by omega⟩ + w (t + 1) ⟨t - 1, by omega⟩ =
                w t ⟨t - 2, by omega⟩ * w (t + 1) ⟨0, hn⟩ := by
              simpa only [hsub] using heq
            linear_combination heq' - hlead
          rw [hval]
          exact mul_ne_zero hne (sub_ne_zero.2 hnb_step)
        refine ⟨?_, ?_, ?_⟩
        · simpa only [show t + 1 - 2 = t - 1 by omega] using hne_next
        · have heq := hstep ⟨t, by omega⟩ (by dsimp only; omega)
          have hno : ¬ Odd t := Nat.not_odd_iff_even.2 he
          simp only [hno, ite_false] at heq
          have hzt : w t ⟨t, by omega⟩ = 0 := hvan ⟨t, by omega⟩ le_rfl
          rw [hzt, zero_add] at heq
          have hsub2 : t + 1 - 2 = t - 1 := by omega
          simp only [Nat.add_sub_cancel, hsub2]
          rw [heq, mul_comm]
        · intro ⟨j, hjlt⟩ hj_ge
          dsimp only at hj_ge
          induction j using Nat.strong_induction_on with
          | h j ihj =>
            have heq := hstep ⟨j, hjlt⟩ (by dsimp only; omega)
            have hztj : w t ⟨j, hjlt⟩ = 0 := hvan ⟨j, hjlt⟩ (by dsimp only; omega)
            rw [hztj, zero_add] at heq
            split_ifs at heq with hoj
            · have hzprev : w t ⟨j - 1, by omega⟩ = 0 := hvan ⟨j - 1, by omega⟩ (by dsimp only; omega)
              rw [hzprev, zero_mul] at heq
              exact heq
            · have hej : Even j := Nat.not_odd_iff_even.1 hoj
              have hj_ge2 : t + 2 ≤ j := by
                rcases he with ⟨m1, rfl⟩
                rcases hej with ⟨m2, rfl⟩
                omega
              have hprev := ihj (j - 1) (by omega) (by omega) (by omega)
              rw [hprev, mul_zero] at heq
              exact heq
      · simp only [he, ite_false] at hstep
        have ho_t : Odd t := Nat.not_even_iff_odd.1 he
        have he_tm1 : Even (t - 1) := by
          rcases ho_t with ⟨m, rfl⟩
          exact ⟨m, by omega⟩
        have hno_tm1 : ¬ Odd (t - 1) := Nat.not_odd_iff_even.2 he_tm1
        have hne_next : w (t + 1) ⟨t - 1, by omega⟩ ≠ 0 := by
          have heq := hstep ⟨t - 1, by omega⟩ (by dsimp only; omega)
          simp only [hno_tm1, ite_false] at heq
          have hsub : t - 1 - 1 = t - 2 := by omega
          have hval : w (t + 1) ⟨t - 1, by omega⟩ =
              (w (t + 1) ⟨0, hn⟩ - w (t - 1) ⟨0, hn⟩) * w t ⟨t - 2, by omega⟩ := by
            have heq' : w (t + 1) ⟨t - 1, by omega⟩ + w t ⟨t - 1, by omega⟩ =
                w (t + 1) ⟨0, hn⟩ * w t ⟨t - 2, by omega⟩ := by
              simpa only [hsub] using heq
            linear_combination heq' - hlead
          rw [hval]
          exact mul_ne_zero (sub_ne_zero.2 hnb_step) hne
        refine ⟨?_, ?_, ?_⟩
        · simpa only [show t + 1 - 2 = t - 1 by omega] using hne_next
        · have heq := hstep ⟨t, by omega⟩ (by dsimp only; omega)
          simp only [ho_t, ite_true] at heq
          have hzt : w t ⟨t, by omega⟩ = 0 := hvan ⟨t, by omega⟩ le_rfl
          rw [hzt, add_zero] at heq
          have hsub2 : t + 1 - 2 = t - 1 := by omega
          simp only [Nat.add_sub_cancel, hsub2]
          exact heq
        · intro ⟨j, hjlt⟩ hj_ge
          dsimp only at hj_ge
          induction j using Nat.strong_induction_on with
          | h j ihj =>
            have heq := hstep ⟨j, hjlt⟩ (by dsimp only; omega)
            have hztj : w t ⟨j, hjlt⟩ = 0 := hvan ⟨j, hjlt⟩ (by dsimp only; omega)
            rw [hztj, add_zero] at heq
            split_ifs at heq with hoj
            · have hj_ge2 : t + 2 ≤ j := by
                rcases ho_t with ⟨m1, rfl⟩
                rcases hoj with ⟨m2, rfl⟩
                omega
              have hprev := ihj (j - 1) (by omega) (by omega) (by omega)
              rw [hprev, zero_mul] at heq
              exact heq
            · have hzprev : w t ⟨j - 1, by omega⟩ = 0 := hvan ⟨j - 1, by omega⟩ (by dsimp only; omega)
              rw [hzprev, mul_zero] at heq
              exact heq

/-- Meet-in-the-middle theorem for `A(n, F)`: over any integral domain `F`, the zero point `(0)`
in `A(n, F)` lies on no closed non-backtracking walk of length `2 r` with `2 ≤ r ≤ n`. -/
theorem no_closed_nb_walk_zero_A {n r : ℕ} {F : Type*} [CommRing F] [IsDomain F]
    (hr2 : 2 ≤ r) (hrn : r ≤ n)
    (w : Fin (2 * r) → Fin n → F)
    (h0 : w ⟨0, by omega⟩ = 0)
    (hadj : ∀ i : Fin (2 * r),
      if Even i.val then
        PLAdjA n F (w i) (w ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩)
      else
        PLAdjA n F (w ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩) (w i))
    (hnb : ∀ i : Fin (2 * r),
      w i ⟨0, by omega⟩ ≠ w ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩ ⟨0, by omega⟩) :
    False := by
  have hn : 0 < n := by omega
  let wf : ℕ → Fin n → F := fun t => w ⟨t % (2 * r), Nat.mod_lt _ (by omega)⟩
  let wb : ℕ → Fin n → F := fun t => w ⟨(2 * r - t % (2 * r)) % (2 * r), Nat.mod_lt _ (by omega)⟩
  have hwf := walkA_invariant hn hrn wf (by simp [wf, h0])
    (by
      intro t ht
      have hmod1 : t % (2 * r) = t := Nat.mod_eq_of_lt (by omega)
      have hmod2 : (t + 1) % (2 * r) = (t % (2 * r) + 1) % (2 * r) := by rw [hmod1]
      have h := hadj ⟨t % (2 * r), Nat.mod_lt _ (by omega)⟩
      simpa only [wf, hmod1, hmod2] using h)
    (by
      intro t ht
      have hmod1 : t % (2 * r) = t := Nat.mod_eq_of_lt (by omega)
      have hmod2 : (t + 2) % (2 * r) = (t % (2 * r) + 2) % (2 * r) := by rw [hmod1]
      have h := hnb ⟨t % (2 * r), Nat.mod_lt _ (by omega)⟩
      simpa only [wf, hmod1, hmod2] using h.symm)
    r hr2 le_rfl
  have hwb := walkA_invariant hn hrn wb (by simp [wb, h0])
    (by
      intro t ht
      have hlt : t < 2 * r := by omega
      have hmod_t : t % (2 * r) = t := Nat.mod_eq_of_lt hlt
      have hmod_tp1 : (t + 1) % (2 * r) = t + 1 := Nat.mod_eq_of_lt (by omega)
      have hidx_tp1 : (2 * r - (t + 1) % (2 * r)) % (2 * r) = 2 * r - (t + 1) := by
        rw [hmod_tp1]; exact Nat.mod_eq_of_lt (by omega)
      have hsucc : ((2 * r - (t + 1)) + 1) % (2 * r) = (2 * r - t % (2 * r)) % (2 * r) := by
        rw [hmod_t]
        by_cases ht0 : t = 0
        · subst ht0
          rw [show 2 * r - (0 + 1) + 1 = 2 * r by omega, Nat.sub_zero, Nat.mod_self]
        · have : 2 * r - (t + 1) + 1 = 2 * r - t := by omega
          rw [this]
      have h := hadj ⟨2 * r - (t + 1), by omega⟩
      have hpar : Even (2 * r - (t + 1)) ↔ ¬ Even t := by
        constructor
        · rintro ⟨m, hm⟩ ⟨m', hm'⟩; omega
        · intro hne
          rcases Nat.not_even_iff_odd.1 hne with ⟨m, hm⟩
          exact ⟨r - m - 1, by omega⟩
      by_cases het : Even t
      · have hno : ¬ Even (2 * r - (t + 1)) := fun h' => hpar.1 h' het
        simp only [het, ite_true, wb, hidx_tp1]
        simp only [hno, ite_false, hsucc] at h
        exact h
      · have he' : Even (2 * r - (t + 1)) := hpar.2 het
        simp only [het, ite_false, wb, hidx_tp1]
        simp only [he', ite_true, hsucc] at h
        exact h)
    (by
      intro t ht
      have hmod_t : t % (2 * r) = t := Nat.mod_eq_of_lt (by omega)
      have hmod_tp2 : (t + 2) % (2 * r) = t + 2 := Nat.mod_eq_of_lt (by omega)
      have hidx_tp2 : (2 * r - (t + 2) % (2 * r)) % (2 * r) = 2 * r - (t + 2) := by
        rw [hmod_tp2]; exact Nat.mod_eq_of_lt (by omega)
      have hadd2 : ((2 * r - (t + 2)) + 2) % (2 * r) = (2 * r - t % (2 * r)) % (2 * r) := by
        rw [hmod_t]
        by_cases ht0 : t = 0
        · subst ht0
          rw [show 2 * r - (0 + 2) + 2 = 2 * r by omega, Nat.sub_zero, Nat.mod_self]
        · have : 2 * r - (t + 2) + 2 = 2 * r - t := by omega
          rw [this]
      have h := hnb ⟨2 * r - (t + 2), by omega⟩
      simpa only [wb, hidx_tp2, hadd2] using h)
    r hr2 le_rfl
  have hwfr : wf r = w ⟨r, by omega⟩ := by
    simp [wf, Nat.mod_eq_of_lt (show r < 2 * r by omega)]
  have hwbr : wb r = w ⟨r, by omega⟩ := by
    have h1 : r % (2 * r) = r := Nat.mod_eq_of_lt (by omega)
    have h2 : (2 * r - r) % (2 * r) = r := by
      have : 2 * r - r = r := by omega
      rw [this, h1]
    simp [wb, h1, h2]
  have hwfm : wf (r - 1) = w ⟨r - 1, by omega⟩ := by
    simp [wf, Nat.mod_eq_of_lt (show r - 1 < 2 * r by omega)]
  have hwbm : wb (r - 1) = w ⟨r + 1, by omega⟩ := by
    have h1 : (r - 1) % (2 * r) = r - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (2 * r - (r - 1)) % (2 * r) = r + 1 := by
      have : 2 * r - (r - 1) = r + 1 := by omega
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    simp [wb, h1, h2]
  rw [hwfr, hwfm] at hwf
  rw [hwbr, hwbm] at hwb
  have hmul : w ⟨r, by omega⟩ ⟨r - 2, by omega⟩ * w ⟨r - 1, by omega⟩ ⟨0, hn⟩ =
      w ⟨r, by omega⟩ ⟨r - 2, by omega⟩ * w ⟨r + 1, by omega⟩ ⟨0, hn⟩ :=
    hwf.2.1.symm.trans hwb.2.1
  have hfc_eq : w ⟨r - 1, by omega⟩ ⟨0, hn⟩ = w ⟨r + 1, by omega⟩ ⟨0, hn⟩ :=
    mul_left_cancel₀ hwf.1 hmul
  have hnb_r := hnb ⟨r - 1, by omega⟩
  have hmod_r : (r - 1 + 2) % (2 * r) = r + 1 := by
    have : r - 1 + 2 = r + 1 := by omega
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  simp only [hmod_r] at hnb_r
  exact hnb_r hfc_eq

/-! ### Part 2: Covering Projection `D(2 k + 1, F) → A(k + 2, F)` -/

/-- Index map embedding coordinates `(1, 2, 3, 5, 7, ..., 2 k + 1)` of `D(2 k + 1, F)` into
`A(k + 2, F)` (0-based: `0 ↦ 0`, `1 ↦ 1`, `j ≥ 2 ↦ 2 j - 2`). -/
def idxDtoA (k : ℕ) (hk : 1 ≤ k) (j : Fin (k + 2)) : Fin (2 * k + 1) :=
  if h0 : j.val = 0 then ⟨0, by omega⟩
  else if h1 : j.val = 1 then ⟨1, by omega⟩
  else ⟨2 * j.val - 2, by omega⟩

/-- Coordinate projection `D(2 k + 1, F) → A(k + 2, F)` preserves point-line adjacency. -/
lemma projDtoA_plAdj {k : ℕ} {F : Type*} [CommRing F] (hk : 1 ≤ k)
    {p l : Fin (2 * k + 1) → F} (h : PLAdj (2 * k + 1) F p l) :
    PLAdjA (k + 2) F (p ∘ idxDtoA k hk) (l ∘ idxDtoA k hk) := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  have h0k : 0 < 2 * k + 1 := by omega
  by_cases hj_eq1 : j = 1
  · subst hj_eq1
    have heq := h ⟨1, by omega⟩ (by dsimp only; omega)
    simp only [Function.comp_apply, idxDtoA, odd_one, ite_true, Nat.one_ne_zero, ↓reduceDIte]
    simpa only [rhsD, h0k, ↓reduceDIte] using heq
  · by_cases hj_eq2 : j = 2
    · subst hj_eq2
      have heq := h ⟨2, by omega⟩ (by dsimp only; omega)
      simp only [Function.comp_apply, idxDtoA]
      have hno2 : ¬ Odd 2 := by decide
      simp only [hno2, ite_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceDIte]
      have h21 : 2 - 1 = 1 := rfl
      have h22 : 2 * 2 - 2 = 2 := rfl
      simp only [h21, h22, Nat.one_ne_zero, ↓reduceDIte]
      simpa only [rhsD, h0k, ↓reduceDIte, OfNat.ofNat_ne_one] using heq
    · have hj3 : 3 ≤ j := by omega
      have hidx : (idxDtoA k hk ⟨j, hjlt⟩).val = 2 * j - 2 := by
        simp [idxDtoA, show j ≠ 0 by omega, hj_eq1]
      have hidx_prev : (idxDtoA k hk ⟨j - 1, by omega⟩).val = 2 * j - 4 := by
        simp only [idxDtoA, show j - 1 ≠ 0 by omega, show j - 1 ≠ 1 by omega, ↓reduceDIte]
        omega
      have heq := h ⟨2 * j - 2, by omega⟩ (by dsimp only; omega)
      simp only [rhsD, h0k, ↓reduceDIte] at heq
      have hne1 : 2 * j - 2 ≠ 1 := by omega
      have hne2 : 2 * j - 2 ≠ 2 := by omega
      have hge3 : 3 ≤ 2 * j - 2 := by omega
      simp only [hne1, hne2, hge3, ↓reduceDIte] at heq
      have heq_idx : idxDtoA k hk ⟨j, hjlt⟩ = ⟨2 * j - 2, by omega⟩ := Fin.ext hidx
      have heq_prev : idxDtoA k hk ⟨j - 1, by omega⟩ = ⟨2 * j - 4, by omega⟩ := Fin.ext hidx_prev
      have heq_zero : idxDtoA k hk ⟨0, by omega⟩ = ⟨0, by omega⟩ := by simp [idxDtoA]
      simp only [Function.comp_apply, heq_idx, heq_prev, heq_zero]
      by_cases hoj : Odd j
      · have hmod : (2 * j - 2 + 1) % 4 = 0 ∨ (2 * j - 2 + 1) % 4 = 1 := by
          rcases hoj with ⟨m, rfl⟩
          right; omega
        simp only [hoj, ite_true]
        simp only [hmod, ite_true] at heq
        have hsub : 2 * j - 2 - 2 = 2 * j - 4 := by omega
        simpa only [hsub] using heq
      · have hej : Even j := Nat.not_odd_iff_even.1 hoj
        have hmod : ¬ ((2 * j - 2 + 1) % 4 = 0 ∨ (2 * j - 2 + 1) % 4 = 1) := by
          rcases hej with ⟨m, rfl⟩
          omega
        simp only [hoj, ite_false]
        simp only [hmod, ite_false] at heq
        have hsub : 2 * j - 2 - 2 = 2 * j - 4 := by omega
        simpa only [hsub] using heq

/-- At `m = 2`, `D(2, F)` coincides directly with `A(2, F)`. -/
lemma plAdj2_to_plAdjA2 {F : Type*} [CommRing F] {p l : Fin 2 → F}
    (h : PLAdj 2 F p l) : PLAdjA 2 F p l := by
  intro ⟨j, hjlt⟩ hj1
  dsimp only at hj1
  have hj_eq : j = 1 := by omega
  subst hj_eq
  have heq := h ⟨1, hjlt⟩ (by dsimp only; omega)
  simp only [odd_one, ite_true]
  simpa only [rhsD, Nat.zero_lt_two, ↓reduceDIte] using heq

/-! ### Part 3: Additive Automorphisms and Point Transitivity of `D(m, F)` -/

/-- DS28 Table 2 additive map `t₀,ₓ` on points: shifts `p 0 ↦ p 0 + x`. -/
def t0P {m : ℕ} {F : Type*} [CommRing F] (x : F) (p : Fin m → F) : Fin m → F :=
  fun ⟨i, hi⟩ =>
    if i = 0 then p ⟨i, hi⟩ + x
    else if i = 1 then p ⟨i, hi⟩
    else if h2 : i = 2 then p ⟨i, hi⟩ + p ⟨1, by omega⟩ * x
    else if h3 : 3 ≤ i then
      if (i + 1) % 4 = 1 ∨ (i + 1) % 4 = 3 then
        p ⟨i, hi⟩ + p ⟨i - 1, by omega⟩ * x
      else
        p ⟨i, hi⟩
    else p ⟨i, hi⟩

/-- DS28 Table 2 additive map `t₀,ₓ` on lines: fixes `l 0`. -/
def t0L {m : ℕ} {F : Type*} [CommRing F] (x : F) (l : Fin m → F) : Fin m → F :=
  fun ⟨i, hi⟩ =>
    if i = 0 then l ⟨i, hi⟩
    else if h1 : i = 1 then l ⟨i, hi⟩ + l ⟨0, by omega⟩ * x
    else if h2 : i = 2 then l ⟨i, hi⟩ + 2 * l ⟨1, by omega⟩ * x + l ⟨0, by omega⟩ * x ^ 2
    else if h3 : 3 ≤ i then
      if (i + 1) % 4 = 0 then l ⟨i, hi⟩
      else if (i + 1) % 4 = 1 then l ⟨i, hi⟩ + l ⟨i - 1, by omega⟩ * x
      else if (i + 1) % 4 = 2 then l ⟨i, hi⟩ + l ⟨i - 2, by omega⟩ * x
      else l ⟨i, hi⟩ + l ⟨i - 1, by omega⟩ * x + l ⟨i - 2, by omega⟩ * x +
        l ⟨i - 3, by omega⟩ * x ^ 2
    else l ⟨i, hi⟩

lemma t0P_zero {m : ℕ} {F : Type*} [CommRing F] (hm : 0 < m) (x : F) (p : Fin m → F) :
    t0P x p ⟨0, hm⟩ = p ⟨0, hm⟩ + x := by simp [t0P]

lemma t0L_zero {m : ℕ} {F : Type*} [CommRing F] (hm : 0 < m) (x : F) (l : Fin m → F) :
    t0L x l ⟨0, hm⟩ = l ⟨0, hm⟩ := by simp [t0L]

/-- `t₀,ₓ` preserves point-line adjacency in `D(m, F)` for all `m` and all commutative rings `F`. -/
lemma t0_preserves_PLAdj {m : ℕ} {F : Type*} [CommRing F] (x : F) {p l : Fin m → F}
    (h : PLAdj m F p l) : PLAdj m F (t0P x p) (t0L x l) := by
  intro ⟨i, hi⟩ hi1
  dsimp only at hi1
  have hm : 0 < m := by omega
  by_cases h1 : i = 1
  · subst h1
    have e1 := h ⟨1, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e1 ⊢
    simp only [t0P, t0L, Nat.one_ne_zero, ↓reduceIte, ↓reduceDIte]
    linear_combination e1
  · by_cases h2 : i = 2
    · subst h2
      have e1 := h ⟨1, by omega⟩ (by dsimp only; omega)
      have e2 := h ⟨2, hi⟩ (by dsimp only; omega)
      simp only [rhsD, hm, ↓reduceDIte] at e1 e2 ⊢
      simp only [t0P, t0L] at e1 e2 ⊢
      norm_num at e1 e2 ⊢
      linear_combination e2 + x * e1
    · have h3 : 3 ≤ i := by omega
      have ei := h ⟨i, hi⟩ (by dsimp only; omega)
      simp only [rhsD, hm, ↓reduceDIte, h1, h2, h3] at ei ⊢
      have hne0 : i ≠ 0 := by omega
      have hmod4 : (i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1 ∨ (i + 1) % 4 = 2 ∨ (i + 1) % 4 = 3 := by
        omega
      rcases hmod4 with hm0 | hm1 | hm2 | hm3
      · have hor : (i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1 := Or.inl hm0
        simp only [hor, ite_true] at ei ⊢
        have hp_i : t0P x p ⟨i, hi⟩ = p ⟨i, hi⟩ := by
          simp [t0P, hne0, h1, h2, h3, hm0]
        have hl_i : t0L x l ⟨i, hi⟩ = l ⟨i, hi⟩ := by
          simp [t0L, hne0, h1, h2, h3, hm0]
        have hp_im2 : t0P x p ⟨i - 2, by omega⟩ = p ⟨i - 2, by omega⟩ := by
          by_cases him2 : i - 2 = 1
          · simp [t0P, him2]
          · have hge3' : 3 ≤ i - 2 := by omega
            have hm' : (i - 2 + 1) % 4 = 2 := by omega
            simp [t0P, show i - 2 ≠ 0 by omega, him2, show i - 2 ≠ 2 by omega, hge3', hm']
        rw [hp_i, hl_i, hp_im2, t0L_zero]
        exact ei
      · have hor : (i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1 := Or.inr hm1
        simp only [hor, ite_true] at ei ⊢
        have hp_i : t0P x p ⟨i, hi⟩ = p ⟨i, hi⟩ + p ⟨i - 1, by omega⟩ * x := by
          simp [t0P, hne0, h1, h2, h3, hm1]
        have hl_i : t0L x l ⟨i, hi⟩ = l ⟨i, hi⟩ + l ⟨i - 1, by omega⟩ * x := by
          simp [t0L, hne0, h1, h2, h3, hm1]
        have hp_im2 : t0P x p ⟨i - 2, by omega⟩ =
            p ⟨i - 2, by omega⟩ + p ⟨i - 3, by omega⟩ * x := by
          by_cases him2 : i - 2 = 2
          · have hsub : i - 3 = 1 := by omega
            simp only [t0P, him2, hsub, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte,
              ↓reduceDIte]
          · have hge3' : 3 ≤ i - 2 := by omega
            have hm' : (i - 2 + 1) % 4 = 3 := by omega
            have hsub : i - 2 - 1 = i - 3 := by omega
            simp only [t0P, show i - 2 ≠ 0 by omega, show i - 2 ≠ 1 by omega, him2, hge3', hm',
              hsub, ↓reduceIte, ↓reduceDIte, or_true]
        have eim1 := h ⟨i - 1, by omega⟩ (by dsimp only; omega)
        have hge3_im1 : 3 ≤ i - 1 := by omega
        have hor_im1 : (i - 1 + 1) % 4 = 0 ∨ (i - 1 + 1) % 4 = 1 := Or.inl (by omega)
        simp only [rhsD, hm, ↓reduceDIte, show i - 1 ≠ 1 by omega, show i - 1 ≠ 2 by omega, hge3_im1,
          hor_im1, ite_true] at eim1
        have hsub : i - 1 - 2 = i - 3 := by omega
        simp only [hsub] at eim1
        rw [hp_i, hl_i, hp_im2, t0L_zero]
        linear_combination ei + x * eim1
      · have hor : ¬ ((i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1) := by omega
        simp only [hor, ite_false] at ei ⊢
        have hp_i : t0P x p ⟨i, hi⟩ = p ⟨i, hi⟩ := by
          simp [t0P, hne0, h1, h2, h3, hm2]
        have hl_i : t0L x l ⟨i, hi⟩ = l ⟨i, hi⟩ + l ⟨i - 2, by omega⟩ * x := by
          simp [t0L, hne0, h1, h2, h3, hm2]
        have hl_im2 : t0L x l ⟨i - 2, by omega⟩ = l ⟨i - 2, by omega⟩ := by
          have hge3' : 3 ≤ i - 2 := by omega
          have hm' : (i - 2 + 1) % 4 = 0 := by omega
          simp [t0L, show i - 2 ≠ 0 by omega, show i - 2 ≠ 1 by omega, show i - 2 ≠ 2 by omega,
            hge3', hm']
        rw [hp_i, hl_i, hl_im2, t0P_zero]
        linear_combination ei
      · have hor : ¬ ((i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1) := by omega
        simp only [hor, ite_false] at ei ⊢
        have hp_i : t0P x p ⟨i, hi⟩ = p ⟨i, hi⟩ + p ⟨i - 1, by omega⟩ * x := by
          simp [t0P, hne0, h1, h2, h3, hm3]
        have hl_i : t0L x l ⟨i, hi⟩ = l ⟨i, hi⟩ + l ⟨i - 1, by omega⟩ * x +
            l ⟨i - 2, by omega⟩ * x + l ⟨i - 3, by omega⟩ * x ^ 2 := by
          simp [t0L, hne0, h1, h2, h3, hm3]
        have hl_im2 : t0L x l ⟨i - 2, by omega⟩ =
            l ⟨i - 2, by omega⟩ + l ⟨i - 3, by omega⟩ * x := by
          have hge3' : 3 ≤ i - 2 := by omega
          have hm' : (i - 2 + 1) % 4 = 1 := by omega
          have hsub : i - 2 - 1 = i - 3 := by omega
          simp only [t0L, show i - 2 ≠ 0 by omega, show i - 2 ≠ 1 by omega, show i - 2 ≠ 2 by omega,
            hge3', hm', hsub, ↓reduceIte, ↓reduceDIte, one_ne_zero]
        have eim1 := h ⟨i - 1, by omega⟩ (by dsimp only; omega)
        have hge3_im1 : 3 ≤ i - 1 := by omega
        have hor_im1 : ¬ ((i - 1 + 1) % 4 = 0 ∨ (i - 1 + 1) % 4 = 1) := by omega
        simp only [rhsD, hm, ↓reduceDIte, show i - 1 ≠ 1 by omega, show i - 1 ≠ 2 by omega, hge3_im1,
          hor_im1, ite_false] at eim1
        have hsub : i - 1 - 2 = i - 3 := by omega
        simp only [hsub] at eim1
        rw [hp_i, hl_i, hl_im2, t0P_zero]
        linear_combination ei + x * eim1

/-- DS28 Table 2 additive map `t₂,ₓ` on points: fixes `p 0`, shifts `p 1 ↦ p 1 + x`. -/
def t2P {m : ℕ} {F : Type*} [CommRing F] (x : F) (p : Fin m → F) : Fin m → F :=
  fun ⟨i, hi⟩ =>
    if i = 0 then p ⟨i, hi⟩
    else if i = 1 then p ⟨i, hi⟩ + x
    else if h2 : i = 2 then p ⟨i, hi⟩ - p ⟨0, by omega⟩ * x
    else if i = 3 then p ⟨i, hi⟩
    else if h4 : i = 4 then p ⟨i, hi⟩ - p ⟨1, by omega⟩ * x
    else if h5 : 5 ≤ i then
      if Odd i then p ⟨i, hi⟩ + p ⟨i - 4, by omega⟩ * x
      else p ⟨i, hi⟩ - p ⟨i - 4, by omega⟩ * x
    else p ⟨i, hi⟩

/-- DS28 Table 2 additive map `t₂,ₓ` on lines: fixes `l 0`, shifts `l 1 ↦ l 1 - x`. -/
def t2L {m : ℕ} {F : Type*} [CommRing F] (x : F) (l : Fin m → F) : Fin m → F :=
  fun ⟨i, hi⟩ =>
    if i = 0 then l ⟨i, hi⟩
    else if i = 1 then l ⟨i, hi⟩ - x
    else if i = 2 then l ⟨i, hi⟩
    else if h3 : i = 3 then l ⟨i, hi⟩ + l ⟨0, by omega⟩ * x
    else if h4 : i = 4 then l ⟨i, hi⟩ - l ⟨1, by omega⟩ * x
    else if h5 : 5 ≤ i then
      if Odd i then l ⟨i, hi⟩ + l ⟨i - 4, by omega⟩ * x
      else l ⟨i, hi⟩ - l ⟨i - 4, by omega⟩ * x
    else l ⟨i, hi⟩

lemma t2P_zero {m : ℕ} {F : Type*} [CommRing F] (hm : 0 < m) (x : F) (p : Fin m → F) :
    t2P x p ⟨0, hm⟩ = p ⟨0, hm⟩ := by simp [t2P]

lemma t2L_zero {m : ℕ} {F : Type*} [CommRing F] (hm : 0 < m) (x : F) (l : Fin m → F) :
    t2L x l ⟨0, hm⟩ = l ⟨0, hm⟩ := by simp [t2L]

lemma t2P_one {m : ℕ} {F : Type*} [CommRing F] (hm : 1 < m) (x : F) (p : Fin m → F) :
    t2P x p ⟨1, hm⟩ = p ⟨1, hm⟩ + x := by simp [t2P]

/-- `t₂,ₓ` preserves point-line adjacency in `D(m, F)` for all `m` and all commutative rings `F`. -/
lemma t2_preserves_PLAdj {m : ℕ} {F : Type*} [CommRing F] (x : F) {p l : Fin m → F}
    (h : PLAdj m F p l) : PLAdj m F (t2P x p) (t2L x l) := by
  intro ⟨i, hi⟩ hi1
  dsimp only at hi1
  have hm : 0 < m := by omega
  match i with
  | 0 => omega
  | 1 =>
    have e1 := h ⟨1, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e1 ⊢
    simp only [t2P, t2L, Nat.one_ne_zero, ↓reduceIte]
    linear_combination e1
  | 2 =>
    have e2 := h ⟨2, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e2 ⊢
    simp only [t2P, t2L]
    norm_num at e2 ⊢
    linear_combination e2
  | 3 =>
    have e3 := h ⟨3, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e3 ⊢
    simp only [t2P, t2L]
    norm_num at e3 ⊢
    linear_combination e3
  | 4 =>
    have e1 := h ⟨1, by omega⟩ (by dsimp only; omega)
    have e4 := h ⟨4, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e1 e4 ⊢
    simp only [t2P, t2L]
    norm_num at e1 e4 ⊢
    linear_combination e4 - x * e1
  | 5 =>
    have e1 := h ⟨1, by omega⟩ (by dsimp only; omega)
    have e5 := h ⟨5, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e1 e5 ⊢
    simp only [t2P, t2L]
    norm_num at e1 e5 ⊢
    have ho5 : Odd 5 := by decide
    simp only [ho5, ite_true]
    linear_combination e5 + x * e1
  | 6 =>
    have e2 := h ⟨2, by omega⟩ (by dsimp only; omega)
    have e6 := h ⟨6, hi⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte] at e2 e6 ⊢
    simp only [t2P, t2L]
    norm_num at e2 e6 ⊢
    have hno6 : ¬ Odd 6 := by decide
    simp only [hno6, ite_false]
    linear_combination e6 - x * e2
  | i + 7 =>
    have hi_ge3 : 3 ≤ i + 7 := by omega
    have hi_ge5 : 5 ≤ i + 7 := by omega
    have him2_ge5 : 5 ≤ i + 5 := by omega
    have him4_ge3 : 3 ≤ i + 3 := by omega
    have ei := h ⟨i + 7, hi⟩ (by dsimp only; omega)
    have eim4 := h ⟨i + 3, by omega⟩ (by dsimp only; omega)
    simp only [rhsD, hm, ↓reduceDIte, show i + 7 ≠ 1 by omega, show i + 7 ≠ 2 by omega, hi_ge3,
      show i + 3 ≠ 1 by omega, show i + 3 ≠ 2 by omega, him4_ge3] at ei eim4 ⊢
    have hmod_eq : ((i + 7 + 1) % 4 = 0 ∨ (i + 7 + 1) % 4 = 1) ↔
        ((i + 3 + 1) % 4 = 0 ∨ (i + 3 + 1) % 4 = 1) := by omega
    have hpar_eq : Odd (i + 7) ↔ Odd (i + 5) := by
      constructor
      · rintro ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
      · rintro ⟨t, ht⟩; exact ⟨t + 1, by omega⟩
    have htp : t2P x p ⟨i + 7, hi⟩ =
        if Odd (i + 7) then p ⟨i + 7, hi⟩ + p ⟨i + 3, by omega⟩ * x
        else p ⟨i + 7, hi⟩ - p ⟨i + 3, by omega⟩ * x := by
      simp only [t2P, show i + 7 ≠ 0 by omega, show i + 7 ≠ 1 by omega, show i + 7 ≠ 2 by omega,
        show i + 7 ≠ 3 by omega, show i + 7 ≠ 4 by omega, hi_ge5, ↓reduceIte, ↓reduceDIte]
      have hsub : i + 7 - 4 = i + 3 := by omega
      simp only [hsub]
    have htl : t2L x l ⟨i + 7, hi⟩ =
        if Odd (i + 7) then l ⟨i + 7, hi⟩ + l ⟨i + 3, by omega⟩ * x
        else l ⟨i + 7, hi⟩ - l ⟨i + 3, by omega⟩ * x := by
      simp only [t2L, show i + 7 ≠ 0 by omega, show i + 7 ≠ 1 by omega, show i + 7 ≠ 2 by omega,
        show i + 7 ≠ 3 by omega, show i + 7 ≠ 4 by omega, hi_ge5, ↓reduceIte, ↓reduceDIte]
      have hsub : i + 7 - 4 = i + 3 := by omega
      simp only [hsub]
    have htp_m2 : t2P x p ⟨i + 5, by omega⟩ =
        if Odd (i + 7) then p ⟨i + 5, by omega⟩ + p ⟨i + 1, by omega⟩ * x
        else p ⟨i + 5, by omega⟩ - p ⟨i + 1, by omega⟩ * x := by
      simp only [t2P, show i + 5 ≠ 0 by omega, show i + 5 ≠ 1 by omega, show i + 5 ≠ 2 by omega,
        show i + 5 ≠ 3 by omega, show i + 5 ≠ 4 by omega, him2_ge5, ↓reduceIte, ↓reduceDIte,
        hpar_eq]
      have hsub : i + 5 - 4 = i + 1 := by omega
      simp only [hsub]
    have htl_m2 : t2L x l ⟨i + 5, by omega⟩ =
        if Odd (i + 7) then l ⟨i + 5, by omega⟩ + l ⟨i + 1, by omega⟩ * x
        else l ⟨i + 5, by omega⟩ - l ⟨i + 1, by omega⟩ * x := by
      simp only [t2L, show i + 5 ≠ 0 by omega, show i + 5 ≠ 1 by omega, show i + 5 ≠ 2 by omega,
        show i + 5 ≠ 3 by omega, show i + 5 ≠ 4 by omega, him2_ge5, ↓reduceIte, ↓reduceDIte,
        hpar_eq]
      have hsub : i + 5 - 4 = i + 1 := by omega
      simp only [hsub]
    have hsub7 : i + 7 - 2 = i + 5 := by omega
    have hsub3 : i + 3 - 2 = i + 1 := by omega
    simp only [hsub7] at ei ⊢
    simp only [hsub3] at eim4
    rw [htp, htl, t2P_zero, t2L_zero, htp_m2, htl_m2]
    by_cases hmod : (i + 7 + 1) % 4 = 0 ∨ (i + 7 + 1) % 4 = 1
    · have hmod' : (i + 3 + 1) % 4 = 0 ∨ (i + 3 + 1) % 4 = 1 := hmod_eq.1 hmod
      simp only [hmod, hmod', ite_true] at ei eim4 ⊢
      split_ifs
      · linear_combination ei + x * eim4
      · linear_combination ei - x * eim4
    · have hmod' : ¬ ((i + 3 + 1) % 4 = 0 ∨ (i + 3 + 1) % 4 = 1) := fun h' => hmod (hmod_eq.2 h')
      simp only [hmod, hmod', ite_false] at ei eim4 ⊢
      split_ifs
      · linear_combination ei + x * eim4
      · linear_combination ei - x * eim4

/-- DS28 Table 3 additive map `tₛ,ₓ` on points for 0-based `s ≥ 2` (1-based `j = s + 1 ≥ 3`):
fixes all coordinates `< s` and shifts coordinate `s` by `+x`. -/
def tjP {m : ℕ} {F : Type*} [CommRing F] (s : ℕ) (x : F) (p : Fin m → F) : Fin m → F :=
  fun ⟨i, hi⟩ =>
    if (s + 1) % 4 = 0 ∨ (s + 1) % 4 = 1 then
      if i = s then p ⟨i, hi⟩ + x
      else if h2 : i = s + 2 then p ⟨i, hi⟩ - p ⟨0, by omega⟩ * x
      else if h4 : i = s + 4 then p ⟨i, hi⟩ - p ⟨1, by omega⟩ * x
      else if h6 : s + 6 ≤ i ∧ Even (i - s) then p ⟨i, hi⟩ - p ⟨i - s - 4, by omega⟩ * x
      else p ⟨i, hi⟩
    else
      if i = s then p ⟨i, hi⟩ + x
      else if h4 : s + 4 ≤ i ∧ Even (i - s) then p ⟨i, hi⟩ + p ⟨i - s - 3, by omega⟩ * x
      else p ⟨i, hi⟩

/-- DS28 Table 3 additive map `tₛ,ₓ` on lines for 0-based `s ≥ 2` (1-based `j = s + 1 ≥ 3`):
fixes all coordinates `< s` and shifts coordinate `s` by `-x`. -/
def tjL {m : ℕ} {F : Type*} [CommRing F] (s : ℕ) (x : F) (l : Fin m → F) : Fin m → F :=
  fun ⟨i, hi⟩ =>
    if (s + 1) % 4 = 0 ∨ (s + 1) % 4 = 1 then
      if i = s then l ⟨i, hi⟩ - x
      else if h4 : i = s + 4 then l ⟨i, hi⟩ - l ⟨1, by omega⟩ * x
      else if h6 : s + 6 ≤ i ∧ Even (i - s) then l ⟨i, hi⟩ - l ⟨i - s - 4, by omega⟩ * x
      else l ⟨i, hi⟩
    else
      if i = s then l ⟨i, hi⟩ - x
      else if h2 : i = s + 2 then l ⟨i, hi⟩ + l ⟨0, by omega⟩ * x
      else if h4 : s + 4 ≤ i ∧ Even (i - s) then l ⟨i, hi⟩ + l ⟨i - s - 3, by omega⟩ * x
      else l ⟨i, hi⟩

lemma tjP_lt {m : ℕ} {F : Type*} [CommRing F] {s : ℕ} (x : F) (p : Fin m → F)
    {i : Fin m} (hlt : i.val < s) : tjP s x p i = p i := by
  rcases i with ⟨i, hi⟩
  dsimp only at hlt
  simp only [tjP]
  split_ifs <;> first | rfl | omega

lemma tjL_lt {m : ℕ} {F : Type*} [CommRing F] {s : ℕ} (x : F) (l : Fin m → F)
    {i : Fin m} (hlt : i.val < s) : tjL s x l i = l i := by
  rcases i with ⟨i, hi⟩
  dsimp only at hlt
  simp only [tjL]
  split_ifs <;> first | rfl | omega

lemma tjP_self {m : ℕ} {F : Type*} [CommRing F] (s : ℕ) (hs : s < m) (x : F) (p : Fin m → F) :
    tjP s x p ⟨s, hs⟩ = p ⟨s, hs⟩ + x := by
  simp only [tjP]
  split_ifs <;> rfl

lemma tjP_odd {m : ℕ} {F : Type*} [CommRing F] {s : ℕ} (x : F) (p : Fin m → F)
    {i : Fin m} (hodd : Odd (i.val - s)) : tjP s x p i = p i := by
  rcases i with ⟨i, hi⟩
  dsimp only at hodd
  have hne : ¬ Even (i - s) := Nat.not_even_iff_odd.2 hodd
  have hne0 : i ≠ s := fun h => hne (by rw [h, Nat.sub_self]; exact Even.zero)
  have hne2 : i ≠ s + 2 := fun h => hne (by rw [h, show s + 2 - s = 2 by omega]; decide)
  have hne4 : i ≠ s + 4 := fun h => hne (by rw [h, show s + 4 - s = 4 by omega]; decide)
  simp only [tjP, hne0, hne2, hne4, hne, and_false, ite_false, ↓reduceDIte]
  split_ifs <;> rfl

lemma tjL_odd {m : ℕ} {F : Type*} [CommRing F] {s : ℕ} (x : F) (l : Fin m → F)
    {i : Fin m} (hodd : Odd (i.val - s)) : tjL s x l i = l i := by
  rcases i with ⟨i, hi⟩
  dsimp only at hodd
  have hne : ¬ Even (i - s) := Nat.not_even_iff_odd.2 hodd
  have hne0 : i ≠ s := fun h => hne (by rw [h, Nat.sub_self]; exact Even.zero)
  have hne2 : i ≠ s + 2 := fun h => hne (by rw [h, show s + 2 - s = 2 by omega]; decide)
  have hne4 : i ≠ s + 4 := fun h => hne (by rw [h, show s + 4 - s = 4 by omega]; decide)
  simp only [tjL, hne0, hne2, hne4, hne, and_false, ite_false, ↓reduceDIte]
  split_ifs <;> rfl

/-- `tₛ,ₓ` (for `s ≥ 2`) preserves point-line adjacency in `D(m, F)`. -/
lemma tj_preserves_PLAdj {m : ℕ} {F : Type*} [CommRing F] {s : ℕ} (hs2 : 2 ≤ s) (x : F)
    {p l : Fin m → F} (h : PLAdj m F p l) : PLAdj m F (tjP s x p) (tjL s x l) := by
  intro ⟨i, hi⟩ hi1
  dsimp only at hi1
  have hm : 0 < m := by omega
  have hp0 : tjP s x p ⟨0, hm⟩ = p ⟨0, hm⟩ := tjP_lt x p (i := ⟨0, hm⟩) (by dsimp only; omega)
  have hl0 : tjL s x l ⟨0, hm⟩ = l ⟨0, hm⟩ := tjL_lt x l (i := ⟨0, hm⟩) (by dsimp only; omega)
  by_cases hilt : i < s
  · have hp_i := tjP_lt x p (i := ⟨i, hi⟩) (by dsimp only; exact hilt)
    have hl_i := tjL_lt x l (i := ⟨i, hi⟩) (by dsimp only; exact hilt)
    have ei := h ⟨i, hi⟩ hi1
    rw [hp_i, hl_i, ei]
    simp only [rhsD, hm, ↓reduceDIte]
    by_cases h1 : i = 1
    · simp only [h1, ↓reduceDIte, hp0, hl0]
    · by_cases h2 : i = 2
      · have hl1 : tjL s x l ⟨1, by omega⟩ = l ⟨1, by omega⟩ :=
          tjL_lt x l (i := ⟨1, by omega⟩) (by dsimp only; omega)
        simp only [h2, OfNat.ofNat_ne_one, ↓reduceDIte, hp0, hl1]
      · have h3 : 3 ≤ i := by omega
        simp only [h1, h2, h3, ↓reduceDIte]
        split_ifs
        · rw [tjP_lt x p (i := ⟨i - 2, by omega⟩) (by dsimp only; omega), hl0]
        · rw [hp0, tjL_lt x l (i := ⟨i - 2, by omega⟩) (by dsimp only; omega)]
  · by_cases his : i = s
    · subst his
      have hp_s := tjP_self i hi x p
      have hl_s : tjL i x l ⟨i, hi⟩ = l ⟨i, hi⟩ - x := by simp only [tjL]; split_ifs <;> rfl
      have ei := h ⟨i, hi⟩ hi1
      rw [hp_s, hl_s]
      have hrhs : rhsD (tjP i x p) (tjL i x l) ⟨i, hi⟩ = rhsD p l ⟨i, hi⟩ := by
        simp only [rhsD, hm, ↓reduceDIte]
        by_cases h1 : i = 1
        · omega
        · by_cases h2 : i = 2
          · simp only [h2, OfNat.ofNat_ne_one, ↓reduceDIte]
            rw [tjP_lt x p (i := ⟨0, hm⟩) (by dsimp only; omega),
              tjL_lt x l (i := ⟨1, by omega⟩) (by dsimp only; omega)]
          · have h3 : 3 ≤ i := by omega
            simp only [h1, h2, h3, ↓reduceDIte]
            split_ifs
            · rw [tjP_lt x p (i := ⟨i - 2, by omega⟩) (by dsimp only; omega), hl0]
            · rw [hp0, tjL_lt x l (i := ⟨i - 2, by omega⟩) (by dsimp only; omega)]
      rw [hrhs]; linear_combination ei
    · have h3 : 3 ≤ i := by omega
      have hne1 : i ≠ 1 := by omega
      have hne2 : i ≠ 2 := by omega
      have ei := h ⟨i, hi⟩ hi1
      simp only [rhsD, hm, ↓reduceDIte, hne1, hne2, h3] at ei ⊢
      by_cases hodd : Odd (i - s)
      · have hpi := tjP_odd x p (i := ⟨i, hi⟩) (by dsimp only; exact hodd)
        have hli := tjL_odd x l (i := ⟨i, hi⟩) (by dsimp only; exact hodd)
        have hp_im2 : tjP s x p ⟨i - 2, by omega⟩ = p ⟨i - 2, by omega⟩ := by
          by_cases hlt' : i - 2 < s
          · exact tjP_lt x p (i := ⟨i - 2, by omega⟩) (by dsimp only; exact hlt')
          · exact tjP_odd x p (i := ⟨i - 2, by omega⟩) (by
              dsimp only; rcases hodd with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩)
        have hl_im2 : tjL s x l ⟨i - 2, by omega⟩ = l ⟨i - 2, by omega⟩ := by
          by_cases hlt' : i - 2 < s
          · exact tjL_lt x l (i := ⟨i - 2, by omega⟩) (by dsimp only; exact hlt')
          · exact tjL_odd x l (i := ⟨i - 2, by omega⟩) (by
              dsimp only; rcases hodd with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩)
        rw [hpi, hli, hp0, hl0, hp_im2, hl_im2]
        exact ei
      · have hev : Even (i - s) := Nat.not_odd_iff_even.1 hodd
        by_cases hsmod : (s + 1) % 4 = 0 ∨ (s + 1) % 4 = 1
        · by_cases hi2 : i = s + 2
          · subst hi2
            have himod : ¬ ((s + 2 + 1) % 4 = 0 ∨ (s + 2 + 1) % 4 = 1) := by omega
            simp only [himod, ite_false] at ei ⊢
            have hpi : tjP s x p ⟨s + 2, hi⟩ = p ⟨s + 2, hi⟩ - p ⟨0, hm⟩ * x := by
              simp [tjP, hsmod]
            have hli : tjL s x l ⟨s + 2, hi⟩ = l ⟨s + 2, hi⟩ := by
              simp [tjL, hsmod]
            have hls : tjL s x l ⟨s, by omega⟩ = l ⟨s, by omega⟩ - x := by
              simp [tjL, hsmod]
            have hsub : s + 2 - 2 = s := by omega
            simp only [hsub] at ei ⊢
            rw [hpi, hli, hp0, hls]; linear_combination ei
          · by_cases hi4 : i = s + 4
            · subst hi4
              have himod : (s + 4 + 1) % 4 = 0 ∨ (s + 4 + 1) % 4 = 1 := by omega
              simp only [himod, ite_true] at ei ⊢
              have hpi : tjP s x p ⟨s + 4, hi⟩ = p ⟨s + 4, hi⟩ - p ⟨1, by omega⟩ * x := by
                simp [tjP, hsmod]
              have hli : tjL s x l ⟨s + 4, hi⟩ = l ⟨s + 4, hi⟩ - l ⟨1, by omega⟩ * x := by
                simp [tjL, hsmod]
              have hpm2 : tjP s x p ⟨s + 2, by omega⟩ =
                  p ⟨s + 2, by omega⟩ - p ⟨0, hm⟩ * x := by
                simp [tjP, hsmod]
              have e1 := h ⟨1, by omega⟩ (by dsimp only; omega)
              simp only [rhsD, hm, ↓reduceDIte] at e1
              have hsub : s + 4 - 2 = s + 2 := by omega
              simp only [hsub] at ei ⊢
              rw [hpi, hli, hpm2, hl0]; linear_combination ei - x * e1
            · have hi6 : s + 6 ≤ i := by rcases hev with ⟨t, ht⟩; omega
              have hpi : tjP s x p ⟨i, hi⟩ = p ⟨i, hi⟩ - p ⟨i - s - 4, by omega⟩ * x := by
                simp [tjP, hsmod, show i ≠ s by omega, hi2, hi4, hi6, hev]
              have hli : tjL s x l ⟨i, hi⟩ = l ⟨i, hi⟩ - l ⟨i - s - 4, by omega⟩ * x := by
                simp [tjL, hsmod, show i ≠ s by omega, hi4, hi6, hev]
              have er := h ⟨i - s - 4, by omega⟩ (by dsimp only; omega)
              by_cases hi6_eq : i = s + 6
              · subst hi6_eq
                have himod : ¬ ((s + 6 + 1) % 4 = 0 ∨ (s + 6 + 1) % 4 = 1) := by omega
                simp only [himod, ite_false] at ei ⊢
                have hlm2 : tjL s x l ⟨s + 4, by omega⟩ =
                    l ⟨s + 4, by omega⟩ - l ⟨1, by omega⟩ * x := by
                  simp [tjL, hsmod]
                have hsub1 : s + 6 - 2 = s + 4 := by omega
                have hsub2 : s + 6 - s - 4 = 2 := by omega
                simp only [hsub1] at ei ⊢
                simp only [hsub2] at hpi hli er
                simp only [rhsD, hm, ↓reduceDIte] at er
                norm_num at er
                rw [hpi, hli, hp0, hlm2]; linear_combination ei - x * er
              · have hi8 : s + 8 ≤ i := by rcases hev with ⟨t, ht⟩; omega
                have hev_m2 : Even (i - 2 - s) := by rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
                have hpm2 : tjP s x p ⟨i - 2, by omega⟩ =
                    p ⟨i - 2, by omega⟩ - p ⟨i - s - 6, by omega⟩ * x := by
                  have hsub : i - 2 - s - 4 = i - s - 6 := by omega
                  simp [tjP, hsmod, show i - 2 ≠ s by omega,
                    show i - 2 ≠ s + 2 by omega, show i - 2 ≠ s + 4 by omega,
                    show s + 6 ≤ i - 2 by omega, hev_m2, hsub]
                have hlm2 : tjL s x l ⟨i - 2, by omega⟩ =
                    l ⟨i - 2, by omega⟩ - l ⟨i - s - 6, by omega⟩ * x := by
                  have hsub : i - 2 - s - 4 = i - s - 6 := by omega
                  simp [tjL, hsmod, show i - 2 ≠ s by omega,
                    show i - 2 ≠ s + 4 by omega,
                    show s + 6 ≤ i - 2 by omega, hev_m2, hsub]
                simp only [rhsD, hm, ↓reduceDIte, show i - s - 4 ≠ 1 by omega,
                  show i - s - 4 ≠ 2 by omega, show 3 ≤ i - s - 4 by omega] at er
                have hsub_r : i - s - 4 - 2 = i - s - 6 := by omega
                simp only [hsub_r] at er
                have hmod_iff : ((i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1) ↔
                    ((i - s - 4 + 1) % 4 = 0 ∨ (i - s - 4 + 1) % 4 = 1) := by
                  rcases hev with ⟨t, ht⟩; omega
                rw [hpi, hli, hp0, hl0, hpm2, hlm2]
                by_cases himod : (i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1
                · have hrmod := hmod_iff.1 himod
                  simp only [himod, hrmod, ite_true] at ei er ⊢
                  linear_combination ei - x * er
                · have hrmod : ¬ ((i - s - 4 + 1) % 4 = 0 ∨ (i - s - 4 + 1) % 4 = 1) :=
                    fun h' => himod (hmod_iff.2 h')
                  simp only [himod, hrmod, ite_false] at ei er ⊢
                  linear_combination ei - x * er
        · by_cases hi2 : i = s + 2
          · subst hi2
            have himod : (s + 2 + 1) % 4 = 0 ∨ (s + 2 + 1) % 4 = 1 := by omega
            simp only [himod, ite_true] at ei ⊢
            have hpi : tjP s x p ⟨s + 2, hi⟩ = p ⟨s + 2, hi⟩ := by
              simp [tjP, hsmod]
            have hli : tjL s x l ⟨s + 2, hi⟩ = l ⟨s + 2, hi⟩ + l ⟨0, hm⟩ * x := by
              simp [tjL, hsmod]
            have hps : tjP s x p ⟨s, by omega⟩ = p ⟨s, by omega⟩ + x := by
              simp [tjP, hsmod]
            have hsub : s + 2 - 2 = s := by omega
            simp only [hsub] at ei ⊢
            rw [hpi, hli, hps, hl0]; linear_combination ei
          · have hi4 : s + 4 ≤ i := by rcases hev with ⟨t, ht⟩; omega
            have hpi : tjP s x p ⟨i, hi⟩ = p ⟨i, hi⟩ + p ⟨i - s - 3, by omega⟩ * x := by
              simp [tjP, hsmod, show i ≠ s by omega, hi4, hev]
            have hli : tjL s x l ⟨i, hi⟩ = l ⟨i, hi⟩ + l ⟨i - s - 3, by omega⟩ * x := by
              simp [tjL, hsmod, show i ≠ s by omega, hi2, hi4, hev]
            have er := h ⟨i - s - 3, by omega⟩ (by dsimp only; omega)
            by_cases hi4_eq : i = s + 4
            · subst hi4_eq
              have himod : ¬ ((s + 4 + 1) % 4 = 0 ∨ (s + 4 + 1) % 4 = 1) := by omega
              simp only [himod, ite_false] at ei ⊢
              have hlm2 : tjL s x l ⟨s + 2, by omega⟩ =
                  l ⟨s + 2, by omega⟩ + l ⟨0, hm⟩ * x := by
                simp [tjL, hsmod]
              have hsub1 : s + 4 - 2 = s + 2 := by omega
              have hsub2 : s + 4 - s - 3 = 1 := by omega
              simp only [hsub1] at ei ⊢
              simp only [hsub2] at hpi hli er
              simp only [rhsD, hm, ↓reduceDIte] at er
              rw [hpi, hli, hp0, hlm2]; linear_combination ei + x * er
            · have hi6 : s + 6 ≤ i := by rcases hev with ⟨t, ht⟩; omega
              have hev_m2 : Even (i - 2 - s) := by rcases hev with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
              have hpm2 : tjP s x p ⟨i - 2, by omega⟩ =
                  p ⟨i - 2, by omega⟩ + p ⟨i - s - 5, by omega⟩ * x := by
                have hsub : i - 2 - s - 3 = i - s - 5 := by omega
                simp [tjP, hsmod, show i - 2 ≠ s by omega,
                  show s + 4 ≤ i - 2 by omega, hev_m2, hsub]
              have hlm2 : tjL s x l ⟨i - 2, by omega⟩ =
                  l ⟨i - 2, by omega⟩ + l ⟨i - s - 5, by omega⟩ * x := by
                have hsub : i - 2 - s - 3 = i - s - 5 := by omega
                simp [tjL, hsmod, show i - 2 ≠ s by omega,
                  show i - 2 ≠ s + 2 by omega,
                  show s + 4 ≤ i - 2 by omega, hev_m2, hsub]
              simp only [rhsD, hm, ↓reduceDIte, show i - s - 3 ≠ 1 by omega,
                show i - s - 3 ≠ 2 by omega, show 3 ≤ i - s - 3 by omega] at er
              have hsub_r : i - s - 3 - 2 = i - s - 5 := by omega
              simp only [hsub_r] at er
              have hmod_iff : ((i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1) ↔
                  ((i - s - 3 + 1) % 4 = 0 ∨ (i - s - 3 + 1) % 4 = 1) := by
                rcases hev with ⟨t, ht⟩; omega
              rw [hpi, hli, hp0, hl0, hpm2, hlm2]
              by_cases himod : (i + 1) % 4 = 0 ∨ (i + 1) % 4 = 1
              · have hrmod := hmod_iff.1 himod
                simp only [himod, hrmod, ite_true] at ei er ⊢
                linear_combination ei + x * er
              · have hrmod : ¬ ((i - s - 3 + 1) % 4 = 0 ∨ (i - s - 3 + 1) % 4 = 1) :=
                  fun h' => himod (hmod_iff.2 h')
                simp only [himod, hrmod, ite_false] at ei er ⊢
                linear_combination ei + x * er

/-- Point transitivity of `D(m, F)`: for any point `p₀`, there is an adjacency-preserving map
`(fp, fl)` sending `p₀ ↦ 0` and preserving distinctness of first coordinates on both sides. -/
theorem exists_shift_to_zero_D {m : ℕ} {F : Type*} [CommRing F] (p₀ : Fin m → F) :
    ∃ (fp fl : (Fin m → F) → (Fin m → F)),
      (∀ p l, PLAdj m F p l → PLAdj m F (fp p) (fl l)) ∧
      fp p₀ = 0 ∧
      (∀ (hm : 0 < m) (p₁ p₂ : Fin m → F), p₁ ⟨0, hm⟩ ≠ p₂ ⟨0, hm⟩ →
        fp p₁ ⟨0, hm⟩ ≠ fp p₂ ⟨0, hm⟩) ∧
      (∀ (hm : 0 < m) (l₁ l₂ : Fin m → F), l₁ ⟨0, hm⟩ ≠ l₂ ⟨0, hm⟩ →
        fl l₁ ⟨0, hm⟩ ≠ fl l₂ ⟨0, hm⟩) := by
  have hprefix : ∀ d, d ≤ m →
      ∃ (fp fl : (Fin m → F) → (Fin m → F)),
        (∀ p l, PLAdj m F p l → PLAdj m F (fp p) (fl l)) ∧
        (∀ j : Fin m, j.val < d → fp p₀ j = 0) ∧
        (∀ (hm : 0 < m) (p₁ p₂ : Fin m → F), p₁ ⟨0, hm⟩ ≠ p₂ ⟨0, hm⟩ →
          fp p₁ ⟨0, hm⟩ ≠ fp p₂ ⟨0, hm⟩) ∧
        (∀ (hm : 0 < m) (l₁ l₂ : Fin m → F), l₁ ⟨0, hm⟩ ≠ l₂ ⟨0, hm⟩ →
          fl l₁ ⟨0, hm⟩ ≠ fl l₂ ⟨0, hm⟩) := by
    intro d hd
    induction d with
    | zero =>
      exact ⟨id, id, fun _ _ h => h, fun _ hlt => by omega, fun _ _ _ h => h, fun _ _ _ h => h⟩
    | succ d ih =>
      rcases ih (by omega) with ⟨fp, fl, hadj, hzero, hfp0, hfl0⟩
      by_cases hd0 : d = 0
      · subst hd0
        let x := -(fp p₀ ⟨0, by omega⟩)
        refine ⟨t0P x ∘ fp, t0L x ∘ fl, fun p l h => t0_preserves_PLAdj x (hadj p l h), ?_, ?_, ?_⟩
        · intro ⟨j, hjlt⟩ hj
          dsimp only at hj
          have hjeq : (⟨j, hjlt⟩ : Fin m) = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hjeq]
          simp [x, t0P_zero]
        · intro hm p₁ p₂ hne heq
          simp only [Function.comp_apply, t0P_zero] at heq
          exact hfp0 hm p₁ p₂ hne (add_right_cancel heq)
        · intro hm l₁ l₂ hne heq
          simp only [Function.comp_apply, t0L_zero] at heq
          exact hfl0 hm l₁ l₂ hne heq
      · by_cases hd1 : d = 1
        · subst hd1
          let x := -(fp p₀ ⟨1, by omega⟩)
          refine ⟨t2P x ∘ fp, t2L x ∘ fl, fun p l h => t2_preserves_PLAdj x (hadj p l h), ?_, ?_, ?_⟩
          · intro ⟨j, hjlt⟩ hj
            dsimp only at hj
            rcases Nat.eq_zero_or_pos j with rfl | hj1
            · simp only [Function.comp_apply, t2P_zero]
              exact hzero ⟨0, hjlt⟩ (by dsimp only; omega)
            · have hjeq : (⟨j, hjlt⟩ : Fin m) = ⟨1, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hjeq]
              simp [x, t2P_one]
          · intro hm p₁ p₂ hne heq
            simp only [Function.comp_apply, t2P_zero] at heq
            exact hfp0 hm p₁ p₂ hne heq
          · intro hm l₁ l₂ hne heq
            simp only [Function.comp_apply, t2L_zero] at heq
            exact hfl0 hm l₁ l₂ hne heq
        · have hd2 : 2 ≤ d := by omega
          let x := -(fp p₀ ⟨d, by omega⟩)
          refine ⟨tjP d x ∘ fp, tjL d x ∘ fl,
            fun p l h => tj_preserves_PLAdj hd2 x (hadj p l h), ?_, ?_, ?_⟩
          · intro ⟨j, hjlt⟩ hj
            dsimp only at hj
            by_cases hlt : j < d
            · simp only [Function.comp_apply]
              rw [tjP_lt x (fp p₀) (i := ⟨j, hjlt⟩) (by dsimp only; exact hlt)]
              exact hzero ⟨j, hjlt⟩ (by dsimp only; exact hlt)
            · have hjeq : (⟨j, hjlt⟩ : Fin m) = ⟨d, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hjeq]
              simp only [Function.comp_apply, tjP_self d (by omega) x (fp p₀), x, add_neg_cancel]
          · intro hm p₁ p₂ hne heq
            simp only [Function.comp_apply] at heq
            rw [tjP_lt x (fp p₁) (i := ⟨0, hm⟩) (by dsimp only; omega),
              tjP_lt x (fp p₂) (i := ⟨0, hm⟩) (by dsimp only; omega)] at heq
            exact hfp0 hm p₁ p₂ hne heq
          · intro hm l₁ l₂ hne heq
            simp only [Function.comp_apply] at heq
            rw [tjL_lt x (fl l₁) (i := ⟨0, hm⟩) (by dsimp only; omega),
              tjL_lt x (fl l₂) (i := ⟨0, hm⟩) (by dsimp only; omega)] at heq
            exact hfl0 hm l₁ l₂ hne heq
  rcases hprefix m le_rfl with ⟨fp, fl, hadj, hzero, hfp0, hfl0⟩
  exact ⟨fp, fl, hadj, funext fun j => hzero j j.isLt, hfp0, hfl0⟩

/-! ### Part 4: Unconditional Lazebnik–Ustimenko Theorem 45 -/

/-- Helper: given any simple cycle of length `2 r` (`2 ≤ r`) in `D(m, F)` (`m > 0`), there is an
alternating point/line sequence `u : Fin (2 r) → Fin m → F` starting at `u 0 = 0`, satisfying
`PLAdj m F` on every edge, and non-backtracking on first coordinates. -/
lemma cycle_to_zero_walk_D {m r : ℕ} {F : Type*} [CommRing F] (hm : 0 < m) (hr2 : 2 ≤ r)
    (hc : HasCycleOfLen (DGraph m F) (2 * r)) :
    ∃ u : Fin (2 * r) → Fin m → F,
      u ⟨0, by omega⟩ = 0 ∧
      (∀ i : Fin (2 * r),
        if Even i.val then
          PLAdj m F (u i) (u ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩)
        else
          PLAdj m F (u ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩) (u i)) ∧
      (∀ i : Fin (2 * r),
        u i ⟨0, hm⟩ ≠ u ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩ ⟨0, hm⟩) := by
  rcases hc with ⟨_, v, hinj, hadj⟩
  have hshift : ∃ v' : Fin (2 * r) → Vertex m F,
      Function.Injective v' ∧
      (∀ i : Fin (2 * r), (DGraph m F).Adj (v' i) (v' ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩)) ∧
      (v' ⟨0, by omega⟩).isLeft = true := by
    cases hv0 : v ⟨0, by omega⟩ with
    | inl p => exact ⟨v, hinj, hadj, by simp [hv0]⟩
    | inr l =>
      let v' : Fin (2 * r) → Vertex m F := fun i => v ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩
      refine ⟨v', ?_, ?_, ?_⟩
      · intro i j heq
        have h1 := congrArg Fin.val (hinj heq)
        dsimp only at h1
        have hi := i.isLt
        have hj := j.isLt
        apply Fin.ext
        by_cases hlt1 : i.val + 1 < 2 * r <;> by_cases hlt2 : j.val + 1 < 2 * r
        · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at h1; omega
        · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)] at h1; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt hlt2] at h1; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
      · intro i
        have hmod2 : (((i.val + 1) % (2 * r)) + 1) % (2 * r) = (i.val + 2) % (2 * r) := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hstep := hadj ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩
        simpa only [v', hmod2] using hstep
      · have hadj0 := hadj ⟨0, by omega⟩
        rw [hv0] at hadj0
        have h1 : (0 + 1) % (2 * r) = 1 := Nat.mod_eq_of_lt (by omega)
        simp only [v', h1]
        cases hv1 : v ⟨1, by omega⟩ with
        | inl p => rfl
        | inr l' =>
          simp only [h1, hv1] at hadj0
          exact False.elim hadj0
  rcases hshift with ⟨v', hinj', hadj', hleft0⟩
  have hpar : ∀ i : Fin (2 * r), (v' i).isLeft = decide (Even i.val) := by
    intro ⟨i, hi⟩
    induction i with
    | zero => simpa using hleft0
    | succ i ih =>
      have hprev := ih (by omega)
      have hstep := hadj' ⟨i, by omega⟩
      have hmod : (i + 1) % (2 * r) = i + 1 := Nat.mod_eq_of_lt hi
      simp only [hmod] at hstep
      cases hu : v' ⟨i, by omega⟩ <;> cases hw : v' ⟨i + 1, hi⟩
      · rw [hu, hw] at hstep; exact False.elim hstep
      · simp only [hu, Sum.isLeft_inl] at hprev
        have he : Even i := of_decide_eq_true hprev.symm
        have hno : ¬ Even (i + 1) := by rcases he with ⟨t, rfl⟩; intro ⟨t', ht'⟩; omega
        simp [hno]
      · simp only [hu, Sum.isLeft_inr] at hprev
        have hno : ¬ Even i := of_decide_eq_false hprev.symm
        have he : Even (i + 1) := by
          rcases Nat.not_even_iff_odd.1 hno with ⟨t, rfl⟩; exact ⟨t + 1, by omega⟩
        simp [he]
      · rw [hu, hw] at hstep; exact False.elim hstep
  cases hp0 : v' ⟨0, by omega⟩ with
  | inr l => simp [hp0] at hleft0
  | inl p₀ =>
    rcases exists_shift_to_zero_D p₀ with ⟨fp, fl, hpres, hfp0, hfp_inj, hfl_inj⟩
    let extract : Vertex m F → Fin m → F
      | Sum.inl p => fp p
      | Sum.inr l => fl l
    refine ⟨fun i => extract (v' i), by simp [extract, hp0, hfp0], ?_, ?_⟩
    · intro i
      have hstep := hadj' i
      have hpi := hpar i
      by_cases hei : Even i.val
      · simp only [hei, ite_true]
        simp only [hei, decide_true] at hpi
        cases hu : v' i with
        | inr _ => simp [hu] at hpi
        | inl p =>
          cases hw : v' ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩ with
          | inl _ =>
            rw [hu, hw] at hstep; exact False.elim hstep
          | inr l =>
            rw [hu, hw] at hstep
            exact hpres p l hstep
      · simp only [hei, ite_false]
        simp only [hei, decide_false] at hpi
        cases hu : v' i with
        | inl _ => simp [hu] at hpi
        | inr l =>
          cases hw : v' ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩ with
          | inr _ =>
            rw [hu, hw] at hstep; exact False.elim hstep
          | inl p =>
            rw [hu, hw] at hstep
            exact hpres p l hstep
    · intro i
      have hne_v : v' i ≠ v' ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩ := by
        intro heq
        have hval := congrArg Fin.val (hinj' heq)
        dsimp only at hval
        have hi := i.isLt
        by_cases hlt2 : i.val + 2 < 2 * r
        · rw [Nat.mod_eq_of_lt hlt2] at hval; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval; omega
      have h1 : (DGraph m F).Adj (v' ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩) (v' i) :=
        (DGraph m F).adj_symm (hadj' i)
      have h2 : (DGraph m F).Adj (v' ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩)
          (v' ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩) := by
        have hmod : (((i.val + 1) % (2 * r)) + 1) % (2 * r) = (i.val + 2) % (2 * r) := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        simpa only [hmod] using hadj' ⟨(i.val + 1) % (2 * r), Nat.mod_lt _ (by omega)⟩
      have hfc_ne : firstCoord hm (v' i) ≠
          firstCoord hm (v' ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩) :=
        fun hfc => hne_v (unique_neighbor_of_firstCoord hm h1 h2 hfc)
      have hpi := hpar i
      have hpi2 := hpar ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩
      have hpar2 : Even ((i.val + 2) % (2 * r)) ↔ Even i.val := by
        have hi := i.isLt
        by_cases hlt : i.val + 2 < 2 * r
        · rw [Nat.mod_eq_of_lt hlt]
          constructor
          · rintro ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
          · rintro ⟨t, ht⟩; exact ⟨t + 1, by omega⟩
        · have hsub : (i.val + 2) % (2 * r) = i.val + 2 - 2 * r := by
            rw [Nat.mod_eq_sub_mod (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hsub]
          constructor
          · rintro ⟨t, ht⟩; exact ⟨t + r - 1, by omega⟩
          · rintro ⟨t, ht⟩; exact ⟨t + 1 - r, by omega⟩
      cases hu : v' i with
      | inl p₁ =>
        simp only [hu, Sum.isLeft_inl] at hpi
        have hei : Even i.val := of_decide_eq_true hpi.symm
        have hei2 : Even ((i.val + 2) % (2 * r)) := hpar2.2 hei
        simp only [hei2, decide_true] at hpi2
        cases hw : v' ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩ with
        | inr _ => simp [hw] at hpi2
        | inl p₂ =>
          simp only [hu, hw, firstCoord] at hfc_ne
          dsimp only
          rw [hu, hw]
          exact hfp_inj hm p₁ p₂ hfc_ne
      | inr l₁ =>
        simp only [hu, Sum.isLeft_inr] at hpi
        have hno : ¬ Even i.val := of_decide_eq_false hpi.symm
        have hno2 : ¬ Even ((i.val + 2) % (2 * r)) := fun h' => hno (hpar2.1 h')
        simp only [hno2, decide_false] at hpi2
        cases hw : v' ⟨(i.val + 2) % (2 * r), Nat.mod_lt _ (by omega)⟩ with
        | inl _ => simp [hw] at hpi2
        | inr l₂ =>
          simp only [hu, hw, firstCoord] at hfc_ne
          dsimp only
          rw [hu, hw]
          exact hfl_inj hm l₁ l₂ hfc_ne

/-- Unconditional Lazebnik–Ustimenko lower bound for odd `m = 2 k + 1 ≥ 3`:
`girth D(2 k + 1, F) ≥ 2 k + 6` over every integral domain `F`. -/
theorem D_odd_girthAtLeast {k : ℕ} (hk : 1 ≤ k) (F : Type*) [CommRing F] [IsDomain F] :
    GirthAtLeast (DGraph (2 * k + 1) F) (2 * k + 6) := by
  intro L hL3 hLlt hc
  rcases even_cycle_len_D hc with ⟨r, hr⟩
  have hL_eq : L = 2 * r := by omega
  subst hL_eq
  have hr2 : 2 ≤ r := by omega
  have hrk : r ≤ k + 2 := by omega
  rcases cycle_to_zero_walk_D (by omega) hr2 hc with ⟨u, hu0, huadj, hunb⟩
  apply no_closed_nb_walk_zero_A (n := k + 2) (r := r) hr2 hrk
    (fun i => u i ∘ idxDtoA k hk)
  · funext j; simp [hu0]
  · intro i
    have h := huadj i
    split_ifs at h ⊢
    · exact projDtoA_plAdj hk h
    · exact projDtoA_plAdj hk h
  · intro i
    have h0idx : idxDtoA k hk ⟨0, by omega⟩ = ⟨0, by omega⟩ := by simp [idxDtoA]
    simpa only [Function.comp_apply, h0idx] using hunb i

/-- Unconditional lower bound `girth D(2, F) ≥ 6` over every integral domain `F`. -/
theorem D_two_girthAtLeast (F : Type*) [CommRing F] [IsDomain F] :
    GirthAtLeast (DGraph 2 F) 6 := by
  intro L hL3 hLlt hc
  rcases even_cycle_len_D hc with ⟨r, hr⟩
  have hL_eq : L = 2 * r := by omega
  subst hL_eq
  have hr2 : 2 ≤ r := by omega
  have hrle : r ≤ 2 := by omega
  rcases cycle_to_zero_walk_D (by omega) hr2 hc with ⟨u, hu0, huadj, hunb⟩
  apply no_closed_nb_walk_zero_A (n := 2) (r := r) hr2 hrle u hu0
  · intro i
    have h := huadj i
    split_ifs at h ⊢
    · exact plAdj2_to_plAdjA2 h
    · exact plAdj2_to_plAdjA2 h
  · exact hunb

/-- Unconditional Lazebnik–Ustimenko lower bound for even `m = 2 k ≥ 2`:
`girth D(2 k, F) ≥ 2 k + 4` over every integral domain `F`. -/
theorem D_even_girthAtLeast {k : ℕ} (hk : 1 ≤ k) (F : Type*) [CommRing F] [IsDomain F] :
    GirthAtLeast (DGraph (2 * k) F) (2 * k + 4) := by
  by_cases hk1 : k = 1
  · subst hk1; exact D_two_girthAtLeast F
  · have hkm1 : 1 ≤ k - 1 := by omega
    have hodd := D_odd_girthAtLeast hkm1 F
    have heq1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have heq2 : 2 * (k - 1) + 6 = 2 * k + 4 := by omega
    rw [heq1, heq2] at hodd
    exact girthAtLeast_of_le (by omega) (by omega) hodd

/-- Unified Lazebnik–Ustimenko Theorem 45 (1995; DS28 Section 6.3):
for every `m ≥ 2` and every integral domain `F`,
`girth D(m, F) ≥ m + 5` (odd `m`) and `girth D(m, F) ≥ m + 4` (even `m`). -/
theorem D_girthAtLeast_LU {m : ℕ} (hm : 2 ≤ m) (F : Type*) [CommRing F] [IsDomain F] :
    GirthAtLeast (DGraph m F) (if Odd m then m + 5 else m + 4) := by
  by_cases ho : Odd m
  · rcases ho with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    simp only [show Odd (2 * k + 1) from ⟨k, rfl⟩, ite_true]
    have h := D_odd_girthAtLeast hk F
    have heq : 2 * k + 1 + 5 = 2 * k + 6 := by omega
    rw [heq]; exact h
  · rcases Nat.not_odd_iff_even.1 ho with ⟨k, rfl⟩
    have hm_eq : k + k = 2 * k := by omega
    rw [hm_eq]
    have hk : 1 ≤ k := by omega
    have hno : ¬ Odd (2 * k) := by rw [← hm_eq]; exact ho
    simp only [hno, ite_false]
    exact D_even_girthAtLeast hk F

/-- Unconditional lower bound `girth D(9, F) ≥ 14` over every integral domain `F`. -/
theorem D9_girthAtLeast_14 (F : Type*) [CommRing F] [IsDomain F] :
    GirthAtLeast (DGraph 9 F) 14 :=
  D_odd_girthAtLeast (k := 4) (by omega) F

/-- Unconditional lower bound `girth D(10, F) ≥ 14` over every integral domain `F`. -/
theorem D10_girthAtLeast_14 (F : Type*) [CommRing F] [IsDomain F] :
    GirthAtLeast (DGraph 10 F) 14 :=
  D_even_girthAtLeast (k := 5) (by omega) F

end LazebnikUstimenko
