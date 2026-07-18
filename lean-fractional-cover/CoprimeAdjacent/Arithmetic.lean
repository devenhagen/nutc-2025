import CoprimeAdjacent.Core

/-!
# Exact finite-`k` arithmetic for the fractional-cover bound

This file uses `binomPrefix k r = ∑_{j<r} k.choose j`.  Indexing by the
number of terms, rather than by the largest index, makes the cases `k=3,4,5`
work without a separate convention for negative upper summation limits.
-/

open scoped BigOperators

namespace CoprimeAdjacent

/-- The first `r` entries of row `k` of Pascal's triangle. -/
def binomPrefix (k r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, Nat.choose k j

@[simp] theorem binomPrefix_zero (k : ℕ) : binomPrefix k 0 = 0 := by
  simp [binomPrefix]

@[simp] theorem binomPrefix_succ (k r : ℕ) :
    binomPrefix k (r + 1) = binomPrefix k r + Nat.choose k r := by
  simp [binomPrefix, Finset.sum_range_succ]

/-- The Ross hard-cutoff bound, with the empty-tail convention built into
natural-number subtraction. -/
def cutoffBound (k t : ℕ) : ℕ :=
  2 * binomPrefix k (t + 1) + binomPrefix k (k - (2 * t + 1))

/-- Fractional-cover value in the residue class `k=3m`. -/
def Uzero (m : ℕ) : ℚ :=
  3 * (binomPrefix (3 * m) (m - 1) : ℚ)
    + 2 * (Nat.choose (3 * m) (m - 1) : ℚ)
    + (Nat.choose (3 * m) m : ℚ)

/-- Fractional-cover value in the residue class `k=3m+1`. -/
def Uone (m : ℕ) : ℚ :=
  3 * (binomPrefix (3 * m + 1) m : ℚ)
    + (3 / 2 : ℚ) * (Nat.choose (3 * m + 1) m : ℚ)

/-- Fractional-cover value in the residue class `k=3m+2`. -/
def Utwo (m : ℕ) : ℚ :=
  3 * (binomPrefix (3 * m + 2) (m - 1) : ℚ)
    + (9 / 4 : ℚ) * (Nat.choose (3 * m + 2) (m - 1) : ℚ)
    + (3 / 2 : ℚ) * (Nat.choose (3 * m + 2) m : ℚ)
    + (3 / 4 : ℚ) * (Nat.choose (3 * m + 2) (m + 1) : ℚ)

/-- The distinguished cutoff in residue class `0 mod 3`. -/
def cutoffZero (m : ℕ) : ℕ := cutoffBound (3 * m) (m - 1)

/-- The distinguished cutoff in residue class `1 mod 3`. -/
def cutoffOne (m : ℕ) : ℕ := cutoffBound (3 * m + 1) m

/-- The distinguished cutoff in residue class `2 mod 3`. -/
def cutoffTwo (m : ℕ) : ℕ := cutoffBound (3 * m + 2) m

/-- Closed form of the old cutoff at `t=m-1` when `k=3m`. -/
theorem cutoffZero_eq (m : ℕ) (hm : 1 ≤ m) :
    cutoffZero m =
      3 * binomPrefix (3 * m) m + Nat.choose (3 * m) m := by
  have hsub : 3 * m - (2 * (m - 1) + 1) = m + 1 := by omega
  have hmstep : m - 1 + 1 = m := by omega
  unfold cutoffZero cutoffBound
  rw [hsub, hmstep, binomPrefix_succ]
  omega

/-- Closed form of the old cutoff at `t=m` when `k=3m+1`. -/
theorem cutoffOne_eq (m : ℕ) :
    cutoffOne m =
      3 * binomPrefix (3 * m + 1) m
        + 2 * Nat.choose (3 * m + 1) m := by
  have hsub : 3 * m + 1 - (2 * m + 1) = m := by omega
  simp [cutoffOne, cutoffBound, hsub, binomPrefix_succ]
  omega

/-- Closed form of the old cutoff at `t=m` when `k=3m+2`. -/
theorem cutoffTwo_eq (m : ℕ) :
    cutoffTwo m = 3 * binomPrefix (3 * m + 2) (m + 1) := by
  have hsub : 3 * m + 2 - (2 * m + 1) = m + 1 := by omega
  simp [cutoffTwo, cutoffBound, hsub]
  omega

/-- The binomial identity used in the `3m+2` gap calculation. -/
theorem choose_three_mul_add_two_succ (m : ℕ) :
    Nat.choose (3 * m + 2) (m + 1) =
      2 * Nat.choose (3 * m + 2) m := by
  have h := Nat.choose_succ_right_eq (3 * m + 2) m
  have hsub : 3 * m + 2 - m = 2 * (m + 1) := by omega
  rw [hsub] at h
  have h' : Nat.choose (3 * m + 2) (m + 1) * (m + 1) =
      (2 * Nat.choose (3 * m + 2) m) * (m + 1) := by
    calc
      Nat.choose (3 * m + 2) (m + 1) * (m + 1) =
          Nat.choose (3 * m + 2) m * (2 * (m + 1)) := h
      _ = (2 * Nat.choose (3 * m + 2) m) * (m + 1) := by ring
  exact Nat.mul_right_cancel (by omega : 0 < m + 1) h'

/-- Exact gap in residue class `0 mod 3`. -/
theorem cutoffZero_sub_Uzero (m : ℕ) (hm : 1 ≤ m) :
    (cutoffZero m : ℚ) - Uzero m =
      (Nat.choose (3 * m) (m - 1) : ℚ) := by
  rw [cutoffZero_eq m hm]
  have hp := binomPrefix_succ (3 * m) (m - 1)
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1] at hp
  rw [hp]
  norm_num [Uzero]
  ring

/-- Exact gap in residue class `1 mod 3`. -/
theorem cutoffOne_sub_Uone (m : ℕ) :
    (cutoffOne m : ℚ) - Uone m =
      (1 / 2 : ℚ) * (Nat.choose (3 * m + 1) m : ℚ) := by
  rw [cutoffOne_eq]
  norm_num [Uone]
  ring

/-- Exact gap in residue class `2 mod 3`. -/
theorem cutoffTwo_sub_Utwo (m : ℕ) (hm : 1 ≤ m) :
    (cutoffTwo m : ℚ) - Utwo m =
      (3 / 4 : ℚ) * (Nat.choose (3 * m + 2) (m - 1) : ℚ) := by
  rw [cutoffTwo_eq]
  have hp0 := binomPrefix_succ (3 * m + 2) (m - 1)
  have hm1 : m - 1 + 1 = m := by omega
  rw [hm1] at hp0
  have hp1 := binomPrefix_succ (3 * m + 2) m
  rw [hp1, hp0]
  unfold Utwo
  rw [choose_three_mul_add_two_succ]
  norm_num
  ring

/-- A positive rational gap below an integral bound gives the one-unit
integer improvement directly, without invoking floor machinery. -/
theorem nat_le_pred_of_cast_le_of_lt
    {e b : ℕ} {u : ℚ} (he : (e : ℚ) ≤ u) (hu : u < b) :
    e ≤ b - 1 := by
  have heb : e < b := by exact_mod_cast he.trans_lt hu
  omega

end CoprimeAdjacent
