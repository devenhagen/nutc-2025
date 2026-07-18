import CoprimeAdjacent.Arithmetic

/-!
# Evaluation of the clipped ramp in the three residue classes
-/

open scoped BigOperators

namespace CoprimeAdjacent

section ClipHelpers

variable {R : Type*} [LinearOrderedField R]

@[simp] theorem clip01_eq_self {x : R} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    clip01 x = x := by
  simp [clip01, max_eq_right h0, min_eq_right h1]

@[simp] theorem clip01_eq_zero_of_le_zero {x : R} (hx : x ≤ 0) :
    clip01 x = 0 := by
  simp [clip01, max_eq_left hx]

end ClipHelpers

/-- The unmultiplied binomial mass of a natural-number ramp. -/
def rampMass (k L : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1),
    (Nat.choose k j : ℚ) * rampNat k L j

/-- Truncate a range sum when every term past `r` vanishes. -/
theorem sum_range_eq_sum_range_of_zero_from
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) {r n : ℕ}
    (hrn : r ≤ n) (hz : ∀ j, r ≤ j → f j = 0) :
    (∑ j ∈ Finset.range n, f j) = ∑ j ∈ Finset.range r, f j := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hrn
  rw [Finset.sum_range_add]
  simp [hz]

/-! ## `k = 3m` -/

private theorem ramp_zero_raw (m j : ℕ) :
    rampNat (3 * m) (m + 1) j =
      clip01 (((m : ℚ) + 1 - (j : ℚ)) / 3) := by
  unfold rampNat ramp
  congr 1
  push_cast
  ring

private theorem ramp_zero_low {m j : ℕ} (h : j < m - 1) :
    rampNat (3 * m) (m + 1) j = 1 := by
  rw [ramp_zero_raw]
  apply clip01_eq_one_of_one_le
  have hj : j + 2 ≤ m := by omega
  have hjq : (j : ℚ) + 2 ≤ (m : ℚ) := by exact_mod_cast hj
  linarith

private theorem ramp_zero_pred (m : ℕ) (hm : 1 ≤ m) :
    rampNat (3 * m) (m + 1) (m - 1) = 2 / 3 := by
  rw [ramp_zero_raw]
  have hcast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  rw [hcast]
  norm_num [clip01_eq_self]

private theorem ramp_zero_at (m : ℕ) :
    rampNat (3 * m) (m + 1) m = 1 / 3 := by
  rw [ramp_zero_raw]
  norm_num [clip01_eq_self]

private theorem ramp_zero_high {m j : ℕ} (h : m + 1 ≤ j) :
    rampNat (3 * m) (m + 1) j = 0 := by
  rw [ramp_zero_raw]
  apply clip01_eq_zero_of_le_zero
  have hq : (m : ℚ) + 1 ≤ (j : ℚ) := by exact_mod_cast h
  linarith

/-- Exact ramp-mass evaluation when `k=3m`. -/
theorem three_mul_rampMass_zero (m : ℕ) (hm : 1 ≤ m) :
    3 * rampMass (3 * m) (m + 1) = Uzero m := by
  let f : ℕ → ℚ := fun j ↦
    (Nat.choose (3 * m) j : ℚ) * rampNat (3 * m) (m + 1) j
  have htrunc :
      (∑ j ∈ Finset.range (3 * m + 1), f j) =
        ∑ j ∈ Finset.range (m + 1), f j := by
    apply sum_range_eq_sum_range_of_zero_from f
    · omega
    · intro j hj
      simp [f, ramp_zero_high hj]
  have hlow :
      (∑ j ∈ Finset.range (m - 1), f j) =
        (binomPrefix (3 * m) (m - 1) : ℚ) := by
    calc
      (∑ j ∈ Finset.range (m - 1), f j) =
          ∑ j ∈ Finset.range (m - 1), (Nat.choose (3 * m) j : ℚ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j < m - 1 := Finset.mem_range.mp hj
            simp [f, ramp_zero_low hj']
      _ = (binomPrefix (3 * m) (m - 1) : ℚ) := by
        simp [binomPrefix]
  have hmstep : m - 1 + 1 = m := by omega
  unfold rampMass
  rw [htrunc]
  rw [show m + 1 = (m - 1) + 1 + 1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hlow]
  simp [f, hmstep, ramp_zero_pred m hm, ramp_zero_at m, Uzero]
  ring

/-! ## `k = 3m+1` -/

private theorem ramp_one_raw (m j : ℕ) :
    rampNat (3 * m + 1) (m + 1) j =
      clip01 (((m : ℚ) + 1 - (j : ℚ)) / 2) := by
  unfold rampNat ramp
  congr 1
  push_cast
  ring

private theorem ramp_one_low {m j : ℕ} (h : j < m) :
    rampNat (3 * m + 1) (m + 1) j = 1 := by
  rw [ramp_one_raw]
  apply clip01_eq_one_of_one_le
  have hj : j + 1 ≤ m := by omega
  have hjq : (j : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast hj
  linarith

private theorem ramp_one_at (m : ℕ) :
    rampNat (3 * m + 1) (m + 1) m = 1 / 2 := by
  rw [ramp_one_raw]
  norm_num [clip01_eq_self]

private theorem ramp_one_high {m j : ℕ} (h : m + 1 ≤ j) :
    rampNat (3 * m + 1) (m + 1) j = 0 := by
  rw [ramp_one_raw]
  apply clip01_eq_zero_of_le_zero
  have hq : (m : ℚ) + 1 ≤ (j : ℚ) := by exact_mod_cast h
  linarith

/-- Exact ramp-mass evaluation when `k=3m+1`. -/
theorem three_mul_rampMass_one (m : ℕ) :
    3 * rampMass (3 * m + 1) (m + 1) = Uone m := by
  let f : ℕ → ℚ := fun j ↦
    (Nat.choose (3 * m + 1) j : ℚ) * rampNat (3 * m + 1) (m + 1) j
  have htrunc :
      (∑ j ∈ Finset.range (3 * m + 2), f j) =
        ∑ j ∈ Finset.range (m + 1), f j := by
    apply sum_range_eq_sum_range_of_zero_from f
    · omega
    · intro j hj
      simp [f, ramp_one_high hj]
  have hlow :
      (∑ j ∈ Finset.range m, f j) =
        (binomPrefix (3 * m + 1) m : ℚ) := by
    calc
      (∑ j ∈ Finset.range m, f j) =
          ∑ j ∈ Finset.range m, (Nat.choose (3 * m + 1) j : ℚ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j < m := Finset.mem_range.mp hj
            simp [f, ramp_one_low hj']
      _ = (binomPrefix (3 * m + 1) m : ℚ) := by
        simp [binomPrefix]
  unfold rampMass
  rw [htrunc, Finset.sum_range_succ, hlow]
  simp [f, ramp_one_at m, Uone]
  ring

/-! ## `k = 3m+2` -/

private theorem ramp_two_raw (m j : ℕ) :
    rampNat (3 * m + 2) (m + 2) j =
      clip01 (((m : ℚ) + 2 - (j : ℚ)) / 4) := by
  unfold rampNat ramp
  congr 1
  push_cast
  ring

private theorem ramp_two_low {m j : ℕ} (h : j < m - 1) :
    rampNat (3 * m + 2) (m + 2) j = 1 := by
  rw [ramp_two_raw]
  apply clip01_eq_one_of_one_le
  have hj : j + 2 ≤ m := by omega
  have hjq : (j : ℚ) + 2 ≤ (m : ℚ) := by exact_mod_cast hj
  linarith

private theorem ramp_two_pred (m : ℕ) (hm : 1 ≤ m) :
    rampNat (3 * m + 2) (m + 2) (m - 1) = 3 / 4 := by
  rw [ramp_two_raw]
  have hcast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub hm]
    norm_num
  rw [hcast]
  norm_num [clip01_eq_self]

private theorem ramp_two_at (m : ℕ) :
    rampNat (3 * m + 2) (m + 2) m = 1 / 2 := by
  rw [ramp_two_raw]
  norm_num [clip01_eq_self]

private theorem ramp_two_succ (m : ℕ) :
    rampNat (3 * m + 2) (m + 2) (m + 1) = 1 / 4 := by
  rw [ramp_two_raw]
  norm_num [clip01_eq_self]

private theorem ramp_two_high {m j : ℕ} (h : m + 2 ≤ j) :
    rampNat (3 * m + 2) (m + 2) j = 0 := by
  rw [ramp_two_raw]
  apply clip01_eq_zero_of_le_zero
  have hq : (m : ℚ) + 2 ≤ (j : ℚ) := by exact_mod_cast h
  linarith

/-- Exact ramp-mass evaluation when `k=3m+2`. -/
theorem three_mul_rampMass_two (m : ℕ) (hm : 1 ≤ m) :
    3 * rampMass (3 * m + 2) (m + 2) = Utwo m := by
  let f : ℕ → ℚ := fun j ↦
    (Nat.choose (3 * m + 2) j : ℚ) * rampNat (3 * m + 2) (m + 2) j
  have htrunc :
      (∑ j ∈ Finset.range (3 * m + 3), f j) =
        ∑ j ∈ Finset.range (m + 2), f j := by
    apply sum_range_eq_sum_range_of_zero_from f
    · omega
    · intro j hj
      simp [f, ramp_two_high hj]
  have hlow :
      (∑ j ∈ Finset.range (m - 1), f j) =
        (binomPrefix (3 * m + 2) (m - 1) : ℚ) := by
    calc
      (∑ j ∈ Finset.range (m - 1), f j) =
          ∑ j ∈ Finset.range (m - 1), (Nat.choose (3 * m + 2) j : ℚ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j < m - 1 := Finset.mem_range.mp hj
            simp [f, ramp_two_low hj']
      _ = (binomPrefix (3 * m + 2) (m - 1) : ℚ) := by
        simp [binomPrefix]
  have hmstep : m - 1 + 1 = m := by omega
  have hm2 : 2 + (m - 1) = m + 1 := by omega
  unfold rampMass
  rw [htrunc]
  rw [show m + 2 = (m - 1) + 1 + 1 + 1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, hlow]
  simp [f, hmstep, hm2, ramp_two_pred m hm, ramp_two_at m,
    ramp_two_succ m, Utwo]
  ring

end CoprimeAdjacent
