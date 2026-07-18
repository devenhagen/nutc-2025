import CoprimeAdjacent.ResidueBounds

/-!
# Closed finite bounds for adjacent disjoint subset-sum gaps
-/

namespace CoprimeAdjacent

section ResidueBounds

variable {ι K E : Type*} [Fintype ι] [DecidableEq ι]
  [LinearOrderedField K] [Fintype E]
variable {weight : ι → K}

/-- The fractional-cover bound in residue class `k=3m`. -/
theorem subset_Uzero_bound
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m) :
    (Fintype.card E : ℚ) ≤ Uzero m := by
  have h := subset_ramp_bound edge hedge hstrict (m + 1) (by
    rw [hcard]
    omega)
  rw [hcard] at h
  change (Fintype.card E : ℚ) ≤ 3 * rampMass (3 * m) (m + 1) at h
  rwa [three_mul_rampMass_zero m hm] at h

/-- The fractional-cover bound in residue class `k=3m+1`. -/
theorem subset_Uone_bound
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hcard : Fintype.card ι = 3 * m + 1) :
    (Fintype.card E : ℚ) ≤ Uone m := by
  have h := subset_ramp_bound edge hedge hstrict (m + 1) (by
    rw [hcard]
    omega)
  rw [hcard] at h
  change (Fintype.card E : ℚ) ≤ 3 * rampMass (3 * m + 1) (m + 1) at h
  rwa [three_mul_rampMass_one m] at h

/-- The fractional-cover bound in residue class `k=3m+2`. -/
theorem subset_Utwo_bound
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m + 2) :
    (Fintype.card E : ℚ) ≤ Utwo m := by
  have h := subset_ramp_bound edge hedge hstrict (m + 2) (by
    rw [hcard]
    omega)
  rw [hcard] at h
  change (Fintype.card E : ℚ) ≤ 3 * rampMass (3 * m + 2) (m + 2) at h
  rwa [three_mul_rampMass_two m hm] at h

/-- Strict one-unit improvement over the distinguished old cutoff when
`k=3m`. -/
theorem subset_lt_cutoffZero
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m) :
    Fintype.card E ≤ cutoffZero m - 1 := by
  apply nat_le_pred_of_cast_le_of_lt
      (subset_Uzero_bound edge hedge hstrict m hm hcard)
  have hgap := cutoffZero_sub_Uzero m hm
  have hposNat : 0 < Nat.choose (3 * m) (m - 1) := by
    apply Nat.choose_pos
    omega
  have hpos : (0 : ℚ) < Nat.choose (3 * m) (m - 1) := by
    exact_mod_cast hposNat
  linarith

/-- Strict one-unit improvement over the distinguished old cutoff when
`k=3m+1`. -/
theorem subset_lt_cutoffOne
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hcard : Fintype.card ι = 3 * m + 1) :
    Fintype.card E ≤ cutoffOne m - 1 := by
  apply nat_le_pred_of_cast_le_of_lt
      (subset_Uone_bound edge hedge hstrict m hcard)
  have hgap := cutoffOne_sub_Uone m
  have hposNat : 0 < Nat.choose (3 * m + 1) m := by
    apply Nat.choose_pos
    omega
  have hpos : (0 : ℚ) < Nat.choose (3 * m + 1) m := by
    exact_mod_cast hposNat
  linarith

/-- Strict one-unit improvement over the distinguished old cutoff when
`k=3m+2`. -/
theorem subset_lt_cutoffTwo
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m + 2) :
    Fintype.card E ≤ cutoffTwo m - 1 := by
  apply nat_le_pred_of_cast_le_of_lt
      (subset_Utwo_bound edge hedge hstrict m hm hcard)
  have hgap := cutoffTwo_sub_Utwo m hm
  have hposNat : 0 < Nat.choose (3 * m + 2) (m - 1) := by
    apply Nat.choose_pos
    omega
  have hpos : (0 : ℚ) < Nat.choose (3 * m + 2) (m - 1) := by
    exact_mod_cast hposNat
  linarith

end ResidueBounds

end CoprimeAdjacent
