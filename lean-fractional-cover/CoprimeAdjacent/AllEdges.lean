import CoprimeAdjacent.FiniteBounds
import CoprimeAdjacent.Cutoff

/-!
# Applying the finite bounds to the complete adjacent-gap family
-/

namespace CoprimeAdjacent

namespace AdjacentGap

variable {P K : Type*} [Fintype P] [LinearOrder K] {value : P → K}

/-- An adjacent gap is determined by its ordered pair of endpoints, so the
complete family is finite whenever the point set is finite. -/
noncomputable instance : Fintype (AdjacentGap P K value) :=
  Fintype.ofInjective (fun e ↦ (e.lo, e.hi)) (by
    intro e₁ e₂ h
    apply AdjacentGap.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h)

end AdjacentGap

namespace DisjointGap

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [LinearOrderedField K] {weight : ι → K}

/-- The complete family of disjoint adjacent subset-sum gaps is finite. -/
noncomputable instance : Fintype (DisjointGap weight) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

end DisjointGap

section CompleteFamily

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [LinearOrderedField K] {weight : ι → K}

/-- The general ramp bound applied to every disjoint adjacent gap. -/
theorem all_subset_ramp_bound
    (hstrict : Function.Injective (subsetValue weight))
    (L : ℕ) (hL : Fintype.card ι < 3 * L) :
    (Fintype.card (DisjointGap weight) : ℚ) ≤
      3 * rampMass (Fintype.card ι) L := by
  change (Fintype.card (DisjointGap weight) : ℚ) ≤
    3 * ∑ j ∈ Finset.range (Fintype.card ι + 1),
      (Nat.choose (Fintype.card ι) j : ℚ) *
        rampNat (Fintype.card ι) L j
  exact subset_ramp_bound id Function.injective_id hstrict L hL

/-- Closed finite bound for the complete edge family when `k=3m`. -/
theorem all_subset_Uzero_bound
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m) :
    (Fintype.card (DisjointGap weight) : ℚ) ≤ Uzero m :=
  subset_Uzero_bound id Function.injective_id hstrict m hm hcard

/-- Closed finite bound for the complete edge family when `k=3m+1`. -/
theorem all_subset_Uone_bound
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hcard : Fintype.card ι = 3 * m + 1) :
    (Fintype.card (DisjointGap weight) : ℚ) ≤ Uone m :=
  subset_Uone_bound id Function.injective_id hstrict m hcard

/-- Closed finite bound for the complete edge family when `k=3m+2`. -/
theorem all_subset_Utwo_bound
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m + 2) :
    (Fintype.card (DisjointGap weight) : ℚ) ≤ Utwo m :=
  subset_Utwo_bound id Function.injective_id hstrict m hm hcard

/-- Strict improvement over the optimized old cutoff for `k=3m`. -/
theorem all_subset_lt_optimized_zero
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m) :
    Fintype.card (DisjointGap weight) ≤ optimizedCutoff (3 * m) - 1 := by
  rw [optimizedCutoff_zero m hm]
  exact subset_lt_cutoffZero id Function.injective_id hstrict m hm hcard

/-- Strict improvement over the optimized old cutoff for `k=3m+1`. -/
theorem all_subset_lt_optimized_one
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hcard : Fintype.card ι = 3 * m + 1) :
    Fintype.card (DisjointGap weight) ≤ optimizedCutoff (3 * m + 1) - 1 := by
  rw [optimizedCutoff_one m]
  exact subset_lt_cutoffOne id Function.injective_id hstrict m hcard

/-- Strict improvement over the optimized old cutoff for `k=3m+2`. -/
theorem all_subset_lt_optimized_two
    (hstrict : Function.Injective (subsetValue weight))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card ι = 3 * m + 2) :
    Fintype.card (DisjointGap weight) ≤ optimizedCutoff (3 * m + 2) - 1 := by
  rw [optimizedCutoff_two m]
  exact subset_lt_cutoffTwo id Function.injective_id hstrict m hm hcard

end CompleteFamily

end CoprimeAdjacent
