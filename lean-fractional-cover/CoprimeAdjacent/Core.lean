import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# A fractional-cover bound for adjacent disjoint subset sums

This file kernel-checks the finite combinatorial core of the proposed
strict finite-`k` improvement for coprime adjacent divisors.

The number-theoretic input is abstracted to a finite family of disjoint
adjacent gaps in a strict subset-sum order.  The formalized chain is:

* uniqueness of the lower and upper endpoint signatures;
* uniqueness of the unused-complement signature via gap midpoints;
* the three-signature fractional-cover inequality;
* the clipped linear ramp inequality;
* conversion of the Boolean-lattice mass to a binomial sum.

There are no `sorry` declarations or additional axioms in this file.
-/

open scoped BigOperators

namespace CoprimeAdjacent

/-! ## Adjacent gaps and midpoint injectivity -/

/-- An oriented gap between two consecutive values of a strict order.
The ambient point type need not itself carry an order; only its `value` map does. -/
@[ext]
structure AdjacentGap (P K : Type*) [LinearOrder K] (value : P → K) where
  lo : P
  hi : P
  lt : value lo < value hi
  noBetween : ∀ p : P, ¬ (value lo < value p ∧ value p < value hi)

namespace AdjacentGap

variable {P K : Type*} [LinearOrderedField K] {value : P → K}

/-- The midpoint of an adjacent gap. -/
def midpoint (e : AdjacentGap P K value) : K :=
  (value e.lo + value e.hi) / 2

theorem lo_lt_midpoint (e : AdjacentGap P K value) :
    value e.lo < e.midpoint := by
  unfold midpoint
  linarith [e.lt]

theorem midpoint_lt_hi (e : AdjacentGap P K value) :
    e.midpoint < value e.hi := by
  unfold midpoint
  linarith [e.lt]

/-- The lower endpoint determines an adjacent gap. -/
theorem lo_injective (hvalue : Function.Injective value) :
    Function.Injective (fun e : AdjacentGap P K value ↦ e.lo) := by
  intro e₁ e₂ hlo
  have hvlo : value e₁.lo = value e₂.lo := congrArg value hlo
  have hvhi : value e₁.hi = value e₂.hi := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h₁₂ | h₂₁
    · exact e₂.noBetween e₁.hi ⟨by simpa [hvlo] using e₁.lt, h₁₂⟩
    · exact e₁.noBetween e₂.hi ⟨by simpa [hvlo] using e₂.lt, h₂₁⟩
  exact AdjacentGap.ext hlo (hvalue hvhi)

/-- The upper endpoint determines an adjacent gap. -/
theorem hi_injective (hvalue : Function.Injective value) :
    Function.Injective (fun e : AdjacentGap P K value ↦ e.hi) := by
  intro e₁ e₂ hhi
  have hvhi : value e₁.hi = value e₂.hi := congrArg value hhi
  have hvlo : value e₁.lo = value e₂.lo := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h₁₂ | h₂₁
    · exact e₁.noBetween e₂.lo ⟨h₁₂, by simpa [hvhi] using e₂.lt⟩
    · exact e₂.noBetween e₁.lo ⟨h₂₁, by simpa [hvhi] using e₁.lt⟩
  exact AdjacentGap.ext (hvalue hvlo) hhi

/-- Distinct adjacent gaps have distinct midpoints. -/
theorem midpoint_injective (hvalue : Function.Injective value) :
    Function.Injective (midpoint (value := value)) := by
  intro e₁ e₂ hmid
  by_cases hlo : value e₁.lo = value e₂.lo
  · apply lo_injective hvalue
    exact hvalue hlo
  rcases lt_or_gt_of_ne hlo with h₁₂ | h₂₁
  · exfalso
    exact e₁.noBetween e₂.lo ⟨h₁₂, by
      calc
        value e₂.lo < e₂.midpoint := lo_lt_midpoint e₂
        _ = e₁.midpoint := hmid.symm
        _ < value e₁.hi := midpoint_lt_hi e₁⟩
  · exfalso
    exact e₂.noBetween e₁.lo ⟨h₂₁, by
      calc
        value e₁.lo < e₁.midpoint := lo_lt_midpoint e₁
        _ = e₂.midpoint := hmid
        _ < value e₂.hi := midpoint_lt_hi e₂⟩

/-- Any signature that determines the midpoint is injective. -/
theorem signature_injective_of_midpoint
    {Γ : Type*} (hvalue : Function.Injective value)
    (signature : AdjacentGap P K value → Γ) (code : Γ → K)
    (hcode : ∀ e, e.midpoint = code (signature e)) :
    Function.Injective signature := by
  intro e₁ e₂ hs
  apply midpoint_injective hvalue
  rw [hcode e₁, hcode e₂, hs]

end AdjacentGap

/-! ## The subset-sum model and its three signatures -/

section SubsetModel

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [LinearOrderedField K]

/-- Additive value of a finite subset. -/
def subsetValue (weight : ι → K) (s : Finset ι) : K :=
  ∑ i ∈ s, weight i

/-- A disjoint adjacent gap in the complete subset-value order. -/
def DisjointGap (weight : ι → K) :=
  {e : AdjacentGap (Finset ι) K (subsetValue weight) // Disjoint e.lo e.hi}

namespace DisjointGap

variable {weight : ι → K}

/-- First endpoint signature. -/
def first (e : DisjointGap weight) : Finset ι := e.1.lo

/-- Second endpoint signature. -/
def second (e : DisjointGap weight) : Finset ι := e.1.hi

/-- Elements unused by either endpoint. -/
def unused (e : DisjointGap weight) : Finset ι :=
  Finset.univ \ (first e ∪ second e)

omit [Fintype ι] [DecidableEq ι] in
/-- The first endpoint is an injective edge signature. -/
theorem first_injective
    (hstrict : Function.Injective (subsetValue weight)) :
    Function.Injective (first (weight := weight)) := by
  intro e₁ e₂ h
  apply Subtype.ext
  exact AdjacentGap.lo_injective hstrict h

omit [Fintype ι] [DecidableEq ι] in
/-- The second endpoint is an injective edge signature. -/
theorem second_injective
    (hstrict : Function.Injective (subsetValue weight)) :
    Function.Injective (second (weight := weight)) := by
  intro e₁ e₂ h
  apply Subtype.ext
  exact AdjacentGap.hi_injective hstrict h

/-- For a disjoint edge, the midpoint is determined by the unused set. -/
theorem midpoint_eq_unused (e : DisjointGap weight) :
    e.1.midpoint =
      (subsetValue weight Finset.univ - subsetValue weight (unused e)) / 2 := by
  have hunion : subsetValue weight (first e ∪ second e) =
      subsetValue weight (first e) + subsetValue weight (second e) := by
    exact Finset.sum_union e.2
  have hcomp : subsetValue weight (unused e) +
      subsetValue weight (first e ∪ second e) = subsetValue weight Finset.univ := by
    exact Finset.sum_sdiff (Finset.subset_univ (first e ∪ second e))
  unfold AdjacentGap.midpoint
  dsimp [unused, first, second] at hcomp hunion ⊢
  linarith

/-- The unused-complement signature is injective. -/
theorem unused_injective
    (hstrict : Function.Injective (subsetValue weight)) :
    Function.Injective (unused (weight := weight)) := by
  intro e₁ e₂ hunused
  apply Subtype.ext
  apply AdjacentGap.midpoint_injective hstrict
  rw [midpoint_eq_unused e₁, midpoint_eq_unused e₂, hunused]

/-- The three signature cardinalities partition the ground-set cardinality. -/
theorem card_first_add_second_add_unused (e : DisjointGap weight) :
    (first e).card + (second e).card + (unused e).card = Fintype.card ι := by
  have hunion : (first e ∪ second e).card = (first e).card + (second e).card :=
    Finset.card_union_of_disjoint e.2
  have hcomp : (unused e).card + (first e ∪ second e).card =
      (Finset.univ : Finset ι).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (first e ∪ second e))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hunion] using hcomp

end DisjointGap
end SubsetModel

/-! ## The abstract fractional-cover inequality -/

section FractionalCover

variable {E Ω R : Type*} [Fintype E] [Fintype Ω]
variable [LinearOrderedField R]

/-- An injective signature uses at most the total available nonnegative mass. -/
theorem sum_comp_le_sum_of_injective (σ : E → Ω) (hσ : Function.Injective σ)
    (mass : Ω → R) (hmass : ∀ x, 0 ≤ mass x) :
    (∑ e : E, mass (σ e)) ≤ ∑ x : Ω, mass x := by
  classical
  rw [← Finset.sum_image hσ.injOn]
  exact Finset.sum_le_univ_sum_of_nonneg hmass

/-- Three injective signatures plus a pointwise fractional cover bound the number of edges. -/
theorem fractional_cover
    (A B C : E → Ω)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hC : Function.Injective C)
    (mass : Ω → R) (hmass : ∀ x, 0 ≤ mass x)
    (hcover : ∀ e, (1 : R) ≤ mass (A e) + mass (B e) + mass (C e)) :
    (Fintype.card E : R) ≤ 3 * ∑ x : Ω, mass x := by
  have hcovsum : (Fintype.card E : R) ≤
      (∑ e : E, mass (A e)) + (∑ e : E, mass (B e)) +
        (∑ e : E, mass (C e)) := by
    calc
      (Fintype.card E : R) = ∑ _e : E, (1 : R) := by simp
      _ ≤ ∑ e : E, (mass (A e) + mass (B e) + mass (C e)) := by
        exact Finset.sum_le_sum (fun e _he ↦ hcover e)
      _ = (∑ e : E, mass (A e)) + (∑ e : E, mass (B e)) +
          (∑ e : E, mass (C e)) := by
        simp only [Finset.sum_add_distrib]
  have hA' := sum_comp_le_sum_of_injective A hA mass hmass
  have hB' := sum_comp_le_sum_of_injective B hB mass hmass
  have hC' := sum_comp_le_sum_of_injective C hC mass hmass
  linarith

end FractionalCover

/-! ## The clipped linear ramp -/

section Ramp

variable {R : Type*} [LinearOrderedField R]

/-- Clipping to the interval `[0,1]`. -/
def clip01 (x : R) : R := min 1 (max 0 x)

theorem clip01_nonneg (x : R) : 0 ≤ clip01 x := by
  unfold clip01
  exact le_min (by norm_num) (le_max_left 0 x)

theorem clip01_eq_one_of_one_le {x : R} (hx : 1 ≤ x) : clip01 x = 1 := by
  unfold clip01
  rw [min_eq_left]
  exact hx.trans (le_max_right 0 x)

theorem le_clip01_of_le_one {x : R} (hx : x ≤ 1) : x ≤ clip01 x := by
  unfold clip01
  exact le_min hx (le_max_right 0 x)

/-- If three untruncated values sum to one, their clipped values cover one. -/
theorem clip01_sum_ge_one {x y z : R} (hxyz : x + y + z = 1) :
    1 ≤ clip01 x + clip01 y + clip01 z := by
  by_cases hx : 1 ≤ x
  · rw [clip01_eq_one_of_one_le hx]
    linarith [clip01_nonneg y, clip01_nonneg z]
  by_cases hy : 1 ≤ y
  · rw [clip01_eq_one_of_one_le hy]
    linarith [clip01_nonneg x, clip01_nonneg z]
  by_cases hz : 1 ≤ z
  · rw [clip01_eq_one_of_one_le hz]
    linarith [clip01_nonneg x, clip01_nonneg y]
  have hx' : x ≤ 1 := le_of_lt (lt_of_not_ge hx)
  have hy' : y ≤ 1 := le_of_lt (lt_of_not_ge hy)
  have hz' : z ≤ 1 := le_of_lt (lt_of_not_ge hz)
  linarith [le_clip01_of_le_one hx', le_clip01_of_le_one hy',
    le_clip01_of_le_one hz']

/-- The clipped linear ramp with denominator `3L-k`. -/
def ramp (k L x : R) : R :=
  clip01 ((L - x) / (3 * L - k))

/-- The ramp covers every triple whose coordinates sum to `k`. -/
theorem ramp_cover {k L a b c : R}
    (hD : 0 < 3 * L - k) (hsum : a + b + c = k) :
    1 ≤ ramp k L a + ramp k L b + ramp k L c := by
  apply clip01_sum_ge_one
  field_simp [ne_of_gt hD]
  linarith

end Ramp

/-! ## Boolean-lattice mass and the specialized finite bound -/

section BooleanMass

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [LinearOrderedField R]

/-- Grouping all finite subsets by cardinality gives the binomial-weighted mass. -/
theorem binomial_mass (f : ℕ → R) :
    (∑ s : Finset ι, f s.card) =
      ∑ j ∈ Finset.range (Fintype.card ι + 1),
        (Nat.choose (Fintype.card ι) j : R) * f j := by
  classical
  have hmap : ∀ s ∈ (Finset.univ : Finset (Finset ι)),
      s.card ∈ Finset.range (Fintype.card ι + 1) := by
    intro s _hs
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.card_le_univ s)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to hmap (fun s : Finset ι ↦ f s.card)
  have hinner (j : ℕ) :
      (∑ s ∈ Finset.powersetCard j (Finset.univ : Finset ι), f s.card) =
        (Nat.choose (Fintype.card ι) j : R) * f j := by
    calc
      (∑ s ∈ Finset.powersetCard j (Finset.univ : Finset ι), f s.card) =
          ∑ _s ∈ Finset.powersetCard j (Finset.univ : Finset ι), f j := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [(Finset.mem_powersetCard.mp hs).2]
      _ = (Finset.powersetCard j (Finset.univ : Finset ι)).card • f j :=
        Finset.sum_const (f j)
      _ = (Nat.choose (Fintype.card ι) j : R) * f j := by
        rw [Finset.card_powersetCard]
        simp [nsmul_eq_mul]
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.univ_filter_card_eq]
  exact hinner j

end BooleanMass

section SubsetFractionalCover

variable {ι K R E : Type*} [Fintype ι] [DecidableEq ι]
  [LinearOrderedField K] [LinearOrderedField R] [Fintype E]
variable {weight : ι → K}

/-- Fractional-cover bound for a finite family of disjoint adjacent subset gaps. -/
theorem subset_fractional_cover
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (f : ℕ → R) (hf : ∀ j, 0 ≤ f j)
    (htriple : ∀ a b c : ℕ, a + b + c = Fintype.card ι →
      (1 : R) ≤ f a + f b + f c) :
    (Fintype.card E : R) ≤
      3 * ∑ s : Finset ι, f s.card := by
  apply fractional_cover
      (fun e ↦ DisjointGap.first (edge e))
      (fun e ↦ DisjointGap.second (edge e))
      (fun e ↦ DisjointGap.unused (edge e))
      ((DisjointGap.first_injective (weight := weight) hstrict).comp hedge)
      ((DisjointGap.second_injective (weight := weight) hstrict).comp hedge)
      ((DisjointGap.unused_injective (weight := weight) hstrict).comp hedge)
      (fun s ↦ f s.card) (fun s ↦ hf s.card)
  intro e
  exact htriple _ _ _ (DisjointGap.card_first_add_second_add_unused (edge e))

/-- The same bound written as a binomial sum. -/
theorem subset_fractional_cover_binomial
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (f : ℕ → R) (hf : ∀ j, 0 ≤ f j)
    (htriple : ∀ a b c : ℕ, a + b + c = Fintype.card ι →
      (1 : R) ≤ f a + f b + f c) :
    (Fintype.card E : R) ≤
      3 * ∑ j ∈ Finset.range (Fintype.card ι + 1),
        (Nat.choose (Fintype.card ι) j : R) * f j := by
  rw [← binomial_mass]
  exact subset_fractional_cover edge hedge hstrict f hf htriple

/-- Natural-number specialization of the ramp. -/
def rampNat (k L j : ℕ) : ℚ :=
  ramp (k : ℚ) (L : ℚ) (j : ℚ)

theorem rampNat_nonneg (k L j : ℕ) : 0 ≤ rampNat k L j := by
  exact clip01_nonneg _

/-- The natural-number ramp covers every cardinality triple. -/
theorem rampNat_cover {k L a b c : ℕ}
    (hL : k < 3 * L) (hsum : a + b + c = k) :
    (1 : ℚ) ≤ rampNat k L a + rampNat k L b + rampNat k L c := by
  apply ramp_cover
  · have hLq : (k : ℚ) < 3 * (L : ℚ) := by exact_mod_cast hL
    linarith
  · exact_mod_cast hsum

/-- The kernel-checked ramp bound for a finite family of adjacent disjoint gaps. -/
theorem subset_ramp_bound
    (edge : E → DisjointGap weight) (hedge : Function.Injective edge)
    (hstrict : Function.Injective (subsetValue weight))
    (L : ℕ) (hL : Fintype.card ι < 3 * L) :
    (Fintype.card E : ℚ) ≤
      3 * ∑ j ∈ Finset.range (Fintype.card ι + 1),
        (Nat.choose (Fintype.card ι) j : ℚ) *
          rampNat (Fintype.card ι) L j := by
  apply subset_fractional_cover_binomial edge hedge hstrict
      (rampNat (Fintype.card ι) L)
      (fun j ↦ rampNat_nonneg _ _ j)
  intro a b c hsum
  exact rampNat_cover hL hsum

end SubsetFractionalCover

end CoprimeAdjacent
