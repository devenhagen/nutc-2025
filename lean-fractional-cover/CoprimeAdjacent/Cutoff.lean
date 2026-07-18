import CoprimeAdjacent.Arithmetic

/-!
# Exact optimization of the old binomial cutoff
-/

namespace CoprimeAdjacent

/-- Strict increase of a binomial row before its midpoint. -/
theorem choose_lt_succ_of_twice_lt {k r : ℕ} (h : 2 * r + 1 < k) :
    Nat.choose k r < Nat.choose k (r + 1) := by
  have hrk : r ≤ k := by omega
  have hpos : 0 < Nat.choose k r := Nat.choose_pos hrk
  have hcoef : r + 1 < k - r := by omega
  have hid := Nat.choose_succ_right_eq k r
  by_contra hnot
  have hle : Nat.choose k (r + 1) ≤ Nat.choose k r := Nat.le_of_not_gt hnot
  have hmulLe : Nat.choose k (r + 1) * (r + 1) ≤
      Nat.choose k r * (r + 1) := Nat.mul_le_mul_right _ hle
  have hmulLt : Nat.choose k r * (r + 1) <
      Nat.choose k r * (k - r) := (Nat.mul_lt_mul_left hpos).2 hcoef
  rw [hid] at hmulLe
  exact (Nat.not_lt_of_ge hmulLe) hmulLt

/-- Monotonicity in the lower binomial index while the target remains on the
left half of the row. -/
theorem choose_le_of_le_of_twice_le {k r s : ℕ}
    (hrs : r ≤ s) (hs : 2 * s ≤ k) :
    Nat.choose k r ≤ Nat.choose k s := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hrs
  induction q with
  | zero => simp
  | succ q ih =>
      have hstep : Nat.choose k (r + q) < Nat.choose k (r + q + 1) := by
        apply choose_lt_succ_of_twice_lt
        omega
      exact (ih (by omega) (by omega)).trans hstep.le

/-- Strict monotonicity in the lower binomial index on the left half. -/
theorem choose_lt_of_lt_of_twice_le {k r s : ℕ}
    (hrs : r < s) (hs : 2 * s ≤ k) :
    Nat.choose k r < Nat.choose k s := by
  have hrs' : r ≤ s - 1 := by omega
  have hweak := choose_le_of_le_of_twice_le hrs' (show 2 * (s - 1) ≤ k by omega)
  have hlast : Nat.choose k (s - 1) < Nat.choose k ((s - 1) + 1) := by
    apply choose_lt_succ_of_twice_lt
    omega
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : s ≠ 0))] using
    hweak.trans_lt hlast

/-- Compare two entries when the first index lies no farther from either end
of the row than the second index. -/
theorem choose_le_of_le_both_sides {k r s : ℕ}
    (hrs : r ≤ s) (hrc : r ≤ k - s) (hsk : s ≤ k) :
    Nat.choose k r ≤ Nat.choose k s := by
  by_cases hs : 2 * s ≤ k
  · exact choose_le_of_le_of_twice_le hrs hs
  · rw [← Nat.choose_symm hsk]
    apply choose_le_of_le_of_twice_le hrc
    omega

/-- Strict version of `choose_le_of_le_both_sides`. -/
theorem choose_lt_of_lt_both_sides {k r s : ℕ}
    (hrs : r < s) (hrc : r < k - s) (hsk : s ≤ k) :
    Nat.choose k r < Nat.choose k s := by
  by_cases hs : 2 * s ≤ k
  · exact choose_lt_of_lt_of_twice_le hrs hs
  · rw [← Nat.choose_symm hsk]
    apply choose_lt_of_lt_of_twice_le hrc
    omega

/-- One step toward the optimal cutoff from the left. -/
theorem cutoffBound_step_down {k t : ℕ} (h : 3 * t + 4 ≤ k) :
    cutoffBound k (t + 1) < cutoffBound k t := by
  let v := k - (2 * t + 2)
  have hv : 1 ≤ v := by dsimp [v]; omega
  have hnew : k - (2 * (t + 1) + 1) = v - 1 := by dsimp [v]; omega
  have hold : k - (2 * t + 1) = v + 1 := by dsimp [v]; omega
  have hvstep : v - 1 + 1 = v := by omega
  have hstrict : Nat.choose k (t + 1) < Nat.choose k v := by
    apply choose_lt_of_lt_both_sides
    all_goals dsimp [v] <;> omega
  have hweak : Nat.choose k (t + 1) ≤ Nat.choose k (v - 1) := by
    apply choose_le_of_le_both_sides
    all_goals dsimp [v] <;> omega
  simp only [cutoffBound, hnew, hold]
  rw [binomPrefix_succ k (t + 1), binomPrefix_succ k v]
  rw [show binomPrefix k v =
      binomPrefix k (v - 1) + Nat.choose k (v - 1) by
        simpa [hvstep] using binomPrefix_succ k (v - 1)]
  omega

/-- One strict step away from the optimal cutoff on the right, as long as the
first binomial prefix has not reached its terminal plateau. -/
theorem cutoffBound_step_up {k t : ℕ}
    (hcenter : k ≤ 3 * t + 3) (htk : t < k) :
    cutoffBound k t < cutoffBound k (t + 1) := by
  have hrk : t + 1 ≤ k := by omega
  have hchoose : 0 < Nat.choose k (t + 1) := Nat.choose_pos hrk
  by_cases htail : 2 * t + 3 ≤ k
  · let v := k - (2 * t + 2)
    have hv : 1 ≤ v := by dsimp [v]; omega
    have hnew : k - (2 * (t + 1) + 1) = v - 1 := by dsimp [v]; omega
    have hold : k - (2 * t + 1) = v + 1 := by dsimp [v]; omega
    have hvstep : v - 1 + 1 = v := by omega
    have hweak : Nat.choose k v ≤ Nat.choose k (t + 1) := by
      apply choose_le_of_le_both_sides
      all_goals dsimp [v] <;> omega
    have hstrict : Nat.choose k (v - 1) < Nat.choose k (t + 1) := by
      apply choose_lt_of_lt_both_sides
      all_goals dsimp [v] <;> omega
    simp only [cutoffBound, hnew, hold]
    rw [binomPrefix_succ k (t + 1), binomPrefix_succ k v]
    rw [show binomPrefix k v =
        binomPrefix k (v - 1) + Nat.choose k (v - 1) by
          simpa [hvstep] using binomPrefix_succ k (v - 1)]
    omega
  · have hnew : k - (2 * (t + 1) + 1) = 0 := by omega
    have hcount : k - (2 * t + 1) ≤ 1 := by omega
    have htailLe : binomPrefix k (k - (2 * t + 1)) ≤ 1 := by
      have hcases : k - (2 * t + 1) = 0 ∨ k - (2 * t + 1) = 1 := by omega
      rcases hcases with hzero | hone
      · simp [hzero]
      · simp [hone, binomPrefix]
    simp only [cutoffBound, hnew]
    rw [binomPrefix_succ k (t + 1)]
    simp only [binomPrefix_zero, Nat.add_zero]
    omega

/-- Past row `k`, the binomial prefix is constant. -/
theorem binomPrefix_eq_full {k r : ℕ} (h : k + 1 ≤ r) :
    binomPrefix k r = binomPrefix k (k + 1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show k + 1 + q = (k + 1) + q by rfl]
  unfold binomPrefix
  rw [Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range q, Nat.choose k (k + 1 + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Nat.choose_eq_zero_of_lt
    have hi' : i < q := Finset.mem_range.mp hi
    omega
  simpa [hz]

/-- The center cutoff used in the exact optimization. -/
def centerCutoffIndex (k : ℕ) : ℕ := (k - 1) / 3

def optimizedCutoff (k : ℕ) : ℕ :=
  cutoffBound k (centerCutoffIndex k)

/-- The distinguished cutoff is no larger than any old cutoff. -/
theorem optimizedCutoff_le (k t : ℕ) (hk : 3 ≤ k) :
    optimizedCutoff k ≤ cutoffBound k t := by
  let t₀ := centerCutoffIndex k
  have hcenter : k ≤ 3 * t₀ + 3 := by
    dsimp [t₀, centerCutoffIndex]
    omega
  have ht₀k : t₀ < k := by
    dsimp [t₀, centerCutoffIndex]
    omega
  change cutoffBound k t₀ ≤ cutoffBound k t
  by_cases hleft : t ≤ t₀
  · exact Nat.decreasingInduction
      (motive := fun s _ ↦ cutoffBound k t₀ ≤ cutoffBound k s)
      (fun s hs ih ↦ ih.trans (cutoffBound_step_down (by
        dsimp [t₀, centerCutoffIndex] at hs
        omega)).le)
      le_rfl hleft
  · have ht₀t : t₀ ≤ t := Nat.le_of_not_ge hleft
    by_cases htk : t ≤ k
    · exact Nat.le_induction
        (motive := fun s _ ↦ cutoffBound k t₀ ≤ cutoffBound k s)
        le_rfl
        (fun s hs ih ↦ ih.trans (cutoffBound_step_up
          (k := k) (t := s) (by omega) (by omega)).le)
        t ht₀t
    · have htoK : cutoffBound k t = cutoffBound k k := by
        have hkt : k ≤ t := Nat.le_of_not_ge htk
        have hfirst := binomPrefix_eq_full (k := k) (r := t + 1) (by omega)
        have htailT : k - (2 * t + 1) = 0 := by omega
        have htailK : k - (2 * k + 1) = 0 := by omega
        unfold cutoffBound
        rw [hfirst, htailT, htailK]
      rw [htoK]
      exact Nat.le_induction
        (motive := fun s _ ↦ cutoffBound k t₀ ≤ cutoffBound k s)
        le_rfl
        (fun s hs ih ↦ ih.trans (cutoffBound_step_up
          (k := k) (t := s) (by omega) (by omega)).le)
        k (by omega)

/-- The optimizer specializes to `m-1,m,m` in the three residue classes. -/
@[simp] theorem centerCutoffIndex_zero (m : ℕ) (hm : 1 ≤ m) :
    centerCutoffIndex (3 * m) = m - 1 := by
  simp [centerCutoffIndex]
  omega

@[simp] theorem centerCutoffIndex_one (m : ℕ) :
    centerCutoffIndex (3 * m + 1) = m := by
  simp [centerCutoffIndex]

@[simp] theorem centerCutoffIndex_two (m : ℕ) :
    centerCutoffIndex (3 * m + 2) = m := by
  simp [centerCutoffIndex]
  omega

@[simp] theorem optimizedCutoff_zero (m : ℕ) (hm : 1 ≤ m) :
    optimizedCutoff (3 * m) = cutoffZero m := by
  simp [optimizedCutoff, cutoffZero, centerCutoffIndex_zero m hm]

@[simp] theorem optimizedCutoff_one (m : ℕ) :
    optimizedCutoff (3 * m + 1) = cutoffOne m := by
  simp [optimizedCutoff, cutoffOne]

@[simp] theorem optimizedCutoff_two (m : ℕ) :
    optimizedCutoff (3 * m + 2) = cutoffTwo m := by
  simp [optimizedCutoff, cutoffTwo]

end CoprimeAdjacent
