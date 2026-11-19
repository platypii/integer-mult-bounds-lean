module

public import IntegerMultBounds.MathlibTM2.DFT.Top
public import IntegerMultBounds.MathlibTM2.Fast.CompactFinalR
import IntegerMultBounds.MathlibTM2.Cost.CompactRetunedTransformMatchR
import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsTime

/-!
# The prime-field DFT below `n log n`

`finalHostMultiplier`: the rounded compact multiplier of `Fast/CompactFinalR.lean` as a
`HostMultiplier (4223103985 / 2 ^ 46)`: its host table on the inputs of length at least `n₀`
(`compactRetunedPrefixR_exec`, `compactCompletedR_hostMul`), extended to every input by
`dispatch` (`dispatch_exec`), with `time = O(n (log n) ^ (1 - κ))`
(`compactMain_runs_time_isBigO`, `isBigO_dispatchTime`).

`dftInTime : DFTInTime (4223103985 / 2 ^ 46)` follows from `HostMultiplier.dftInTime`, and
`dft_in_time : DFTStatement` from `dftInTime`.
-/

@[expose] public section

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main Filter Asymptotics

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The final multiplier as a subroutine of the transform. -/
theorem finalHostMultiplier : Nonempty (HostMultiplier (4223103985 / 2 ^ 46 : ℝ)) := by
  obtain ⟨Cs, hCs⟩ := Cost.compactRetunedR_transform_cost_le
  have hexec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x, y)).length = n →
      HostMulWithin (compactCompletedTableR compactRetunedPrefixR) (compactMainOldProc .main)
        compactMainV₀ (compactRetunedTimeR (compactCompletedPushR compactRetunedPrefixR) 16) x y := by
    filter_upwards [compactRetunedPrefixR_exec] with n hn x y hxy
    obtain ⟨m, v, S, hm, he, hi, ho, hL⟩ := hn x y hxy
    exact compactCompletedR_hostMul compactRetunedPrefixR 16 x y he (hxy ▸ hm) hi ho hL
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hexec
  have hfast : ∀ x y, n₀ ≤ (pairEnc (x, y)).length →
      HostMulWithin (compactCompletedTableR compactRetunedPrefixR) (compactMainOldProc .main)
        compactMainV₀ (compactRetunedTimeR (compactCompletedPushR compactRetunedPrefixR) 16) x y :=
    fun x y hn => hn₀ _ hn x y rfl
  have htime : (fun n => (compactRetunedTimeR (compactCompletedPushR compactRetunedPrefixR) 16 n :
      ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) * Real.log n ^ (1 - (4223103985 / 2 ^ 46 : ℝ)) :=
    compactMain_runs_time_isBigO compactRetunedDist compactRetunedCFR compactRetunedCOR compactMnT
      (compactCompletedPushR compactRetunedPrefixR) 16 hCs
  have hpos : ∀ᶠ n in atTop, 1 ≤ compactRetunedTimeR (compactCompletedPushR compactRetunedPrefixR)
      16 n :=
    eventually_atTop.2 ⟨n₀, fun n hn => by have := two_le_time hfast hn; omega⟩
  exact ⟨{
    T := _, Q := _, A := _, U := _, P := _
    fintypeU := inferInstance
    fintypeP := inferInstance
    body := dispatch n₀ (compactCompletedTableR compactRetunedPrefixR) (compactMainOldProc .main)
    pm := none
    v₀ := withBuf compactMainV₀ Buf.empty
    time := dispatchTime n₀ (compactRetunedTimeR (compactCompletedPushR compactRetunedPrefixR) 16)
    run := dispatch_exec _ _ _ _ n₀ hfast
    isBigO := (isBigO_dispatchTime n₀ _ hpos).trans htime }⟩

/-- **The prime-field DFT below `n log n`** with the explicit saving: one fixed finite Mathlib
machine computes the transform of every instance in worst-case time `O(N (log N) ^ (1 - κ))`,
`N` the input length, for `κ = 4223103985 / 2 ^ 46`. -/
theorem dftInTime : DFTInTime (4223103985 / 2 ^ 46 : ℝ) := by
  obtain ⟨M⟩ := finalHostMultiplier
  exact M.dftInTime (by norm_num)

/-- The statement of `Statement.lean`. -/
theorem dft_in_time : DFTStatement :=
  ⟨4223103985 / 2 ^ 46, by norm_num, dftInTime⟩

end IntegerMultBounds.MathlibTM2.DFT

#print axioms IntegerMultBounds.MathlibTM2.DFT.dftInTime
#print axioms IntegerMultBounds.MathlibTM2.DFT.dft_in_time
