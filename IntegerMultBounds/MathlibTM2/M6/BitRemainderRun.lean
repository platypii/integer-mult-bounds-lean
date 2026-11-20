module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun

/-! Physical interchange of the unhosted interval on an idle owner's flag coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitHosting
open BitOccurrences

/-- Physical idle intervals, including empty spans, realize the charged rank list. -/
theorem remainderWidths_perm :
    (remainderIntervals.map fun e => e.2 - e.1).Perm remainders := by
  have widths : ∀ i : Fin 9, (idleRanks 4).getD i.val 0 =
      7 * idleTarget i.val - 7 * idleSource i.val := by decide +kernel
  apply List.Perm.trans _ remainders_perm
  apply List.Perm.of_eq
  simp only [remainderIntervals, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro k _
  rw [widths ⟨i, List.mem_range.mp hi⟩]
  change 7 * idleTarget i - (7 * idleSource i + 8*k) = (7 * idleTarget i - 7 * idleSource i) - 8*k
  omega

end IntegerMultBounds.MathlibTM2.M6.BitHosting

namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthOriginalTotalRun (program cost input)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

/-- With its headers represented, one fixed program exchanges the idle interval on
the owner's tape, preserving both exterior slices even for an empty interval. -/
theorem remainderInterval_runs [M8.Machine.Net] {t w W : ℕ}
    (e : ℕ × ℕ) (hW : 0 < W)
    (caller : Tapes t prime) (headers : Fin 6 → Fin t) (src : Fin t)
    (hs : Fin 6 → List Bool) :
    let child := phaseIntervalChild e.1 e.2 w W 64
    RecursiveDimensionBank.Headers child hs →
    (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) →
    (∀ i, caller.head (headers i) = 1) →
    ∀ x : Fin (volume prime child) → ZMod 2,
    caller.tape src = sourceWord x → caller.head src = 0 →
    ∃ y : Fin (volume prime child) → ZMod 2,
      HoareTime (program headers src) (fun z => z = input caller)
        (fun z => z = input (SharedPlacementAlphabet.setTape caller src (sourceWord y) 0))
        (cost child hs) ∧
      ∀ a b h d u v j,
        y (RecursiveInterchangeScaling.index (intervalAddress 64 a b d h u v j)) =
        x (RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v j)) := by
  intro child valid words heads x data origin
  have pos := pow_pos Shared50ModularControl.prime_prime.pos w
  have positive : child.Positive := ⟨Nat.zero_lt_one, Nat.zero_lt_one, pow_pos pos _,
    pow_pos pos _, Nat.mul_pos (pow_pos pos _) hW⟩
  exact ⟨_, M8.Machine.ArbitraryWidthOriginalTotalRun.runs caller headers src child hs
    positive valid words heads x data origin, intervalAddress_transpose 64 x⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
