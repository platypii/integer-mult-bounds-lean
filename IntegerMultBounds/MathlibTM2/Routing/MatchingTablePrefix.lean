module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPrefixExtract
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileGather

/-! Extract the bulk endpoint table from a complete coordinate-ordered matching
table. Prefix traversal is generated from its binary byte count and fully erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

theorem matchingEntryWords_append (L : ℕ) (xs ys : List (ℕ × ℕ)) :
    matchingEntryWords (A := A) L (xs ++ ys) = matchingEntryWords L xs ++ matchingEntryWords L ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, matchingEntryWords, ih, List.append_assoc]

theorem matchingTableEntries_take (N B : ℕ) (hB : B ≤ N) (mate : ℕ → ℕ) :
    (matchingTableEntries N mate).take B = matchingTableEntries B mate := by
  simp only [matchingTableEntries, ← List.map_take, List.take_range, Nat.min_eq_left hB]

theorem matchingTableWords_split (N B L : ℕ) (hB : B ≤ N) (mate : ℕ → ℕ) :
    matchingEntryWords (A := A) L (matchingTableEntries N mate) =
      matchingEntryWords L (matchingTableEntries B mate) ++
        matchingEntryWords L ((matchingTableEntries N mate).drop B) := by
  rw [← matchingTableEntries_take N B hB mate, ← matchingEntryWords_append, List.take_append_drop]

theorem matchingTablePrefix_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (N B L Lc : ℕ) (hB : B ≤ N)
    (mate : ℕ → ℕ) (hfit : B * (2 * L + 2) < 2 ^ Lc)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R (rg 0) = binSyms Lc (B * (2 * L + 2)))
    (hinput : S.R (rg 5) = matchingEntryWords L (matchingTableEntries N mate))
    (hblank : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryPrefixExtractCost Lc (B * (2 * L + 2)) ∧
      Exec body (binaryPrefixExtractProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 6) (matchingEntryWords L (matchingTableEntries B mate) ++ S.R (rg 6)) }) := by
  have hlength : (matchingEntryWords (A := A) L (matchingTableEntries B mate)).length = B * (2 * L + 2) := by
    simp [matchingEntryWords_length, matchingTableEntries]
  obtain ⟨v', steps, hu, hm, he⟩ := binaryPrefixExtract_exec body rg hrg Lc
    (matchingEntryWords L (matchingTableEntries B mate))
    (matchingEntryWords L ((matchingTableEntries N mate).drop B))
    (by simpa only [hlength] using hfit) v S
    (by simpa only [hlength] using hcount)
    (hinput.trans (matchingTableWords_split N B L hB mate)) hblank
  exact ⟨v', steps, hu, by simpa only [hlength] using hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
