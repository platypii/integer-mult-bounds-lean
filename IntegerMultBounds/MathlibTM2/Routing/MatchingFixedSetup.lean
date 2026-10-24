module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionBank

/-! The matching table and resized controls establish the fixed production frame.
The prefix count is installed separately before production. No execution premise is introduced. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N A : ℕ}

def matchingInitialBank (coreWords : Fin N → List (Fin (A + 4))) (p : Par)
    (mate : Fin p.wy → Fin p.wy) (Li Lk Lc : ℕ) : Fin (N + 36) → List (Fin (A + 4)) :=
  matchingProductionBank coreWords (binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2)))
    (matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate)))
    (binSyms Lk p.K) (binSyms Lk p.ρ)

theorem matchingInitialBank_length_le (coreWords : Fin N → List (Fin (A + 4))) (p : Par)
    (mate : Fin p.wy → Fin p.wy) (Li Lk Lc : ℕ) (str : Fin N) (C : ℕ)
    (hcore : ∀ j, j ≠ str → (coreWords j).length ≤ C)
    (j : Fin (N + 36)) (hj : j ≠ matchingCoreEmbed N str) :
    (matchingInitialBank coreWords p mate Li Lk Lc j).length ≤
      C + Lc + p.wy * (2 * (Li + Lk) + 2) + Lk + Lk := by
  simpa only [matchingInitialBank, length_binSyms, matchingEntryWords_length,
    matchingTableEntries, List.length_map, List.length_range] using
    matchingProductionBank_length_le coreWords
      (binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2)))
      (matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate)))
      (binSyms Lk p.K) (binSyms Lk p.ρ) str C hcore j hj

noncomputable def matchingFixedFrame (p : Par) (mate : Fin p.wy → Fin p.wy)
    (hK : 0 < p.K) (hρ : p.ρ < p.K) (hinv : Function.Involutive mate) (reverse : Bool)
    (Li Lk Lc : ℕ) (hwidth : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (coreWords : Fin N → List (Fin (A + 4))) (dst : Fin N) (S : Stacks (N + 36) A)
    (countWord : List (Fin (A + 4)))
    (hR : S.R = matchingProductionBank coreWords countWord
      (matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate)))
      (binSyms Lk p.K) (binSyms Lk p.ρ)) :
    MatchingProductionFrame p mate Li Lk Lc (matchingCoreEmbed N dst) S := by
  have hg (j : Fin 11) : S.R (matchingGenerateSlot N j) = [] := by
    rw [hR]
    exact matchingProductionBank_generate _ _ _ _ _ j
  refine {
    extract := matchingExtractSlot N
    hprefix := matchingExtractSlot_injective N
    gather := matchingGatherSlot N
    hgather := matchingGatherSlot_injective N
    generate := matchingGenerateSlot N
    hgenerate := matchingGenerateSlot_injective N
    hseparate := fun j => matchingGenerateSlot_gather N 7 j
    hdst := fun j => matchingCoreEmbed_generate N dst j
    hjoin := matchingExtractSlot_join N
    hgenerateSource := fun j => matchingGenerateSlot_gather N j 14
    hdstBulk := matchingCoreEmbed_gather N dst 14
    hK := hK
    hρ := hρ
    hinv := hinv
    reverse := reverse
    hwidth := hwidth
    hk := hk
    hinput := ?_
    hblankPrefix := ?_
    hbulkBlank := ?_
    hblankGather := ?_
    hstride := ?_
    hresidue := ?_
    htmpGather := ?_
    hsavedGather := ?_
    haccumGather := ?_
    hblankGenerate := fun j _ _ => hg j
    htmpGenerate := hg 9
    hsavedGenerate := hg 8
    haccumGenerate := hg 10
    hsourceBlank := hg 7 }
  · rw [hR]
    simp [matchingProductionBank_extract, matchingWorkspaceWords]
  · intro j hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rw [hR] <;> simp [matchingProductionBank_extract, matchingWorkspaceWords]
  · rw [hR]
    simp [matchingProductionBank_gather, matchingWorkspaceWords]
  · intro j hj
    have hval : j.val = 0 ∨ j.val = 12 ∨ j.val = 13 ∨ (2 ≤ j.val ∧ j.val < 10) := by
      rcases hj with rfl | rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr h))
    rw [hR]
    rw [matchingProductionBank_gather]
    simp only [matchingWorkspaceWords, ite_eq_right (show 7 + j.val ≠ 0 by omega),
      ite_eq_right (show 7 + j.val ≠ 5 by omega), ite_eq_right (show 7 + j.val ≠ 8 by omega),
      ite_eq_right (show 7 + j.val ≠ 18 by omega)]
  all_goals rw [hR]; simp [matchingProductionBank_gather, matchingWorkspaceWords]

/-- The historical ready-count interface reuses the common fixed frame. -/
noncomputable def matchingFixedSetup (p : Par) (mate : Fin p.wy → Fin p.wy)
    (hK : 0 < p.K) (hρ : p.ρ < p.K) (hinv : Function.Involutive mate) (reverse : Bool)
    (Li Lk Lc : ℕ) (hwidth : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (hcountFit : (p.n * p.K) * (2 * (Li + Lk) + 2) < 2 ^ Lc)
    (coreWords : Fin N → List (Fin (A + 4))) (dst : Fin N) (S : Stacks (N + 36) A)
    (hR : S.R = matchingInitialBank coreWords p mate Li Lk Lc) :
    MatchingProductionSetup p mate Li Lk Lc (matchingCoreEmbed N dst) S := by
  refine {
    toMatchingProductionFrame := matchingFixedFrame p mate hK hρ hinv reverse Li Lk Lc hwidth hk coreWords dst S
      (binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2))) (by simpa only [matchingInitialBank] using hR)
    hcountFit := hcountFit
    hcount := ?_ }
  change S.R (matchingExtractSlot N 0) = _
  rw [hR]
  simp [matchingInitialBank, matchingProductionBank_extract, matchingWorkspaceWords]

end
end IntegerMultBounds.MathlibTM2.Routing
