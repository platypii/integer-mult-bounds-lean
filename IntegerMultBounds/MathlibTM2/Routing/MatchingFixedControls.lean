module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedSetup
public import IntegerMultBounds.MathlibTM2.Routing.MatchingControlScope

/-! Compact controls use three core inputs and reuse the fixed producer scratch.
Their two resized outputs occupy exactly the gather stride and residue slots. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {N A : ℕ}

def matchingFixedControlSlot (inputs : Fin 3 → Fin N) : Fin 11 → Fin (N + 36) :=
  ![matchingCoreEmbed N (inputs 0), matchingCoreEmbed N (inputs 1),
    matchingGatherSlot N 1, matchingGatherSlot N 11,
    matchingGenerateSlot N 0, matchingGenerateSlot N 1, matchingGenerateSlot N 2,
    matchingCoreEmbed N (inputs 2),
    matchingGenerateSlot N 3, matchingGenerateSlot N 4, matchingGenerateSlot N 5]

theorem matchingFixedControlSlot_injective (inputs : Fin 3 → Fin N)
    (hin : Function.Injective inputs) : Function.Injective (matchingFixedControlSlot inputs) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [matchingFixedControlSlot, (matchingCoreEmbed_injective N).eq_iff,
      hin.eq_iff, (matchingGatherSlot_injective N).eq_iff,
      (matchingGenerateSlot_injective N).eq_iff,
      matchingCoreEmbed_gather, matchingCoreEmbed_generate, matchingGenerateSlot_gather,
      Ne.symm (matchingCoreEmbed_gather N _ _),
      Ne.symm (matchingCoreEmbed_generate N _ _),
      Ne.symm (matchingGenerateSlot_gather N _ _)]

theorem matchingFixedControlBank (inputs : Fin 3 → Fin N)
    (coreWords : Fin N → List (Fin (A + 4)))
    (count table : List (Fin (A + 4))) (L K r : ℕ) :
    matchingControlBank (matchingProductionBank coreWords count table [] [])
      (matchingFixedControlSlot inputs) L K r =
      matchingProductionBank coreWords count table (binSyms L K) (binSyms L r) := by
  change Function.update (Function.update (matchingProductionBank coreWords count table [] [])
    (matchingGatherSlot N 11) (binSyms L r)) (matchingGatherSlot N 1) (binSyms L K) = _
  exact matchingProductionBank_update_controls coreWords count table (binSyms L K) (binSyms L r)

theorem matchingFixedControlBlank (inputs : Fin 3 → Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (count table : List (Fin (A + 4)))
    (j : Fin 11) (h0 : j ≠ 0) (h1 : j ≠ 1) (h7 : j ≠ 7) :
    matchingProductionBank coreWords count table [] [] (matchingFixedControlSlot inputs j) = [] := by
  fin_cases j <;> simp_all [matchingFixedControlSlot, matchingProductionBank_gather,
    matchingProductionBank_generate, matchingWorkspaceWords]

/-- The actual compact-control installer supplies the fixed producer frame;
no separately supplied frame or prefix-count word is needed. -/
noncomputable def matchingFixedControlFrame
    (inputs : Fin 3 → Fin N) (p : Par) (mate : Fin p.wy → Fin p.wy)
    (hK : 0 < p.K) (hρ : p.ρ < p.K) (hinv : Function.Involutive mate) (reverse : Bool)
    (Li Lk Lc : ℕ) (hwidth : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (coreWords : Fin N → List (Fin (A + 4))) (dst : Fin N) (S : Stacks (N + 36) A)
    (hR : S.R = matchingControlBank
      (matchingProductionBank coreWords []
        (matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate))) [] [])
      (matchingFixedControlSlot inputs) Lk p.K p.ρ) :
    MatchingProductionFrame p mate Li Lk Lc (matchingCoreEmbed N dst) S := by
  apply matchingFixedFrame p mate hK hρ hinv reverse Li Lk Lc hwidth hk coreWords dst S []
  rw [hR, matchingFixedControlBank]

end IntegerMultBounds.MathlibTM2.Routing
