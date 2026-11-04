module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderWords

/-! The two count inputs determine the three derived masters. Together with
owned origins they complete the ten-word ABI from five fundamental unary words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T A : ℕ}

def publicationDimensionSourceIndex (j : Fin 5) : Fin 10 := ![3,6,1,0,2] j

theorem publicationDimensionSourceIndex_injective : Function.Injective publicationDimensionSourceIndex := by
  decide +kernel

def publicationDimensionSources (src : Fin 10 → Fin T) : Fin 5 → Fin T := src ∘ publicationDimensionSourceIndex

theorem publicationDimensionSources_injective (src : Fin 10 → Fin T) (hinj : Function.Injective src) :
    Function.Injective (publicationDimensionSources src) := hinj.comp publicationDimensionSourceIndex_injective

noncomputable def publicationGeneratedMasterState (src : Fin 10 → Fin T) (b V : ℕ) (origins : List ℕ)
    (S : Stacks (T+tapeCount) A) :=
  publicationDimensionsLoaded (publicationDimensionSources src) b origins.length
    (originPacketState (Fin.castAdd tapeCount (src 9)) (Fin.castAdd tapeCount (src 6)) V origins S)

theorem publicationHeaderWords_of_generated_masters (src : Fin 10 → Fin T) (hinj : Function.Injective src)
    (b L W V s : ℕ) (origins : List ℕ) (S : Stacks (T+tapeCount) A)
    (hwords : ∀ j, j ∉ [(0 : Fin 10),1,2,6,9] → S.R (Fin.castAdd tapeCount (src j)) =
      publicationHeaderWords (Nat.clog 2 origins.length) b L W V s origins [] j) :
    ∀ j, (publicationGeneratedMasterState src b V origins S).R (Fin.castAdd tapeCount (src j)) =
      publicationHeaderWords (Nat.clog 2 origins.length) b L W V s origins [] j := by
  intro j
  have hc : Function.Injective (fun j => Fin.castAdd tapeCount (src j)) := (Fin.castAdd_injective _ _).comp hinj
  by_cases h0 : j = 0
  · subst j
    simp [publicationGeneratedMasterState,publicationDimensionsLoaded,publicationDimensionSources,
      publicationDimensionSourceIndex,publicationHeaderWords,hc.eq_iff]
  by_cases h1 : j = 1
  · subst j
    simp [publicationGeneratedMasterState,publicationDimensionsLoaded,publicationDimensionSources,
      publicationDimensionSourceIndex,publicationHeaderWords,hc.eq_iff]
  by_cases h2 : j = 2
  · subst j
    simp [publicationGeneratedMasterState,publicationDimensionsLoaded,publicationDimensionSources,
      publicationDimensionSourceIndex,publicationHeaderWords,hc.eq_iff]
  have hd : (publicationGeneratedMasterState src b V origins S).R (Fin.castAdd tapeCount (src j)) =
      (originPacketState (Fin.castAdd tapeCount (src 9)) (Fin.castAdd tapeCount (src 6)) V origins S).R (Fin.castAdd tapeCount (src j)) := by
    apply publicationDimensionsLoaded_off
    · exact hc.ne h1
    · exact hc.ne h0
    · exact hc.ne h2
  rw [hd]
  by_cases h6 : j = 6
  · subst j
    simp [originPacketState,publicationHeaderWords]
  by_cases h9 : j = 9
  · subst j
    simp [originPacketState,publicationHeaderWords,hc.ne (by decide : (9 : Fin 10) ≠ 6)]
  rw [originPacketState_off _ _ _ _ S _ (hc.ne h9) (hc.ne h6)]
  exact hwords j (by simp [h0,h1,h2,h6,h9])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
