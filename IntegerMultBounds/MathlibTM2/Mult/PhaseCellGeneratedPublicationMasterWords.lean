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

/-- The five retained controls after origins and dimension masters are generated. -/
theorem publicationFundamentalIndex_cases (j : Fin 10)
    (hj : j ∉ [(0 : Fin 10),1,2,6,9]) : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 := by
  revert j
  decide +kernel

noncomputable def publicationGeneratedMasterState (src : Fin 10 → Fin T) (b V : ℕ) (origins : List ℕ)
    (S : Stacks (T+tapeCount) A) :=
  publicationDimensionsLoaded (publicationDimensionSources src) b origins.length
    (originPacketState (Fin.castAdd tapeCount (src 9)) (Fin.castAdd tapeCount (src 6)) V origins S)

theorem publicationHeaderInput_of_generated_masters (src : Fin 10 → Fin T) (hinj : Function.Injective src)
    (b L W V s : ℕ) (origins : List ℕ) (S : Stacks (T+tapeCount) A)
    (hlengths : ∀ j, j ∉ [(0 : Fin 10),1,2,6,9] → (S.R (Fin.castAdd tapeCount (src j))).length =
      (publicationHeaderWords (A := A) (Nat.clog 2 origins.length) b L W V s origins [] j).length) :
    PublicationHeaderInput (Fin.castAdd tapeCount ∘ src) (Nat.clog 2 origins.length) b L W V s origins []
      (publicationGeneratedMasterState src b V origins S) := by
  have hc : Function.Injective (fun j => Fin.castAdd tapeCount (src j)) := (Fin.castAdd_injective _ _).comp hinj
  have hcount : (publicationGeneratedMasterState src b V origins S).R (Fin.castAdd tapeCount (src 6)) =
      List.replicate origins.length tick := by
    unfold publicationGeneratedMasterState
    rw [publicationDimensionsLoaded_off]
    · simp [originPacketState]
    · exact hc.ne (by decide)
    · exact hc.ne (by decide)
    · exact hc.ne (by decide)
  have hpacket : (publicationGeneratedMasterState src b V origins S).R (Fin.castAdd tapeCount (src 9)) =
      origins.flatMap (binSyms V)++[] := by
    unfold publicationGeneratedMasterState
    rw [publicationDimensionsLoaded_off]
    · simp [originPacketState,hc.ne (by decide : (9 : Fin 10) ≠ 6)]
    · exact hc.ne (by decide)
    · exact hc.ne (by decide)
    · exact hc.ne (by decide)
  refine ⟨?_,hcount,hpacket⟩
  intro j
  change ((publicationGeneratedMasterState src b V origins S).R (Fin.castAdd tapeCount (src j))).length = _
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
      publicationDimensionSourceIndex,publicationHeaderWords]
  by_cases h6 : j = 6
  · subst j; simp [hcount,publicationHeaderWords]
  by_cases h9 : j = 9
  · subst j; simp [hpacket,publicationHeaderWords]
  unfold publicationGeneratedMasterState
  rw [publicationDimensionsLoaded_off _ _ _ _ _ (hc.ne h1) (hc.ne h0) (hc.ne h2),
    originPacketState_off _ _ _ _ S _ (hc.ne h9) (hc.ne h6)]
  exact hlengths j (by simp [h0,h1,h2,h6,h9])

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
