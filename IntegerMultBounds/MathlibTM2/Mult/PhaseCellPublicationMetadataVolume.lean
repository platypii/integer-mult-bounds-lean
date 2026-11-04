module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderRetirement

/-! Readiness determines the metadata bill independently of ambient contents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  ScalarPlacement.ComputedClassBanks
variable {T A : ℕ}

def publicationHeaderVolume (a b L W V s N : ℕ) : ℕ :=
  a+b+2^a+2^b+L+W+N+V+s+N*V

theorem publicationMetadataVolume_of_input (src : Fin 10 → Fin T) (a b L W V s : ℕ)
    (origins : List ℕ) (tail : List (Fin (A+4))) (S : Stacks (T+tapeCount) A)
    (h : PublicationHeaderInput (Fin.castAdd tapeCount ∘ src) a b L W V s origins tail S) :
    publicationMetadataVolume src S = publicationHeaderVolume a b L W V s origins.length+tail.length := by
  have hlen (j) : (S.R (Fin.castAdd tapeCount (src j))).length =
      (publicationHeaderWords a b L W V s origins tail j).length := h.lengths j
  simp only [publicationMetadataVolume,publicationHeaderCopies,publicationHeaderAssignments,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hlen]
  simp [publicationHeaderWords,publicationHeaderVolume,List.length_flatMap,length_binSyms,Nat.add_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
