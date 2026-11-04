module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedOriginPacket
public import Mathlib.Data.Fin.VecNotation

/-! Publication packets have one shared layout, independent of the numerical
producer. The origin and count fields are filled by an actual owned scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast
variable {T A : ℕ}

/-- The rectangular publication and ambient word bounds shared by callers. -/
structure PublicationShapeBounds (a b L W V s N : ℕ) : Prop where
  packetPositive : 0 < L*W
  stageBits : a+b < V
  volumeFit : (L*W)*2^(a+b) < 2^V
  rowCapacity : N ≤ 2^a
  wordFit : W < 2^V
  ambientFit : s < 2^V
  ambientVolumeFit : s*W < 2^V

def publicationHeaderWords (a b L W V s : ℕ) (origins : List ℕ)
    (originTail : List (Fin (A+4))) : Fin 10 → List (Fin (A+4)) :=
  ![List.replicate a tick,List.replicate b tick,List.replicate (2^a) tick,
    List.replicate (2^b) tick,List.replicate L tick,List.replicate W tick,
    List.replicate origins.length tick,List.replicate V tick,List.replicate s tick,
    origins.flatMap (binSyms V)++originTail]

/-- Unary controls are read by length. The row counter and binary origin packet
retain their exact contents for the destructive publication sweep. -/
structure PublicationHeaderInput (src : Fin 10 → Fin T) (a b L W V s : ℕ)
    (origins : List ℕ) (originTail : List (Fin (A+4))) (S : Stacks T A) : Prop where
  lengths : ∀ j, (S.R (src j)).length =
    (publicationHeaderWords a b L W V s origins originTail j).length
  count : S.R (src 6) = List.replicate origins.length tick
  packet : S.R (src 9) = origins.flatMap (binSyms V)++originTail

theorem publicationHeaderWords_of_owned_packet (src : Fin 10 → Fin T) (hinj : Function.Injective src)
    (a b L W V s : ℕ) (origins : List ℕ) (S : Stacks T A)
    (hwords : ∀ j, j ≠ 6 → j ≠ 9 → S.R (src j) = publicationHeaderWords a b L W V s origins [] j) :
    ∀ j, (originPacketState (src 9) (src 6) V origins S).R (src j) = publicationHeaderWords a b L W V s origins [] j := by
  intro j
  by_cases hc : j = 6
  · subst j
    simp [originPacketState,publicationHeaderWords]
  by_cases hp : j = 9
  · subst j
    simp [originPacketState,publicationHeaderWords,hinj.ne (by decide : (9 : Fin 10) ≠ 6)]
  rw [originPacketState_off _ _ _ _ S _ (hinj.ne hp) (hinj.ne hc)]
  exact hwords j hc hp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
