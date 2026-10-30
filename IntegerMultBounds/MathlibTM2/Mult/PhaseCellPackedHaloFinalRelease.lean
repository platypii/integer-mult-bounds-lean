module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBetweenInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

/-- Dispose of shared setup once, after the whole fixed-key batch. -/
theorem packedHaloFinalRelease_between_exec
    {p stage q l s t u band a b V w W : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (columns : List (ZMod s → GaussianInt))
    (hlen : columns.length = B.card) (D : ℕ) (tail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hbetween : PackedHaloBetweenInputs p stage q l s t u band a b V w W B.card S)
    (htable : S.R 220 = bandTableWords A w B W columns 0++tail)
    (hstock : BoundaryFactorStock (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (embStk packedBoundaryRecoveryBase S))) D) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ retirePackedBandTableCost B.card W w+packedFactorReleaseCost D ∧
      Exec body packedHaloFinalRelease (mk v S) n
        (mk v' (packedFactorReleased {S with R := Function.update S.R 220 tail})) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedTableRelease_exec B W w columns hlen tail v S
    hbetween.bank.ready.m2n hbetween.bank.ready.sn hbetween.bank.ready.ready.wn htable (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hbetween.native 104 (by decide) (by decide)
      · exact hbetween.native 105 (by decide) (by decide)
      · exact hbetween.native 106 (by decide) (by decide)
      · exact hbetween.native 107 (by decide) (by decide)
      · exact hbetween.native 108 (by decide) (by decide)
      · exact hbetween.native 109 (by decide) (by decide)
      · exact hbetween.native 111 (by decide) (by decide)
      · exact hbetween.native 112 (by decide) (by decide))
  let T : Stacks 248 A := {S with R := Function.update S.R 220 tail}
  have hstockT : ∀ i ∈ packedFactorOwnedIndices, (T.R (packedFactorOwnedReg i)).length ≤ D := by
    intro i hi
    have hb := packedFactorOwnedReg_bounds i hi
    have hi' : 154 ≤ i.val ∧ i ≠ 206 := by simpa [packedFactorOwnedIndices] using hi
    rw [show T.R (packedFactorOwnedReg i) = S.R (packedFactorOwnedReg i) from
      Function.update_of_ne hb.2.2 _ _]
    exact hstock i hi'.1 hi'.2
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedFactorRelease_exec D v₁ T hstockT
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
