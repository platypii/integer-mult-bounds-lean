module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseCaller
public import IntegerMultBounds.MathlibTM2.Host.StackStock

/-! Price the raw ABI's actual initial register bank, with arbitrary borrowed tails. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- The register cover leaves only scalar words, one input line and an output
prefix. All native and left-stack spectators remain explicit in the frame. -/
theorem familyInverseCaller_initial_stock_le {Q A W p u l target s t w : ℕ} {U : Type}
    [NeZero s] (v : HS 303 Q A U) (S : Stacks 303 A)
    (F : ZMod s → GaussianInt) (tail wl : List (Fin (A+4))) (hwl : wl.length = W)
    (hscalar : tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t 0 s)))
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → S.R (familyInverseCoreReg i) = [])
    (hsource : S.R 110 = cstream A w (chirpLine s F)++tail) :
    mnSize (mk v S) ≤ hostFrameStock S+303*(tail.length+(S.R 132).length)+303*(s*w+W) := by
  have hR : ∀ i : Fin 303, (S.R i).length ≤ s*w+tail.length+(S.R 132).length+W := by
    intro i
    rcases familyInverseCallerReg_cover i with ⟨j,rfl⟩ | ⟨r,rfl⟩
    · by_cases hj110 : j = 110
      · subst j
        change (S.R 110).length ≤ _
        rw [hsource]
        simp only [List.length_append,length_cstream]
        simp only [chirpLine,List.length_map,List.length_range]
        omega
      by_cases hj132 : j = 132
      · subst j
        change (S.R 132).length ≤ _
        omega
      rw [hblank j hj110 hj132]
      simp
    · have hx := hscalar r
      change S.R (familyInverseSetupReg (inverseScalarReg r)) = _ at hx
      rw [hx]
      have hlen : (tblRho W wl [] (inverseInputScalars p u l target s t 0 s) r).length ≤ W := by
        cases r <;> simp [tblRho,inverseInputScalars,hwl]
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hR i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  rw [mnSize_mk_stock]
  exact (Nat.add_le_add_left hsum _).trans_eq (by ring)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
