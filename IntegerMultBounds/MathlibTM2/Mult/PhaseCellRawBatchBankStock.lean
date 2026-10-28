module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseBatchDispatchStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost

/-! Price the actual scalar/input/count bank serialized by each dispatch step. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem familyInverseBatch_bank_stock_le {A W p u l target s t a b w : ℕ} [NeZero s]
    (S : Stacks 303 A) (Fs : List (ZMod s → GaussianInt))
    (tail wl : List (Fin (A+4))) (hwl : wl.length = W)
    (hscalar : tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = [])
    (hsource : S.R 110 = cstream A w (Fs.map (chirpLine s)).flatten++tail)
    (hcount : (S.R (familyInverseCoreReg 246)).length = Fs.length) :
    (∑ i, (S.R i).length) ≤ 303*(Fs.length*s*w+tail.length+(S.R 132).length+W+Fs.length) := by
  have hR : ∀ i : Fin 303, (S.R i).length ≤ Fs.length*s*w+tail.length+(S.R 132).length+W+Fs.length := by
    intro i
    rcases familyInverseCallerReg_cover i with ⟨j,rfl⟩ | ⟨r,rfl⟩
    · by_cases hj110 : j = 110
      · subst j
        change (S.R 110).length ≤ _
        rw [hsource,List.length_append,familyBatchWords_length]
        omega
      by_cases hj132 : j = 132
      · subst j
        change (S.R 132).length ≤ _
        omega
      by_cases hj246 : j = 246
      · subst j
        rw [hcount]
        omega
      rw [hblank j hj110 hj132 hj246]
      simp
    · have hx := hscalar r
      change S.R (familyInverseSetupReg (inverseScalarReg r)) = _ at hx
      rw [hx]
      have hlen : (tblRho W wl [] (inverseInputScalars p u l target s t a b) r).length ≤ W := by
        cases r <;> simp [tblRho,inverseInputScalars,hwl]
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hR i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hsum

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
