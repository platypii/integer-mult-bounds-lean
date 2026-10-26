module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSimilarityArgumentAt

/-! Construct the two shared natural similarity-argument constants while
retaining coordinates, sampled numerators and arithmetic-grid powers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def withinSimilaritySetup : TblCode 48 :=
  tblBlock 48 [.add 34 34 47, .sub 35 34 44, .mul 34 44 44, .add 44 44 44] (.add 44 44 44)

theorem withinSimilaritySetup_do {A V w s t : ℕ} (st : TblSt 48 A)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hst : s < t)
    (hsV : 2*s < 2^V) (htV : t < 2^V) (hdenV : similarityDenominator s t < 2^V) :
    TblDo A V w withinSimilaritySetup st (fun st' =>
      st'.val 47 = 2*s ∧ st'.val 44 = similarityDenominator s t ∧ st'.acc = st.acc ∧
      ∀ r, r ≠ 44 → r ≠ 47 → st'.val r = st.val r) 5 := by
  have hD : (s*(t-s)+s*(t-s))+(s*(t-s)+s*(t-s)) = similarityDenominator s t := by
    unfold similarityDenominator
    ring
  have hbound : 4*(s*(t-s)) < 2^V := by
    simpa [similarityDenominator, Nat.mul_assoc] using hdenV
  have hDtwo : 2*(2*(s*(t-s))) = similarityDenominator s t := by
    unfold similarityDenominator
    ring
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,ht,hst.le,hD]
    omega
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    simp [hs,ht,← two_mul,hDtwo]
    intro r hr44 hr47
    simp [hr44,hr47]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
