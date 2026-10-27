module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget

/-! The canonical retained-inverse precision is an affine function of ordinary parameters and bit counts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN

def inverseExecutionExponent (p l target rowCount band : ℕ) : ℕ :=
  target+2*l+24*p+4*Nat.size (8*p)+Nat.size rowCount+Nat.size (2*band+1)+28

theorem inverseExecutionExponent_eq (p u l target rowCount : ℕ) :
    inverseExecutionExponent p l target rowCount (PhaseCellBand.width p u) =
      executionExponent p l (initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 rowCount) 2) 2 := by
  dsimp [inverseExecutionExponent,executionExponent,inputExponent,sourceExponent,initialSchurTarget,
    boundaryTableBits,boundaryErrorBits,boundaryRecoveryTarget,recoveryTarget,recoveryGuardBits,
    recoveryFirstTarget,recoveryRhsExponent,couplingRowExponent,stableInteriorExponent,couplingCountExponent]
  omega

def tblInverseExponent : TblCode 8 :=
  tblBlock 8 ([.copy 0 7,.add 7 7 7,.add 7 7 7,.add 7 7 7,
    .add 7 7 6,.add 6 7 6,.add 6 2 6,.add 1 1 7,.add 6 7 6,
    .add 3 3 7,.add 7 7 7,.add 6 7 6,.add 6 4 6,.add 6 5 6]++
    List.replicate 27 (.inc 6)) (.inc 6)

def inverseExponentValues (p l target logP logN logBand : ℕ) : Fin 8 → ℕ :=
  ![p,l,target,logP,logN,logBand,target+2*l+24*p+4*logP+logN+logBand+28,4*logP]

theorem tblInverseExponent_do {A W e : ℕ} (st : TblSt 8 A)
    (p l target logP logN logBand : ℕ)
    (h0 : st.val 0 = p) (h1 : st.val 1 = l) (h2 : st.val 2 = target)
    (h3 : st.val 3 = logP) (h4 : st.val 4 = logN) (h5 : st.val 5 = logBand)
    (hroom : target+2*l+24*p+4*logP+logN+logBand+28 < 2^W) :
    TblDo A W e tblInverseExponent st
      (fun z => z.val = inverseExponentValues p l target logP logN logBand ∧ z.acc = st.acc ∧
        ∀ i, z.val i < 2^W) 42 := by
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,h0,h1,h2,h3,h4,h5,List.replicate_succ]
    omega
  · refine ⟨?_,?_,?_⟩
    · funext i
      fin_cases i <;> simp [tblExactList,TblIns.exact,h0,h1,h2,h3,h4,h5,
        inverseExponentValues,List.replicate_succ] <;> omega
    · simp [tblExactList,TblIns.exact,List.replicate_succ]
    · intro i
      fin_cases i <;> simp [tblExactList,TblIns.exact,h0,h1,h2,h3,h4,h5,List.replicate_succ] <;> omega

def tblInverseDimensionWords : TblCode 6 :=
  .seq (tblBlock 6 ([.add 1 1 2,.add 2 2 2,.add 1 1 3,.inc 3,.add 2 2 4]++
    List.replicate 7 (.inc 4)) (.inc 4))
    (tblBlock 6 ([.zero 5,.inc 5]++List.replicate 15 (.add 5 5 5)) (.mul 0 5 5))

def inverseDimensionValues (p E : ℕ) : Fin 6 → ℕ := ![p,E,4*E,2*E+1,8*E+8,2^15*p]

theorem tblInverseDimensionWords_do {A W e : ℕ} (st : TblSt 6 A) (p E : ℕ)
    (hp : st.val 0 = p) (hE : st.val 1 = E) (hroom : 2^15*(p+1)+8*E+9 < 2^W) :
    TblDo A W e tblInverseDimensionWords st
      (fun z => z.val = inverseDimensionValues p E ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W) 31 := by
  have hW : W ≠ 0 := by intro he; subst W; norm_num at hroom
  unfold tblInverseDimensionWords
  apply TblDo.seq (K₁ := 13) (K₂ := 18)
    (P₁ := fun z => z.val 0 = p ∧ z.val 1 = E ∧ z.val 2 = 4*E ∧
      z.val 3 = 2*E+1 ∧ z.val 4 = 8*E+8 ∧ z.acc = st.acc)
  · apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,hE,List.replicate_succ]
      omega
    · simp [tblExactList,TblIns.exact,hE,List.replicate_succ]
      omega
  · intro z ⟨h0,h1,h2,h3,h4,ha⟩
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,h0,List.replicate_succ]
      omega
    · refine ⟨?_,?_,?_⟩
      · funext i
        fin_cases i <;> simp [tblExactList,TblIns.exact,inverseDimensionValues,
          h0,h1,h2,h3,h4,List.replicate_succ,Nat.mul_comm]
      · simpa [tblExactList,TblIns.exact,List.replicate_succ] using ha
      · intro i
        fin_cases i <;> simp [tblExactList,TblIns.exact,h0,h1,h2,h3,h4,List.replicate_succ] <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
