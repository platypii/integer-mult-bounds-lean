module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundSelectionSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseRoundVariables

/-! Rounding setup needs the retained precision, not another geometry computation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblPrepareRetainedRound : TblCode 25 :=
  .seq tblRoundSelection
    (tblBlock 25 ([.add 18 18 20]++List.replicate 8 (.inc 20)++[.zero 15,.zero 16]) (.zero 17))

theorem tblPrepareRetainedRound_do {A W e p q : ℕ} (st : TblSt 25 A)
    (hp : st.val 0 = p) (hq : st.val 18 = q)
    (hselectionRoom : 8*(p+2) < 2^W) (hwidthRoom : 2*q+8 < 2^W)
    (hfit : ∀ i, st.val i < 2^W) :
    TblDo A W e tblPrepareRetainedRound st (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 18 = q ∧ z.val 20 = 2*q+8 ∧ z.val 8 = p+8 ∧
      z.val 14 = inverseNormalizationShift p ∧ z.val 15 = 0 ∧ z.val 16 = 0 ∧ z.val 17 = 0 ∧
      z.acc = st.acc ∧ ∀ i, z.val i < 2^W) (4*Nat.size (4*p)+31) := by
  unfold tblPrepareRetainedRound
  have hs := tblRoundSelection_do (e := e) st hp hselectionRoom hfit
  let Post : TblSt 25 A → Prop := (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 18 = q ∧ z.val 20 = 2*q+8 ∧ z.val 8 = p+8 ∧
      z.val 14 = inverseNormalizationShift p ∧ z.val 15 = 0 ∧ z.val 16 = 0 ∧ z.val 17 = 0 ∧
      z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
  have h : TblDo A W e
      (.seq tblRoundSelection
        (tblBlock 25 ([.add 18 18 20]++List.replicate 8 (.inc 20)++[.zero 15,.zero 16]) (.zero 17)))
      st Post ((4*Nat.size (4*p)+19)+12) := hs.seq (fun z ⟨hkeep,hmag,hshift,hacc,hq',_,hfitZ⟩ => by
    let F : TblSt 25 A := ⟨Function.update (Function.update (Function.update
      (Function.update z.val 20 (2*q+8)) 15 0) 16 0) 17 0,z.acc⟩
    have hqZ : z.val 18 = q := hq'.trans hq
    have hb : TblDo A W e
        (tblBlock 25 ([.add 18 18 20]++List.replicate 8 (.inc 20)++[.zero 15,.zero 16]) (.zero 17))
        z (fun z' => z' = F) 12 :=
      TblDo.block _ _
        (by simp [tblFitsList,TblIns.fits,TblIns.exact,hqZ,List.replicate_succ]; omega)
        (by simp [tblExactList,TblIns.exact,hqZ,List.replicate_succ,F,two_mul,Nat.add_assoc])
    exact (tblDo_with_fits hb hfitZ).mono
      (P' := fun z' =>
        (∀ i : Fin 8, z'.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
        z'.val 18 = q ∧ z'.val 20 = 2*q+8 ∧ z'.val 8 = p+8 ∧
        z'.val 14 = inverseNormalizationShift p ∧ z'.val 15 = 0 ∧ z'.val 16 = 0 ∧ z'.val 17 = 0 ∧
        z'.acc = st.acc ∧ ∀ i, z'.val i < 2^W)
      (K' := 12) (fun z' ⟨he,hfits⟩ => by
        subst z'
        refine ⟨?_,?_,by simp [F],?_,?_,by simp [F],by simp [F],by simp [F],hacc,hfits⟩
        · intro i
          have hi := hkeep i
          fin_cases i <;> simpa [F] using hi
        · simpa [F] using hqZ
        · simpa [F] using hmag
        · simpa [F] using hshift) (le_refl _))
  exact h.mono (fun _ hz => hz) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
