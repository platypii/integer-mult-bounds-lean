module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseScalarSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundSelectionSetup

/-! Derive the rounding scalar view directly from the inverse's eight ordinary inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def tblPrepareInverseRound : TblCode 25 :=
  .seq tblInverseScalars (.seq tblRoundSelection (tblBlock 25 [.zero 15,.zero 16] (.zero 17)))

theorem tblPrepareInverseRound_do {A W e p u l target s t a b : ℕ} [NeZero s] (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let E := inverseExecutionExponent p l target N band
    TblDo A W e tblPrepareInverseRound st (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 18 = 4*E ∧ z.val 20 = 8*E+8 ∧ z.val 8 = p+8 ∧
      z.val 14 = inverseNormalizationShift p ∧ z.val 15 = 0 ∧ z.val 16 = 0 ∧ z.val 17 = 0 ∧
      z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      (inverseScalarAtoms p s t u a b+(4*Nat.size (4*p)+22)) := by
  dsimp only
  let Post : TblSt 25 A → Prop := fun z =>
          (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
          z.val 18 = 4*inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) ∧
          z.val 20 = 8*inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8 ∧
          z.val 8 = p+8 ∧ z.val 14 = inverseNormalizationShift p ∧
          z.val 15 = 0 ∧ z.val 16 = 0 ∧ z.val 17 = 0 ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W
  have hi := tblInverseScalars_do (e := e) st h0 h1 h2 h3 h4 h5 h6 h7 hst haS hbS hbandS
    hbandRoom hgeometryRoom hprecisionRoom hfit
  have hselectRoom : 8*(p+2) < 2^W := by
    dsimp [inversePrecisionRoom] at hprecisionRoom
    omega
  unfold tblPrepareInverseRound
  have hr : TblDo A W e
      (.seq tblInverseScalars (.seq tblRoundSelection (tblBlock 25 [.zero 15,.zero 16] (.zero 17))))
      st Post (inverseScalarAtoms p s t u a b+((4*Nat.size (4*p)+19)+3)) := hi.seq (fun zI ⟨hkeepI,hband,hN,hE,hq,hstage,hw,hP,haccI,hfitI⟩ => by
    have hs := tblRoundSelection_do (e := e) zI ((hkeepI 0).trans h0) hselectRoom hfitI
    exact hs.seq (fun zS ⟨hkeepS,hmag,hshift,haccS,hqS,hwS,hfitS⟩ => by
      let zF : TblSt 25 A := ⟨Function.update (Function.update (Function.update zS.val 15 0) 16 0) 17 0,zS.acc⟩
      have hc : TblDo A W e (tblBlock 25 [.zero 15,.zero 16] (.zero 17)) zS (fun z => z = zF) 3 :=
        TblDo.block _ _ (by simp [tblFitsList,TblIns.fits]) (by simp [tblExactList,TblIns.exact,zF])
      exact (tblDo_with_fits hc hfitS).mono
        (P' := Post)
        (K' := 3) (fun z ⟨he,hfitZ⟩ => by
          subst z
          refine ⟨?_,?_,?_,?_,?_,by simp [zF],by simp [zF],by simp [zF],haccS.trans haccI,hfitZ⟩
          · intro i
            have hv := (hkeepS i).trans (hkeepI i)
            fin_cases i <;> simpa [zF] using hv
          · simpa [zF,hqS] using hq
          · simpa [zF,hwS] using hw
          · simpa [zF] using hmag
          · simpa [zF] using hshift) (le_refl _)))
  exact hr.mono (fun _ hz => hz) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
