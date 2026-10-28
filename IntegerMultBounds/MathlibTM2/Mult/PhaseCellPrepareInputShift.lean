module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseScalarSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftScalarSetup

/-! Derive reversible input-conversion controls from the eight ordinary inverse inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def tblPrepareInputShift : TblCode 25 := .seq tblInverseScalars tblInputShiftDimensions

theorem tblPrepareInputShift_do {A W e p u l target s t a b : ℕ} [NeZero s] (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    TblDo A W e tblPrepareInputShift st (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 18 = 4*E ∧ z.val 20 = 8*E+8 ∧ z.val 15 = 4*E-p-1 ∧
      z.val 16 = (8*E+8)-(4*E-p-1) ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      (inverseScalarAtoms p s t u a b+5) := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let Post : TblSt 25 A → Prop := fun z =>
    (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
    z.val 18 = 4*E ∧ z.val 20 = 8*E+8 ∧ z.val 15 = 4*E-p-1 ∧
    z.val 16 = (8*E+8)-(4*E-p-1) ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W
  have hi := tblInverseScalars_do (e := e) st h0 h1 h2 h3 h4 h5 h6 h7 hst ha hb hband
    hbandRoom hgeometryRoom hprecisionRoom hfit
  unfold tblPrepareInputShift
  have hr : TblDo A W e (.seq tblInverseScalars tblInputShiftDimensions) st Post
      (inverseScalarAtoms p s t u a b+5) := hi.seq (fun zI ⟨hkeepI,hbandI,hN,hE,hq,hstage,hw,hP,haccI,hfitI⟩ => by
    have hqroom : 8*E+8 < 2^W := by rw [←hw]; exact hfitI 20
    have hs := tblInputShiftDimensions_do (e := e) zI ((hkeepI 0).trans h0) hq hw
      (by dsimp [E,inverseExecutionExponent]; omega) (by omega) hqroom
    exact (tblDo_with_fits hs hfitI).mono (P' := Post) (K' := 5)
      (fun z ⟨⟨hoff,hd,hk,hunit,haccS⟩,hfitZ⟩ => by
        refine ⟨?_,?_,?_,hd,hk,haccS.trans haccI,hfitZ⟩
        · intro i
          have hne (n : Fin 25) (hn : 8 ≤ n.val) : (⟨i.val,by omega⟩ : Fin 25) ≠ n := by
            intro he
            have hv := congrArg (fun k : Fin 25 => k.val) he
            have hi := i.isLt
            change i.val = n.val at hv
            omega
          exact (hoff _ (hne 15 (by decide)) (hne 16 (by decide)) (hne 17 (by decide))).trans (hkeepI i)
        · exact (hoff 18 (by decide) (by decide) (by decide)).trans hq
        · exact (hoff 20 (by decide) (by decide) (by decide)).trans hw) (le_refl _))
  exact hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
