module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandParameterSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCountSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedInversePrecision

/-! Generate inverse band, boundary cardinality and arithmetic dimensions from the eight ordinary scalar inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace InverseScalars

def band : Fin 7 → Fin 25 := ![0,1,8,9,10,11,12]
def count : Fin 17 → Fin 25 := ![4,5,11,13,6,7,14,15,16,17,18,19,20,21,22,23,24]
def precision : Fin 18 → Fin 25 := ![0,2,3,24,11,8,9,10,12,13,14,15,16,17,18,19,20,21]

theorem band_injective : Function.Injective band := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [band]
theorem count_injective : Function.Injective count := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [count]
theorem precision_injective : Function.Injective precision := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [precision]

end InverseScalars

def tblInverseScalars : TblCode 25 :=
  .seq (tblBandParameter.rename InverseScalars.band)
    (.seq (boundaryCountCode.rename InverseScalars.count)
      (tblComputedInversePrecision.rename InverseScalars.precision))

noncomputable def inverseScalarAtoms (p s t u a b : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  (4*band+12)+(31*s+4)+inversePrecisionAtoms p N band

theorem tblInverseScalars_do {A W e p u l target s t a b : ℕ} [NeZero s] (st : TblSt 25 A)
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
    TblDo A W e tblInverseScalars st (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 11 = band ∧ z.val 24 = N ∧ z.val 13 = E ∧ z.val 18 = 4*E ∧
      z.val 19 = 2*E+1 ∧ z.val 20 = 8*E+8 ∧ z.val 21 = 2^15*p ∧
      z.acc = st.acc ∧ ∀ i, z.val i < 2^W) (inverseScalarAtoms p s t u a b) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let E := inverseExecutionExponent p l target N band
  have hband := tblDo_with_fits ((tblBandParameter_do (A := A) (W := W) (e := e)
    (st.restrict InverseScalars.band) p u h0 h1 hbandRoom).rename InverseScalars.band_injective) hfit
  unfold tblInverseScalars
  have hr : TblDo A W e tblInverseScalars st (fun z =>
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.val 11 = band ∧ z.val 24 = N ∧ z.val 13 = E ∧ z.val 18 = 4*E ∧
      z.val 19 = 2*E+1 ∧ z.val 20 = 8*E+8 ∧ z.val 21 = 2^15*p ∧
      z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      ((4*band+12)+((31*s+4)+inversePrecisionAtoms p N band)) := hband.seq (fun zB ⟨⟨⟨hvB,haB,_⟩,hoffB⟩,hfitB⟩ => by
    have hv (i : Fin 7) : zB.val (InverseScalars.band i) = bandParameterValues p u i := congrFun hvB i
    have hsB : zB.val 4 = s := (hoffB 4 (by intro i; fin_cases i <;> decide)).trans h4
    have htB : zB.val 5 = t := (hoffB 5 (by intro i; fin_cases i <;> decide)).trans h5
    have haB' : zB.val 6 = a := (hoffB 6 (by intro i; fin_cases i <;> decide)).trans h6
    have hbB : zB.val 7 = b := (hoffB 7 (by intro i; fin_cases i <;> decide)).trans h7
    have hcountFit : ∀ i, (zB.restrict InverseScalars.count).val i < 2^W := fun i => hfitB _
    have hcount := tblDo_with_fits ((boundaryCountCode_do (A := A) (V := W) (w := e)
      (zB.restrict InverseScalars.count) hsB htB (hv 5) haB' hbB hst haS hbS hbandS hgeometryRoom hcountFit).rename
        InverseScalars.count_injective) hfitB
    exact hcount.seq (fun zC ⟨⟨⟨hN,haC,hfC,_⟩,hoffC⟩,hfitC⟩ => by
      have hf (i : Fin 17) (hi : i.val < 6) (hindex : i ≠ 3) :
          zC.val (InverseScalars.count i) = zB.val (InverseScalars.count i) := hfC i hi hindex
      have hpC : zC.val 0 = p := (hoffC 0 (by intro i; fin_cases i <;> decide)).trans (hv 0)
      have hlC : zC.val 2 = l := (hoffC 2 (by intro i; fin_cases i <;> decide)).trans
        ((hoffB 2 (by intro i; fin_cases i <;> decide)).trans h2)
      have htC : zC.val 3 = target := (hoffC 3 (by intro i; fin_cases i <;> decide)).trans
        ((hoffB 3 (by intro i; fin_cases i <;> decide)).trans h3)
      have hbC : zC.val 11 = band := (hf 2 (by decide) (by decide)).trans (hv 5)
      have hprecFit : ∀ i, (zC.restrict InverseScalars.precision).val i < 2^W := fun i => hfitC _
      have hprec := tblDo_with_fits ((tblComputedInversePrecision_do (A := A) (W := W) (e := e)
        (zC.restrict InverseScalars.precision) p l target N band hpC hlC htC hN hbC hprecisionRoom hprecFit).rename
          InverseScalars.precision_injective) hfitC
      exact hprec.mono (P' := fun z =>
        (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
        z.val 11 = band ∧ z.val 24 = N ∧ z.val 13 = E ∧ z.val 18 = 4*E ∧ z.val 19 = 2*E+1 ∧
        z.val 20 = 8*E+8 ∧ z.val 21 = 2^15*p ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
        (fun zP ⟨⟨⟨hpP,hlP,htP,hNP,hbP,hEP,hqP,hstageP,hwP,hscaledP,haP,_⟩,hoffP⟩,hfitP⟩ => by
          refine ⟨?_,hbP,hNP,hEP,hqP,hstageP,hwP,hscaledP,haP.trans (haC.trans haB),hfitP⟩
          intro i
          fin_cases i
          · exact hpP.trans h0.symm
          · exact (hoffP 1 (by intro j; fin_cases j <;> decide)).trans
              ((hoffC 1 (by intro j; fin_cases j <;> decide)).trans ((hv 1).trans h1.symm))
          · exact hlP.trans h2.symm
          · exact htP.trans h3.symm
          · exact (hoffP 4 (by intro j; fin_cases j <;> decide)).trans ((hf 0 (by decide) (by decide)).trans
              (hoffB 4 (by intro j; fin_cases j <;> decide)))
          · exact (hoffP 5 (by intro j; fin_cases j <;> decide)).trans ((hf 1 (by decide) (by decide)).trans
              (hoffB 5 (by intro j; fin_cases j <;> decide)))
          · exact (hoffP 6 (by intro j; fin_cases j <;> decide)).trans ((hf 4 (by decide) (by decide)).trans
              (hoffB 6 (by intro j; fin_cases j <;> decide)))
          · exact (hoffP 7 (by intro j; fin_cases j <;> decide)).trans ((hf 5 (by decide) (by decide)).trans
              (hoffB 7 (by intro j; fin_cases j <;> decide)))) (le_refl _)))
  exact hr.mono (fun _ h => h) (by dsimp [inverseScalarAtoms,band,N]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
