module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoefficientLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords

/-! Emit a full spatial coefficient row while retaining its prepared constants. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem coefficientSweepWords_negative (P q s t u band i : ℕ) :
    coefficientSweepWords true P q s t u band i band = offsetCoefficientWords true P q s t u band i band := by
  apply List.ext_getElem
  · simp [coefficientSweepWords,offsetCoefficientWords]
  · intro n hn hn'
    have hnb : n < band := by simpa [coefficientSweepWords] using hn
    simp only [coefficientSweepWords,offsetCoefficientWords,List.getElem_map,List.getElem_range,
      List.getElem_reverse,List.length_range,ite_true]
    congr 1
    omega

theorem coefficientSweepWords_positive (P q s t u band i : ℕ) :
    coefficientSweepWords false P q s t u band i band = (offsetCoefficientWords false P q s t u band i band).reverse := by
  simp [coefficientSweepWords,offsetCoefficientWords,List.map_reverse]

def preparedUnitCoefficient : TblCode 50 := tblBlock 50 [.zero 25] (.emit 39 25)

theorem preparedUnitCoefficient_do {A V w P q s t u band i : ℕ} (st : TblSt 50 A)
    (hready : CoefficientSweepReady P q s t u band i st) :
    TblDo A V w preparedUnitCoefficient st (fun st' =>
      CoefficientSweepReady P q s t u band i st' ∧
      st'.acc = (csyms A w (signedCoefficientWord false P q s t u band i 0)).reverse++st.acc) 2 := by
  have hz : signedCoefficientWord false P q s t u band i 0 = rationalWord q 1 := by
    simp [signedCoefficientWord,couplingOffset]
  have hout : rationalWord q 1 = (⟨((2^q : ℕ) : ℤ),0⟩ : GaussianInt) := by
    simpa using rationalWord_nat_ratio q 1 1
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact]
  · constructor
    · apply hready.of_frame
      intro r hr
      have hn : r ≠ (25 : Fin 50) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [tblExactList,TblIns.exact,hn]
    · simp [tblExactList,TblIns.exact,hready.grid,hout,hz,csyms,tbl_pairs_red]

def preparedCoefficientRow : TblCode 50 :=
  preparedCoefficientSweep true ;; (preparedUnitCoefficient ;; preparedCoefficientSweep false)

theorem preparedCoefficientRow_do {A w q P s t u band i : ℕ} (st : TblSt 50 A)
    (hready : CoefficientSweepReady P q s t u band i st)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w preparedCoefficientRow st
      (fun st' => CoefficientSweepReady P q s t u band i st' ∧
        st'.acc = (cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++st.acc)
      (2*band*(930*P+372)+8) := by
  have hneg := preparedCoefficientSweep_do (A := A) (w := w) true st hready hs0 hst hP hi
  have hc : TblDo A (liftedCoefficientWidth P q w s t u band) w preparedCoefficientRow st
      (fun st' => CoefficientSweepReady P q s t u band i st' ∧
        st'.acc = (cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++st.acc)
      ((band*(930*P+372)+3)+(2+(band*(930*P+372)+3))) := by
    unfold preparedCoefficientRow
    refine hneg.seq (fun st₁ h₁ => ?_)
    refine (preparedUnitCoefficient_do st₁ h₁.1).seq (fun st₂ h₂ => ?_)
    have hpos := preparedCoefficientSweep_do (A := A) (w := w) false st₂ h₂.1 hs0 hst hP hi
    refine hpos.mono (fun st₃ h₃ => ⟨h₃.1,?_⟩) le_rfl
    rw [h₃.2,h₂.2,h₁.2,coefficientSweepWords_negative,coefficientSweepWords_positive,
      spatialCouplingCoefficientWords_split]
    simp [cstream_append,cstream_cons,cstream_nil,List.reverse_append,List.append_assoc]
  exact hc.mono (fun _ h => h) (by nlinarith)

def coefficientRowCode : TblCode 50 :=
  prepareDirectCoefficient.rename coefficientSweepReg ;;
    (tblBlock 50 [.mul 49 34 43] (.add 37 43 37) ;; preparedCoefficientRow)

theorem coefficientRowCode_do {A w q P s t u band i : ℕ} (st : TblSt 50 A)
    (hP' : st.val 19 = P) (hq : st.val 44 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hi' : st.val 37 = i) (hb : st.val 49 = band)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w coefficientRowCode st
      (fun st' => st'.acc = (cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++st.acc)
      (154*P+4*q+2*band*(930*P+372)+423) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hf := withinCoefficientWidth_fits false P q w s t u band i 0 hi (by omega)
  have hp := (prepareDirectCoefficient_do (A := A) (w := w) (V := V)
    (st.restrict coefficientSweepReg) hP' hq hP hf.semanticWidth (by have hh := hf.gridWidth; omega)).rename
      coefficientSweepReg_injective
  have hc : TblDo A V w coefficientRowCode st
      (fun st' => st'.acc = (cstream A w (spatialCouplingCoefficientWords P q s t u band i)).reverse++st.acc)
      ((154*P+4*q+413)+(2+(2*band*(930*P+372)+8))) := by
    unfold coefficientRowCode
    refine hp.seq (fun st₁ h₁ => ?_)
    have hframe (r : Fin 48) (hr : 34 ≤ r.val) (h39 : r ≠ 39) (h40 : r ≠ 40) (h45 : r ≠ 45) :
        st₁.val (coefficientSweepReg r) = st.val (coefficientSweepReg r) := h₁.1.2.2.2.2.2.2 r hr h39 h40 h45
    have h49 : st₁.val 49 = st.val 49 := h₁.2 49 (fun k he => by
      have hk := k.isLt; have hv := congrArg Fin.val he; simp [coefficientSweepReg] at hv; omega)
    have hs₁ : st₁.val 34 = s := (hframe 34 (by decide) (by decide) (by decide) (by decide)).trans hs
    have hi₁ : st₁.val 37 = i := (hframe 37 (by decide) (by decide) (by decide) (by decide)).trans hi'
    have hb₁ : st₁.val 49 = band := h49.trans hb
    let S₂ : TblSt 50 A := ⟨Function.update (Function.update st₁.val 43 (band*s)) 37 (liftedSource s band i),st₁.acc⟩
    have hcap : i+band*s < 2^V :=
      (liftedCoefficientWidth_fits false P q w s t u band i 0 hi (by omega)).coordinates
    have hlift : TblDo A V w (tblBlock 50 [.mul 49 34 43] (.add 37 43 37)) st₁ (fun st' => st' = S₂) 2 := by
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits,TblIns.exact,hs₁,hi₁,hb₁]
        omega
      · simp [tblExactList,TblIns.exact,hs₁,hi₁,hb₁,S₂,liftedSource]
    refine hlift.seq (fun st₂ he => ?_)
    subst st₂
    have hready : CoefficientSweepReady P q s t u band i S₂ := by
      constructor
      · simpa [S₂,coefficientSweepReg,TblSt.restrict] using h₁.1.1
      · simpa [S₂,coefficientSweepReg,TblSt.restrict] using h₁.1.2.1
      · simpa [S₂,coefficientSweepReg,TblSt.restrict] using h₁.1.2.2.1
      · simpa [S₂] using hs₁
      · simpa [S₂,coefficientSweepReg] using (hframe 35 (by decide) (by decide) (by decide) (by decide)).trans ht
      · simpa [S₂,coefficientSweepReg] using (hframe 36 (by decide) (by decide) (by decide) (by decide)).trans hu
      · simp [S₂]
      · simpa [S₂,coefficientSweepReg,TblSt.restrict] using h₁.1.2.2.2.1
      · simpa [S₂,coefficientSweepReg,TblSt.restrict] using h₁.1.2.2.2.2.1
      · simpa [S₂] using hb₁
    have hacc₁ : st₁.acc = st.acc := h₁.1.2.2.2.2.2.1
    exact (preparedCoefficientRow_do S₂ hready hs0 hst hP hi).mono
      (fun _ h => by simpa [S₂,hacc₁] using h.2) le_rfl
  exact hc.mono (fun _ h => h) (by nlinarith)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
