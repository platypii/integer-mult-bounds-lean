module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedSelectedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhaseCoefficientFromSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientOffsetLoop

/-! Prepared coefficient steps retain constants and isolate binary sweep controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def coefficientSweepReg (i : Fin 48) : Fin 50 := ⟨i.val,by omega⟩

theorem coefficientSweepReg_injective : Function.Injective coefficientSweepReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 50 => k.val) he)

def preparedCoefficientEntry : TblCode 50 := phaseCoefficientFromSource.rename coefficientSweepReg

theorem preparedCoefficientEntry_do {A w q P s t u band i d : ℕ}
    (negative : Bool) (st : TblSt 50 A)
    (hsource : st.val 26 = similarityGridNumerator P s t u (liftedSource s band i))
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = liftedSource s band i) (hk : st.val 38 = liftedTarget negative s band i d)
    (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band) (hi : i < s) (hd0 : 0 < d) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w preparedCoefficientEntry st
      (fun st' => st'.acc = (csyms A w (signedCoefficientWord negative P q s t u band i d)).reverse++st.acc ∧
        st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
        (∀ r : Fin 50, 34 ≤ r.val → r.val ≤ 40 → st'.val r = st.val r) ∧
        st'.val 48 = st.val 48 ∧ st'.val 49 = st.val 49 ∧ st'.val 26 = st.val 26) (620*P+251) := by
  have hdist := lifted_naturalDistance negative (s := s) (i := i) hs0 hd
  have hjk : liftedSource s band i ≠ liftedTarget negative s band i d := by
    intro he
    rw [he] at hdist
    simp [naturalDistance] at hdist
    omega
  have hc := phaseCoefficientFromSource_frame_do (A := A) (w := w) negative
    (st.restrict coefficientSweepReg) hsource hpi hP' hneg hs ht hu hj hk hq hpowP hs0 hst hP hd hi hjk
  have hr := (hc.rename coefficientSweepReg_injective).keep
  refine hr.mono (fun st' hfull => ?_) le_rfl
  have h := hfull.1
  refine ⟨?_,h.1.2.1,h.1.2.2.1,h.1.2.2.2.1,?_,?_,?_,?_⟩
  · simpa only [TblSt.restrict_acc,signedCoefficientWord,lifted_entry negative P t u hs0 hd] using h.1.1
  · intro r hrlo hrhi
    let k : Fin 48 := ⟨r.val,by omega⟩
    have he : coefficientSweepReg k = r := Fin.ext rfl
    simpa only [TblSt.restrict_val,he] using h.1.2.2.2.2 k hrlo hrhi
  · exact h.2 48 (fun k he => by have hv := congrArg Fin.val he; have hk := k.isLt; simp [coefficientSweepReg] at hv; omega)
  · exact h.2 49 (fun k he => by have hv := congrArg Fin.val he; have hk := k.isLt; simp [coefficientSweepReg] at hv; omega)

  · exact hfull.2 26 (by decide)

def coefficientSweepStep (negative : Bool) : TblCode 50 :=
  (if negative then tblBlock 50 [.sub 37 49 38] (.add 38 48 38)
    else tblBlock 50 [.add 37 48 38] (.inc 38)) ;; preparedCoefficientEntry

theorem coefficientSweepStep_do {A w q P s t u band i n : ℕ}
    (negative : Bool) (st : TblSt 50 A)
    (hsource : st.val 26 = similarityGridNumerator P s t u (liftedSource s band i))
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = liftedSource s band i) (hindex : st.val 48 = n) (hband : st.val 49 = band)
    (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hn : n < band) (hi : i < s) :
    let d := if negative then band-n else n+1
    TblDo A (liftedCoefficientWidth P q w s t u band) w (coefficientSweepStep negative) st
      (fun st' => st'.acc = (csyms A w (signedCoefficientWord negative P q s t u band i d)).reverse++st.acc ∧
        st'.val 18 = st.val 18 ∧ st'.val 19 = st.val 19 ∧ st'.val 22 = st.val 22 ∧
        (∀ r : Fin 50, 34 ≤ r.val → r.val ≤ 40 → r ≠ 38 → st'.val r = st.val r) ∧
        st'.val 48 = st.val 48 ∧ st'.val 49 = st.val 49 ∧ st'.val 26 = st.val 26) (620*P+253) := by
  dsimp only
  let V := liftedCoefficientWidth P q w s t u band
  let d := if negative then band-n else n+1
  have hd : d ≤ band := by dsimp [d]; split <;> omega
  have hcap : i+band*s+band < 2^V :=
    (liftedCoefficientWidth_fits negative P q w s t u band i band hi le_rfl).coordinates
  have hbase : band ≤ liftedSource s band i := offset_le_liftedSource hs0 le_rfl
  let S₁ : TblSt 50 A := ⟨Function.update st.val 38 (liftedTarget negative s band i d),st.acc⟩
  have hp : TblDo A V w
      (if negative then tblBlock 50 [.sub 37 49 38] (.add 38 48 38)
        else tblBlock 50 [.add 37 48 38] (.inc 38)) st (fun st' => st' = S₁) 2 := by
    cases negative <;> apply TblDo.block
    all_goals first
    | (simp [tblFitsList,TblIns.fits,TblIns.exact,hj,hindex,hband,liftedSource] at *; omega)
    | (dsimp only [liftedSource] at hbase
       simp [tblExactList,TblIns.exact,S₁,hj,hindex,hband,liftedTarget,d,liftedSource]
       congr 1 <;> omega)
  have hf (r : Fin 50) (hr : r ≠ 38) : S₁.val r = st.val r := by simp [S₁,hr]
  have hc := preparedCoefficientEntry_do (A := A) (w := w) negative S₁
    ((hf 26 (by decide)).trans hsource)
    ((hf 18 (by decide)).trans hpi) ((hf 19 (by decide)).trans hP')
    ((hf 22 (by decide)).trans hneg) ((hf 34 (by decide)).trans hs)
    ((hf 35 (by decide)).trans ht) ((hf 36 (by decide)).trans hu)
    ((hf 37 (by decide)).trans hj) (by simp [S₁])
    ((hf 39 (by decide)).trans hq) ((hf 40 (by decide)).trans hpowP) hs0 hst hP hd hi (by dsimp [d]; split <;> omega)
  have hrun := hp.seq (K₂ := 620*P+251) (fun st₁ he => by subst st₁; exact hc)
  refine hrun.mono (fun st' h => ?_) (by omega)
  refine ⟨h.1,h.2.1.trans (hf 18 (by decide)),h.2.2.1.trans (hf 19 (by decide)),
    h.2.2.2.1.trans (hf 22 (by decide)),?_,h.2.2.2.2.2.1.trans (hf 48 (by decide)),
    h.2.2.2.2.2.2.1.trans (hf 49 (by decide)),
    h.2.2.2.2.2.2.2.trans (hf 26 (by decide))⟩
  intro r hrlo hrhi hr38
  exact (h.2.2.2.2.1 r hrlo hrhi).trans (hf r hr38)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
