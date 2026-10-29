module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonCoordinateCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskCode

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def ribbonMaskSmallReg (i : Fin 16) : Fin 18 := ⟨i.val,by omega⟩

theorem ribbonMaskSmallReg_injective : Function.Injective ribbonMaskSmallReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 18 => k.val) he
  exact Fin.ext hv

def ribbonMaskRowCode (boundary : Bool) : TblCode 18 :=
  ribbonCoordinateCode ;; (couplingSourceMaskRow boundary).rename ribbonMaskSmallReg

theorem ribbonMaskRowCode_do (boundary : Bool) {A V w s t band a b k : ℕ} (st : TblSt 18 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hk : st.val 16 = k)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hfit : k+s < 2^V) (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (ribbonMaskRowCode boundary) st (fun st' =>
      st'.acc = (tblPairs A w (if haloMaskAt boundary s t band a b ((k+s-band)%s) then 1 else 0)
        (if haloMaskAt boundary s t band a b ((k+s-band)%s) then 1 else 0)).reverse++st.acc ∧
      (∀ r : Fin 18, r.val < 6 → r ≠ 3 → st'.val r = st.val r) ∧
      (∀ r : Fin 18, 16 ≤ r.val → st'.val r = st.val r)) 29 := by
  have hc := ribbonCoordinateCode_do (A := A) (V := V) (w := w) st hs hband hk hs0 hbandS hfit
  apply hc.seq (K₂ := 26)
  intro st₁ ⟨hquery,hacc,hframe⟩
  have hf (r : Fin 18) (hr : r ≠ 3) := hframe r hr
  have hm := couplingSourceMaskRow_do (A := A) (V := V) (w := w) boundary
    (st₁.restrict ribbonMaskSmallReg)
    ((hf 0 (by decide)).trans hs) ((hf 1 (by decide)).trans ht)
    ((hf 2 (by decide)).trans hband) hquery
    ((hf 4 (by decide)).trans ha) ((hf 5 (by decide)).trans hb)
    hs0 hst haS hbS hwide
  exact (hm.rename (f := ribbonMaskSmallReg) ribbonMaskSmallReg_injective).mono (fun st₂ ⟨⟨hout,hlow⟩,hoff⟩ => by
    dsimp only [TblSt.restrict] at hout
    refine ⟨hout.trans (by rw [hacc]),?_,?_⟩
    · intro r hr h3
      let i : Fin 16 := ⟨r.val,by omega⟩
      have hi : ribbonMaskSmallReg i = r := Fin.ext rfl
      have he := hlow i (by dsimp [i]; omega)
      change st₂.val (ribbonMaskSmallReg i) = st₁.val (ribbonMaskSmallReg i) at he
      rw [hi] at he
      exact he.trans (hf r h3)
    · intro r hr
      have h3 : r ≠ 3 := by intro he; subst r; norm_num at hr
      have hsep : ∀ i, ribbonMaskSmallReg i ≠ r := by
        intro i he
        have hi := i.isLt
        have hv := congrArg (fun j : Fin 18 => j.val) he
        change i.val = r.val at hv
        omega
      exact (hoff r hsep).trans (hf r h3)) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
