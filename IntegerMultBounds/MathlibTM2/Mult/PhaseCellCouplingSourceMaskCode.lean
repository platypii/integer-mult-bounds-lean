module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMembershipMask
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Generate either halo selection mask in ambient coordinate order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem publicationMaskSymbol (A : ℕ) (flag : Bool) :
    tblPairs A 1 (if flag then 1 else 0) (if flag then 1 else 0) =
      [IntegerMultBounds.MathlibTM2.Layer.pairSym A flag flag] := by
  cases flag <;> norm_num [tblPairs,IntegerMultBounds.MathlibTM2.Layer.coeffSyms,List.ofFn_succ,ZMod.val_one_eq_one_mod]

def couplingSourceMaskRow (boundary : Bool) : TblCode 16 := haloMembershipMaskCode boundary ;; .ins (.emit 15 15)

theorem couplingSourceMaskRow_do (boundary : Bool) {A V w s t band a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (couplingSourceMaskRow boundary) st (fun st' =>
      st'.acc = (tblPairs A w (if haloMaskAt boundary s t band a b k then 1 else 0)
        (if haloMaskAt boundary s t band a b k then 1 else 0)).reverse ++ st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 26 := by
  have hm := haloMembershipMaskCode_do (A := A) (V := V) (w := w) boundary st
    hs ht hband hk ha hb hs0 hst haS hbS hbandS hwide
  unfold couplingSourceMaskRow
  refine hm.seq (K₂ := 1) (fun st' ⟨hflag,hacc,hframe⟩ => ?_)
  apply TblDo.ins (.emit 15 15)
  refine ⟨?_,hframe⟩
  simp [TblIns.run,hflag,hacc]

def couplingSourceMaskCode (boundary : Bool) : TblCode 16 := tblFor 3 0 (couplingSourceMaskRow boundary)

theorem couplingSourceMaskCode_do (boundary : Bool) {A V w s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (couplingSourceMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range s).flatMap (fun k =>
        tblPairs A w (if haloMaskAt boundary s t band a b k then 1 else 0)
          (if haloMaskAt boundary s t band a b k then 1 else 0))).reverse ++ st.acc)
      (29*s+3) := by
  let F := fun k => tblPairs A w (if haloMaskAt boundary s t band a b k then 1 else 0)
    (if haloMaskAt boundary s t band a b k then 1 else 0)
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ r : Fin 16, r.val < 6 → r ≠ 3 → st'.val r = st.val r) ∧
    st'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hsV : s < 2^V := by nlinarith [hst, Nat.zero_le (t*t)]
  have hc : TblDo A V w (couplingSourceMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range s).flatMap F).reverse ++ st.acc) (1+(s*(26+1+2)+2)) := by
    apply TblDo.for s 26 hs hsV (by decide) Inv
    · constructor
      · intro r hr h3
        simp [h3]
      · simp
    · intro k hk st₁ ⟨hf,hacc⟩ hindex hcount
      have hrow := couplingSourceMaskRow_do boundary (A := A) (V := V) (w := w) st₁
        ((hf 0 (by decide) (by decide)).trans hs)
        ((hf 1 (by decide) (by decide)).trans ht)
        ((hf 2 (by decide) (by decide)).trans hband) hindex
        ((hf 4 (by decide) (by decide)).trans ha)
        ((hf 5 (by decide) (by decide)).trans hb)
        hs0 hst haS hbS hbandS hwide
      exact hrow.mono (fun st₂ ⟨hrowacc,hframe⟩ =>
        ⟨(hframe 3 (by decide)).trans hindex,(hframe 0 (by decide)).trans hcount,by
          constructor
          · intro r hr h3
            simpa [h3] using (hframe r hr).trans (hf r hr h3)
          · rw [hrowacc,hacc,List.range_succ]
            simp [F,List.reverse_append,List.append_assoc]⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  exact hc.mono (fun st' hh => hh) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
