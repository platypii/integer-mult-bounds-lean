module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExteriorMaskCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskCode

/-! Combine enlarged-interior and exterior zero-row guards in one geometry scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def recoveryGuardMaskAt (boundary : Bool) (s t B a b k : ℕ) : Bool :=
  (boundary && haloInteriorAt s t B a b k) || haloExteriorAt s (B/2) a b k

def recoveryGuardMembershipCode (boundary : Bool) : TblCode 16 :=
  if boundary then haloMembershipMaskCode false ;; (tblBlock 16 [.zero 6] (.inc 6) ;;
    .ite 15 6 exteriorMaskCode (.ins (.copy 15 15)))
  else exteriorMaskCode

theorem recoveryGuardMembershipCode_do (boundary : Bool) {A V w s t B a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hB : st.val 2 = B) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hks : k < s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*B+8 < 2^V) :
    TblDo A V w (recoveryGuardMembershipCode boundary) st (fun st' =>
      st'.val 15 = (if recoveryGuardMaskAt boundary s t B a b k then 1 else 0) ∧ st'.acc = st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 42 := by
  cases boundary with
  | false =>
    have hw : 2*s+2*B+8 < 2^V := by nlinarith [Nat.zero_le (t*t)]
    exact (exteriorMaskCode_do (A := A) (V := V) (w := w) st hs hB hk ha hb hks hbS hw).mono
      (fun st' h => by simpa [recoveryGuardMaskAt] using h) (by omega)
  | true =>
    have hV : V ≠ 0 := by intro h; subst V; norm_num at hwide <;> omega
    have hd := haloMembershipMaskCode_do (A := A) (V := V) (w := w) false st
      hs ht hB hk ha hb hs0 hst haS hbS hwide
    unfold recoveryGuardMembershipCode
    refine hd.seq (K₂ := 17) (fun st₁ ⟨hflag,hacc,hframe⟩ => ?_)
    let S₂ : TblSt 16 A := ⟨Function.update st₁.val 6 1,st₁.acc⟩
    have hp : TblDo A V w (tblBlock 16 [.zero 6] (.inc 6)) st₁ (fun st' => st' = S₂) 2 := by
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits,TblIns.exact,hV]
      · simp [tblExactList,TblIns.exact,S₂]
    refine hp.seq (K₂ := 15) (fun st₂ he => ?_)
    subst st₂
    have hlow (r : Fin 16) (hr : r.val < 6) : S₂.val r = st.val r := by
      have hn : r ≠ 6 := by intro h; subst r; norm_num at hr
      simpa [S₂,hn] using hframe r hr
    have hflag₂ : S₂.val 15 = if haloInteriorAt s t B a b k then 1 else 0 := by
      simpa [S₂,haloMaskAt] using hflag
    cases hdeep : haloInteriorAt s t B a b k with
    | false =>
      apply TblDo.iteT (by simp [S₂,hflag,haloMaskAt,hdeep])
      have hw : 2*s+2*B+8 < 2^V := by nlinarith [Nat.zero_le (t*t)]
      have he := exteriorMaskCode_do (A := A) (V := V) (w := w) S₂
        ((hlow 0 (by decide)).trans hs) ((hlow 2 (by decide)).trans hB)
        ((hlow 3 (by decide)).trans hk) ((hlow 4 (by decide)).trans ha)
        ((hlow 5 (by decide)).trans hb) hks hbS hw
      exact he.mono (fun st₃ h => ⟨by simpa [recoveryGuardMaskAt,hdeep] using h.1,
        h.2.1.trans hacc,fun r hr => (h.2.2 r hr).trans (hlow r hr)⟩) le_rfl
    | true =>
      have hc : TblDo A V w (.ins (.copy 15 15)) S₂ (fun st' =>
          st'.val 15 = (if recoveryGuardMaskAt true s t B a b k then 1 else 0) ∧ st'.acc = st.acc ∧
          ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 1 := by
        apply TblDo.insX (.copy 15 15) (by simp [TblIns.fits])
        refine ⟨by simp [TblIns.exact,hflag₂,recoveryGuardMaskAt,hdeep],hacc,?_⟩
        intro r hr
        have hn : r ≠ 15 := by intro h; subst r; norm_num at hr
        simpa [TblIns.exact,hn] using hlow r hr
      exact (TblDo.iteF (by simp [S₂,hflag,haloMaskAt,hdeep]) hc).mono (fun _ h => h) (by omega)
  
def recoveryGuardMaskRow (boundary : Bool) : TblCode 16 := recoveryGuardMembershipCode boundary ;; .ins (.emit 15 15)

theorem recoveryGuardMaskRow_do (boundary : Bool) {A V w s t band a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hks : k < s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (recoveryGuardMaskRow boundary) st (fun st' =>
      st'.acc = (tblPairs A w (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)
        (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)).reverse ++ st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 43 := by
  have hm := recoveryGuardMembershipCode_do boundary (A := A) (V := V) (w := w) st
    hs ht hband hk ha hb hks hs0 hst haS hbS hwide
  unfold recoveryGuardMaskRow
  refine hm.seq (K₂ := 1) (fun st' ⟨hflag,hacc,hframe⟩ => ?_)
  apply TblDo.ins (.emit 15 15)
  refine ⟨?_,hframe⟩
  simp [TblIns.run,hflag,hacc]

def recoveryGuardMaskCode (boundary : Bool) : TblCode 16 := tblFor 3 0 (recoveryGuardMaskRow boundary)

theorem recoveryGuardMaskCode_do (boundary : Bool) {A V w s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (recoveryGuardMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range s).flatMap (fun k =>
        tblPairs A w (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)
          (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0))).reverse ++ st.acc)
      (46*s+3) := by
  let F := fun k => tblPairs A w (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)
    (if recoveryGuardMaskAt boundary s t band a b k then 1 else 0)
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ r : Fin 16, r.val < 6 → r ≠ 3 → st'.val r = st.val r) ∧
    st'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hsV : s < 2^V := by nlinarith [hst, Nat.zero_le (t*t)]
  have hc : TblDo A V w (recoveryGuardMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range s).flatMap F).reverse ++ st.acc) (1+(s*(43+1+2)+2)) := by
    apply TblDo.for s 43 hs hsV (by decide) Inv
    · constructor
      · intro r hr h3
        simp [h3]
      · simp
    · intro k hk st₁ ⟨hf,hacc⟩ hindex hcount
      have hrow := recoveryGuardMaskRow_do boundary (A := A) (V := V) (w := w) st₁
        ((hf 0 (by decide) (by decide)).trans hs)
        ((hf 1 (by decide) (by decide)).trans ht)
        ((hf 2 (by decide) (by decide)).trans hband) hindex
        ((hf 4 (by decide) (by decide)).trans ha)
        ((hf 5 (by decide) (by decide)).trans hb)
        hk hs0 hst haS hbS hwide
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
