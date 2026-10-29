module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskRowCode
public import IntegerMultBounds.MathlibTM2.Fast.TableForFrom

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def ribbonMaskCode (boundary : Bool) : TblCode 18 :=
  tblForFrom 16 17 (ribbonMaskRowCode boundary)

theorem ribbonMaskCode_do (boundary : Bool) {A V w s t band a b origin L : ℕ} (st : TblSt 18 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hindex : st.val 16 = origin) (hcount : st.val 17 = origin+L)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hfit : origin+L+s < 2^V) (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (ribbonMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range L).flatMap (fun j =>
        tblPairs A w (if haloMaskAt boundary s t band a b ((origin+j+s-band)%s) then 1 else 0)
          (if haloMaskAt boundary s t band a b ((origin+j+s-band)%s) then 1 else 0))).reverse++st.acc)
      (32*L+2) := by
  let F := fun j => tblPairs A w
    (if haloMaskAt boundary s t band a b ((origin+j+s-band)%s) then 1 else 0)
    (if haloMaskAt boundary s t band a b ((origin+j+s-band)%s) then 1 else 0)
  let Inv := fun j (st' : TblSt 18 A) =>
    (∀ r : Fin 18, r.val < 6 → r ≠ 3 → st'.val r = st.val r) ∧
      st'.acc = ((List.range j).flatMap F).reverse++st.acc
  have hc : TblDo A V w (ribbonMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range L).flatMap F).reverse++st.acc) (L*(29+3)+2) := by
    apply TblDo.forFrom origin L 29 hindex hcount (by omega) (by decide) Inv
    · exact ⟨by intros; rfl,by simp⟩
    · intro j hj st₁ ⟨hf,hacc⟩ hidx hcnt
      have hrow := ribbonMaskRowCode_do (A := A) (V := V) (w := w) boundary st₁
        ((hf 0 (by decide) (by decide)).trans hs)
        ((hf 1 (by decide) (by decide)).trans ht)
        ((hf 2 (by decide) (by decide)).trans hband)
        ((hf 4 (by decide) (by decide)).trans ha)
        ((hf 5 (by decide) (by decide)).trans hb) hidx
        hs0 hst haS hbS hbandS (by omega) hwide
      exact hrow.mono (fun st₂ ⟨hout,hlow,hhigh⟩ => ⟨
        (hhigh 16 (by decide)).trans hidx,(hhigh 17 (by decide)).trans hcnt,by
          constructor
          · intro r hr h3
            have h16 : r ≠ 16 := by intro he; subst r; norm_num at hr
            simpa [h16] using (hlow r hr h3).trans (hf r hr h3)
          · dsimp only
            rw [hout,hacc,List.range_succ]
            simp [F,List.reverse_append,List.append_assoc]⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  exact hc.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
