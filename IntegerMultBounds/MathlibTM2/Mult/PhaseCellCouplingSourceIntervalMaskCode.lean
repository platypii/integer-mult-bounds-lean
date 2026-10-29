module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskCode
public import IntegerMultBounds.MathlibTM2.Fast.TableForFrom

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingSourceIntervalMaskCode (boundary : Bool) : TblCode 17 :=
  tblForFrom 3 16 ((couplingSourceMaskRow boundary).rename Fin.castSucc)

theorem couplingSourceIntervalMaskCode_do (boundary : Bool) {A V w s t band a b origin N : ℕ}
    (st : TblSt 17 A) (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hindex : st.val 3 = origin)
    (hcount : st.val 16 = origin+N) (hfit : origin+N ≤ s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w (couplingSourceIntervalMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range N).flatMap (fun j =>
        tblPairs A w (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)
          (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0))).reverse ++ st.acc)
      (29*N+2) := by
  let F := fun j => tblPairs A w (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)
    (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)
  let Inv := fun j (st' : TblSt 17 A) =>
    (∀ r : Fin 17, r.val < 6 → r ≠ 3 → st'.val r = st.val r) ∧
    st'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hsV : s < 2^V := by nlinarith [Nat.zero_le (t*t)]
  have hc : TblDo A V w (couplingSourceIntervalMaskCode boundary) st (fun st' =>
      st'.acc = ((List.range N).flatMap F).reverse ++ st.acc) (N*(26+3)+2) := by
    apply TblDo.forFrom origin N 26 hindex hcount (by omega) (by decide) Inv
    · exact ⟨by intros; rfl,by simp⟩
    · intro j hj st₁ ⟨hf,hacc⟩ hidx hcnt
      have hrow := couplingSourceMaskRow_do boundary (A := A) (V := V) (w := w)
        (st₁.restrict Fin.castSucc)
        ((hf 0 (by decide) (by decide)).trans hs)
        ((hf 1 (by decide) (by decide)).trans ht)
        ((hf 2 (by decide) (by decide)).trans hband) hidx
        ((hf 4 (by decide) (by decide)).trans ha)
        ((hf 5 (by decide) (by decide)).trans hb)
        hs0 hst haS hbS hwide
      have hr := hrow.rename (f := Fin.castSucc) (Fin.castSucc_injective 16)
      exact hr.mono (fun st₂ ⟨⟨hrowacc,hframe⟩,hoff⟩ => ⟨
        (hframe 3 (by decide)).trans hidx,
        (hoff 16 (by intro k; exact Fin.ne_of_val_ne (by have hk := k.isLt; simp; omega))).trans hcnt,by
          constructor
          · intro r hlow h3
            let k : Fin 16 := ⟨r.val,by omega⟩
            have hk : Fin.castSucc k = r := Fin.ext rfl
            have he := hframe k (by dsimp [k]; omega)
            change st₂.val (Fin.castSucc k) = st₁.val (Fin.castSucc k) at he
            rw [hk] at he
            simpa [h3] using he.trans (hf r hlow h3)
          · dsimp only [TblSt.restrict] at hrowacc
            dsimp only
            rw [hrowacc,hacc,List.range_succ]
            simp [F,List.reverse_append,List.append_assoc]⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  exact hc.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
