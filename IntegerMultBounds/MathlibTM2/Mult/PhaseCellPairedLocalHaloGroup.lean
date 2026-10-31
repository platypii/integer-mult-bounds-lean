module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedHaloGroupRow
public import IntegerMultBounds.MathlibTM2.Fast.TableForFrom
public import IntegerMultBounds.NLogN.PhaseCellHaloPhaseRange

/-! Run the unchanged halo row program only over phases touching this halo. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def pairedLocalHaloGroupCode : TblCode 16 := tblForFrom 4 15 pairedHaloGroupRowCode

theorem pairedLocalHaloGroupCode_do {A W w s t band a b L : ℕ} [NeZero s] (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (hindex : st.val 4 = haloPhaseStart s t a) (hcount : st.val 15 = naturalPhase s t b+1)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (hab : a ≤ b) (hbS : b ≤ s)
    (hst : s < t) (hL : 0 < L) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w pairedLocalHaloGroupCode st (fun st' =>
      st'.acc = ((haloLengthGroup s t band a b L).flatMap
        (fun phase => tblPairs A w (haloStart s t band a phase) (haloStart s t band a phase-a))).reverse ++ st.acc)
      (37*haloPhaseCount s t a b+2) := by
  let start := haloPhaseStart s t a
  let count := haloPhaseCount s t a b
  let F := fun j => if haloLength s t band a b (start+j) = L then
    tblPairs A w (haloStart s t band a (start+j)) (haloStart s t band a (start+j)-a) else []
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ k, k ∉ [(4 : Fin 16),8,9,10,11] → st'.val k = st.val k) ∧
    st'.acc = ((List.range j).flatMap F).reverse++st.acc
  have hend := haloPhaseRange_end (t := t) (NeZero.pos s) a b hab hbS
  have hN : t-s+1 < 2^W := by have hd := Nat.sub_le t s; nlinarith only [hwide,hd]
  have hcount' : st.val 15 = start+count := hcount.trans hend.1.symm
  have hNW : start+count < 2^W := by omega
  have hc : TblDo A W w pairedLocalHaloGroupCode st
      (fun st' => st'.acc = ((List.range count).flatMap F).reverse++st.acc) (count*(34+3)+2) := by
    apply TblDo.forFrom start count 34 hindex hcount' hNW (by decide) Inv
    · exact ⟨by intros; rfl,by simp⟩
    · intro j hj st₁ ⟨hf,hacc⟩ hidx hcnt
      have hr := pairedHaloGroupRowCode_do (A := A) (W := W) (w := w) st₁
        ((hf 0 (by simp)).trans hs') ((hf 2 (by simp)).trans hband) ((hf 3 (by simp)).trans hL') hidx
        ((hf 6 (by simp)).trans hden) ((hf 7 (by simp)).trans hone)
        ((hf 13 (by simp)).trans ha) ((hf 14 (by simp)).trans hb) (by omega) hbS (NeZero.pos s) hst (by omega) hwide
      exact hr.mono (fun st₂ ⟨hout,hframe⟩ => ⟨(hframe 4 (by simp)).trans hidx,
        (hframe 15 (by simp)).trans hcnt,by
          constructor
          · intro k hk
            have h4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
            have hrest : k ∉ [(8 : Fin 16),9,10,11] := fun hm => hk (List.mem_cons_of_mem _ hm)
            simpa [h4] using (hframe k hrest).trans (hf k hk)
          · rw [hout,hacc,List.range_succ]
            simp [F,List.reverse_append,List.append_assoc]⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  have hemits : (List.range count).flatMap F = (haloLengthGroup s t band a b L).flatMap
      (fun phase => tblPairs A w (haloStart s t band a phase) (haloStart s t band a phase-a)) := by
    have hfilter (xs : List ℕ) : xs.flatMap (fun phase => if haloLength s t band a b phase = L then
        tblPairs A w (haloStart s t band a phase) (haloStart s t band a phase-a) else []) =
        (xs.filter (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L))).flatMap
          (fun phase => tblPairs A w (haloStart s t band a phase) (haloStart s t band a phase-a)) := by
      induction xs with
      | nil => rfl
      | cons phase xs ih =>
        by_cases hh : haloLength s t band a b phase = L <;> simp [hh,hL,ih]
    have hh := hfilter ((List.range count).map (start+·))
    rw [haloLengthGroup_local hst band a b L hab hbS] at hh
    simpa only [F,List.flatMap_map,Function.comp_def] using hh
  exact hc.mono (fun st' hh => by simpa only [hemits] using hh) (by dsimp only [count]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
