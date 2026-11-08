module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEnumeration

/-! Compute one regular halo window's two counts. Interior windows share the
same body/overlap values; only first, final and padded dummy windows differ. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountRow
open IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- B is the complete overlap width, twice the one-sided halo. -/
def values (L B N j : ℕ) : List ℕ :=
  if j < N then
    if j+1 < N then [if j = 0 then L else L-B,B]
    else [if j = 0 then L+B else L,0]
  else [0,0]

def emitTwo (a b : Fin 16) : TblCode 16 := tblBlock 16 [.emit a 12] (.emit b 12)

private theorem emitTwo_do {A W w x y : ℕ} (a b : Fin 16) (st : TblSt 16 A)
    (ha : st.val a = x) (hb : st.val b = y) (hz : st.val 12 = 0) :
    TblDo A W w (emitTwo a b) st (fun st' =>
      st'.acc = (tblPairs A w x 0++tblPairs A w y 0).reverse++st.acc ∧
      ∀ i, st'.val i = st.val i) 2 := by
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits]
  · constructor
    · simp [tblExactList,TblIns.exact,ha,hb,hz,List.reverse_append,List.append_assoc]
    · intro i; rfl

def choose : TblCode 16 :=
  .ite 8 0 (.ite 12 4 (emitTwo 5 2) (emitTwo 1 2))
    (.ite 12 4 (emitTwo 1 12) (emitTwo 6 12))

theorem choose_do {A W w L B N j : ℕ} (st : TblSt 16 A)
    (hN : st.val 0 = N) (hL : st.val 1 = L) (hB : st.val 2 = B)
    (hj : st.val 4 = j) (hbody : st.val 5 = L-B) (hsingle : st.val 6 = L+B)
    (hnext : st.val 8 = j+1) (hz : st.val 12 = 0) (hreal : j < N) :
    TblDo A W w choose st (fun st' =>
      st'.acc = ((values L B N j).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc ∧
      ∀ i, st'.val i = st.val i) 4 := by
  by_cases hlast : j+1 < N
  · apply TblDo.iteT (by simpa [hnext,hN] using hlast)
    by_cases hfirst : j = 0
    · apply TblDo.iteF (by simp [hz,hj,hfirst])
      exact (emitTwo_do 1 2 st hL hB hz).mono
        (fun st' ⟨ha,hf⟩ => ⟨by simpa only [values,ite_eq_left hreal,ite_eq_left hlast,ite_eq_left hfirst,List.flatMap_cons,List.flatMap_nil,List.append_nil] using ha,hf⟩) le_rfl
    · apply TblDo.iteT (by simp only [hz,hj]; omega)
      exact (emitTwo_do 5 2 st hbody hB hz).mono
        (fun st' ⟨ha,hf⟩ => ⟨by simpa only [values,ite_eq_left hreal,ite_eq_left hlast,ite_eq_right hfirst,List.flatMap_cons,List.flatMap_nil,List.append_nil] using ha,hf⟩) le_rfl
  · apply TblDo.iteF (by simpa [hnext,hN] using hlast)
    by_cases hfirst : j = 0
    · apply TblDo.iteF (by simp [hz,hj,hfirst])
      exact (emitTwo_do 6 12 st hsingle hz hz).mono
        (fun st' ⟨ha,hf⟩ => ⟨by simpa only [values,ite_eq_left hreal,ite_eq_right hlast,ite_eq_left hfirst,List.flatMap_cons,List.flatMap_nil,List.append_nil] using ha,hf⟩) le_rfl
    · apply TblDo.iteT (by simp only [hz,hj]; omega)
      exact (emitTwo_do 1 12 st hL hz hz).mono
        (fun st' ⟨ha,hf⟩ => ⟨by simpa only [values,ite_eq_left hreal,ite_eq_right hlast,ite_eq_right hfirst,List.flatMap_cons,List.flatMap_nil,List.append_nil] using ha,hf⟩) le_rfl

def row : TblCode 16 :=
  .ite 4 0 ((tblBlock 16 [.copy 4 8] (.inc 8)) ;; choose) (emitTwo 12 12)

theorem row_do {A W w L B N j : ℕ} (st : TblSt 16 A)
    (hN : st.val 0 = N) (hL : st.val 1 = L) (hB : st.val 2 = B)
    (hj : st.val 4 = j) (hbody : st.val 5 = L-B) (hsingle : st.val 6 = L+B)
    (hz : st.val 12 = 0) (hwide : N < 2^W) :
    TblDo A W w row st (fun st' =>
      st'.acc = ((values L B N j).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc ∧
      ∀ i, i ≠ 8 → st'.val i = st.val i) 7 := by
  by_cases hreal : j < N
  · apply TblDo.iteT (by simpa [hj,hN] using hreal)
    have hinit : TblDo A W w (tblBlock 16 [.copy 4 8] (.inc 8)) st
        (fun st' => st' = ⟨Function.update st.val 8 (j+1),st.acc⟩) 2 := by
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits,TblIns.exact,hj]
        omega
      · simp [tblExactList,TblIns.exact,hj]
    exact hinit.seq (K₂ := 4) (fun st₁ he => by
      subst st₁
      exact (choose_do _ (by simpa using hN) (by simpa using hL) (by simpa using hB)
        (by simpa using hj) (by simpa using hbody) (by simpa using hsingle) (by simp)
        (by simpa using hz) hreal).mono (fun st₂ ⟨ha,hf⟩ => ⟨ha,by
          intro i hi
          simpa [hi] using hf i⟩) le_rfl)
  · apply TblDo.iteF (by simpa [hj,hN] using hreal)
    exact (emitTwo_do 12 12 st hz hz hz).mono (fun st' ⟨ha,hf⟩ =>
      ⟨by simpa [values,hreal] using ha,by intro i _; exact hf i⟩) (by decide)

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountRow
