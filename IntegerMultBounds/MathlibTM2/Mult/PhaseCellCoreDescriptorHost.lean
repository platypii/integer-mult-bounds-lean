module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreDescriptorCode
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! # Descriptor generation on the stack machine

The loop count is computed from the numeric s and width headers. A generic
injective register placement suffices; all outside stacks and the existing
output suffix are preserved by the standard table host interpreter.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellMatrix

def coreDescriptorInit : TblCode 16 :=
  tblBlock 16 [.add 0 1 8,.zero 12,.inc 12,.sub 8 12 8,.div 8 1 15] (.zero 12)

theorem coreDescriptorInit_do {A W w s width : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hwidth : 0 < width)
    (hwide : s+width < 2^W) :
    TblDo A W w coreDescriptorInit st (fun st' =>
      st'.val 0 = s ∧ st'.val 1 = width ∧ st'.val 12 = 0 ∧
      st'.val 15 = (s+width-1)/width ∧ st'.acc = st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),12,15] → st'.val i = st.val i) 6 := by
  have hW : W ≠ 0 := by intro he; subst W; simp at hwide; omega
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,hw,hW]
    omega
  · refine ⟨by simp [tblExactList,TblIns.exact,hs],by simp [tblExactList,TblIns.exact,hw],by simp [tblExactList,TblIns.exact],by simp [tblExactList,TblIns.exact,hs,hw],rfl,?_⟩
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [tblExactList,TblIns.exact,hi.1,hi.2.1,hi.2.2]

def generatedCoreDescriptorCode : TblCode 16 := coreDescriptorInit ;; coreDescriptorCode

theorem generatedCoreDescriptorCode_do {A W w s width : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hwidth : 0 < width)
    (hwide : s+width < 2^W) :
    TblDo A W w generatedCoreDescriptorCode st (fun st' =>
      st'.acc = ((coreIndices s width).flatMap (fun k =>
        tblPairs A w (coreStart width k) 0++tblPairs A w (coreLength s width k) 0)).reverse++st.acc)
      (11*((s+width-1)/width)+9) := by
  have hc : (s+width-1)/width < 2^W :=
    (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt hwide)
  have h := coreDescriptorInit_do (A := A) (W := W) (w := w) st hs hw hwidth hwide
  exact (h.seq (fun st₁ ⟨hs₁,hw₁,hz,hcount,hacc,_⟩ =>
    (coreDescriptorCode_do (A := A) (W := W) (w := w) st₁ hs₁ hw₁ hz hcount hwidth
      (by omega) hc).mono (fun st₂ he => by rw [he,hacc]) le_rfl)).mono
      (fun _ he => he) (by omega)

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem generatedCoreDescriptorHost_exec (rg : TblR 16 → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ r, rg r ≠ out) {W w s width : ℕ}
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (hnl : nl.length = w) (hwW : w ≤ W)
    (st : TblSt 16 A) (hs : st.val 0 = s) (hw : st.val 1 = width)
    (hwidth : 0 < width) (hwide : s+width < 2^W)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (11*((s+width-1)/width)+9)*tblC W w+4*((coreIndices s width).length*w)+2 ∧
      Exec body (tblHost rg generatedCoreDescriptorCode out) (mk v S) m (mk v' S') ∧
      S'.R out = (coreIndices s width).flatMap (fun k =>
        tblPairs A w (coreStart width k) 0++tblPairs A w (coreLength s width k) 0)++S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val,[]⟩) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v',S',m,st',he,hu,hm,hex,hout',hholds,hframe⟩ := tblHost_runs (body := body)
    hrg hout wl nl hwl hnl hwW (generatedCoreDescriptorCode_do st hs hw hwidth hwide)
    hbound v S hS
  have ha : st'.acc = ((coreIndices s width).flatMap (fun k =>
      tblPairs A w (coreStart width k) 0++tblPairs A w (coreLength s width k) 0)).reverse := by
    simpa only [hacc,List.append_nil] using he
  refine ⟨v',S',m,st',hu,?_,hex,?_,hholds,hframe⟩
  · have hlen : st'.acc.length = (coreIndices s width).length*(2*w) := by
      rw [ha]
      simp [List.length_flatMap,tblPairs,Nat.two_mul]
    rw [hlen] at hm
    nlinarith only [hm]
  · simpa only [ha,List.reverse_reverse] using hout'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
