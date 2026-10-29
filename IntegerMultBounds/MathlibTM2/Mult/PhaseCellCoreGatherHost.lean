module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherCode

/-! # Host execution of generated group origins

The host computes the group's origins from numeric geometry fields and emits
them in order, retaining the existing output suffix and all outside stacks.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem generatedCoreGatherHost_exec (rg : TblR 16 → Fin T) (hrg : Function.Injective rg)
    (out : Fin T) (hout : ∀ r, rg r ≠ out) {W w s width radius L : ℕ}
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (hnl : nl.length = w) (hwW : w ≤ W)
    (st : TblSt 16 A) (hs : st.val 0 = s) (hw : st.val 1 = width)
    (hr : st.val 2 = radius) (hL : st.val 3 = L)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^W)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (18*((s+width-1)/width)+9)*tblC W w+2*((coreGatherIndices s width radius L).length*w)+2 ∧
      Exec body (tblHost rg generatedCoreGatherCode out) (mk v S) m (mk v' S') ∧
      S'.R out = (coreGatherIndices s width radius L).flatMap (fun k =>
        tblPairs A w (coreStart width k-radius) 0)++S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val,[]⟩) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v',S',m,st',he,hu,hm,hex,hout',hholds,hframe⟩ := tblHost_runs (body := body)
    hrg hout wl nl hwl hnl hwW (generatedCoreGatherCode_do st hs hw hr hL hwidth hwide)
    hbound v S hS
  have ha : st'.acc = ((coreGatherIndices s width radius L).flatMap (fun k =>
      tblPairs A w (coreStart width k-radius) 0)).reverse := by
    simpa only [hacc,List.append_nil] using he
  refine ⟨v',S',m,st',hu,?_,hex,?_,hholds,hframe⟩
  · have hlen : st'.acc.length = (coreGatherIndices s width radius L).length*w := by
      rw [ha]
      simp [List.length_flatMap,tblPairs]
    rw [hlen] at hm
    nlinarith only [hm]
  · simpa only [ha,List.reverse_reverse] using hout'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
