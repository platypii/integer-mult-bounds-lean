module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicStageCountLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleRowsCode

/-! A fixed schedule generator: compute the count, save the packet seed,
enumerate the rows, and restore the retained seed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def generatedDyadicScheduleCode : TblCode 16 :=
  .seq generatedDyadicCountCode
    (.seq (.ins (.copy 9 4)) (.seq dyadicScheduleRowsCode (.ins (.copy 4 9))))

theorem generatedDyadicScheduleCode_do {A W w a b C : ℕ} (st : TblSt 16 A)
    (ha : st.val 6 = a) (hb : st.val 7 = b) (hC : st.val 9 = C)
    (hbits : a+b < W) (hfit : C*2^(a+b) < 2^W) :
    TblDo A W w generatedDyadicScheduleCode st (fun F =>
      F.val 3 = dyadicStageCount (a+b) a b ∧
      F.acc = ((dyadicScheduleValues (a+b) a b C).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc ∧
      F.val 6 = a ∧ F.val 7 = b ∧ F.val 9 = C)
      (dyadicStageCount (a+b) a b*((a+b)*(4*(a+b)+19)+27)+13) := by
  let N := dyadicStageCount (a+b) a b
  let K := N*((a+b)*(4*(a+b)+19)+18)+3
  have hcount := generatedDyadicCountCode_do (W := W) (w := w) st ha hb
    (hbits.trans Nat.lt_two_pow_self)
  unfold generatedDyadicScheduleCode
  apply (hcount.seq (K₂ := 1+(K+1)) ?_).mono (fun _ h => h) (by dsimp [K,N]; apply le_of_eq; ring)
  intro s ⟨hn,h5,h2,hacc,hframe⟩
  have haS := (hframe 6 (by decide)).trans ha
  have hbS := (hframe 7 (by decide)).trans hb
  have hCS := (hframe 9 (by decide)).trans hC
  have hsave : TblDo A W w (.ins (.copy 9 4)) s
      (fun t => t = ⟨Function.update s.val 4 C,s.acc⟩) 1 := by
    apply TblDo.ins
    simp [TblIns.run,hCS]
  apply hsave.seq
  intro t ht
  subst t
  have hrows := dyadicScheduleRowsCode_do (W := W) (w := w)
    (⟨Function.update s.val 4 C,s.acc⟩ : TblSt 16 A)
    (by simpa using haS) (by simpa using hbS) (by simp) (by simpa using hn) hbits hfit
  apply hrows.seq
  intro u ⟨hN,hindex,hout,hkeep⟩
  have haU : u.val 6 = a := by simpa using (hkeep 6 (by decide) (by decide)).trans haS
  have hbU : u.val 7 = b := by simpa using (hkeep 7 (by decide) (by decide)).trans hbS
  have hCU : u.val 4 = C := by simpa using hkeep 4 (by decide) (by decide)
  apply TblDo.ins
  simp [TblIns.run,hN,hout,hacc,haU,hbU,hCU]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
