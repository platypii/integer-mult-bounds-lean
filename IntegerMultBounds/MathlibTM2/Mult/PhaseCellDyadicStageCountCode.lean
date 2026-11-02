module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleSelector
public import IntegerMultBounds.MathlibTM2.Fast.TableNatSub

/-! A fixed table-machine Euclidean counting step. Registers 0/1 hold the
remaining exponents, 2 is zero, 3 the count, 4 temporary and 5 the loop guard. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def dyadicCountStepCode : TblCode 16 :=
  .seq (.ite 0 1 (tblBlock 16 [.copy 0 4,.sub 1 0 0] (.copy 4 1)) (.ins (.sub 0 1 0)))
    (.seq (.ins (.inc 3)) (tblNatMin 0 1 5))

def dyadicCountNext {A : ℕ} (a b c : ℕ) (st : TblSt 16 A) : TblSt 16 A :=
  let R := if a < b then Function.update (Function.update (Function.update st.val 4 a) 0 (b-a)) 1 a
    else Function.update st.val 0 (a-b)
  ⟨Function.update (Function.update R 3 (c+1)) 5
    (min (if a < b then b-a else a-b) (if a < b then a else b)),st.acc⟩

theorem dyadicCountNext_off {A a b c : ℕ} (st : TblSt 16 A) (k : Fin 16)
    (hk : k ∉ [(0 : Fin 16),1,3,4,5]) : (dyadicCountNext a b c st).val k = st.val k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  by_cases hab : a < b <;> simp [dyadicCountNext,hab,hk]

theorem dyadicCountStepCode_do {A W w a b c : ℕ} (st : TblSt 16 A)
    (ha : st.val 0 = a) (hb : st.val 1 = b) (hc : st.val 3 = c)
    (hapos : 0 < a) (hbpos : 0 < b) (hwide : c+a+b < 2^W) :
    TblDo A W w dyadicCountStepCode st (fun st' => st' = dyadicCountNext a b c st) 7 := by
  let R := if a < b then Function.update (Function.update (Function.update st.val 4 a) 0 (b-a)) 1 a
    else Function.update st.val 0 (a-b)
  let M : TblSt 16 A := ⟨R,st.acc⟩
  have hbranch : TblDo A W w
      (.ite 0 1 (tblBlock 16 [.copy 0 4,.sub 1 0 0] (.copy 4 1)) (.ins (.sub 0 1 0))) st
      (fun st' => st' = M) 4 := by
    by_cases hab : a < b
    · apply TblDo.iteT (by simpa [ha,hb] using hab)
      apply TblDo.block
      · simp [tblFitsList,TblIns.fits,TblIns.exact,ha,hb]
        omega
      · simp [tblExactList,TblIns.exact,M,R,hab,ha,hb]
    · have ht := TblDo.iteF (st := st) (A := A) (W := W) (w := w) (a := (0 : Fin 16)) (b := 1)
        (c := tblBlock 16 [.copy 0 4,.sub 1 0 0] (.copy 4 1))
        (by simpa [ha,hb] using hab)
        (TblDo.insX (.sub 0 1 0) (P := fun s => s = M) (by simp [TblIns.fits,ha,hb]; omega)
          (by simp [TblIns.exact,M,R,hab,ha,hb] :
            (.sub 0 1 0 : TblIns 16).exact A w st = M))
      exact ht.mono (fun _ h => h) (by omega)
  unfold dyadicCountStepCode
  apply hbranch.seq (K₂ := 3)
  intro st₁ he
  subst st₁
  let N : TblSt 16 A := ⟨Function.update R 3 (c+1),st.acc⟩
  have hinc : TblDo A W w (.ins (.inc 3)) M (fun st' => st' = N) 1 := by
    apply TblDo.insX
    · by_cases hab : a < b <;> simp [TblIns.fits,M,R,hab,hc] <;> omega
    · by_cases hab : a < b <;> simp [TblIns.exact,M,R,N,hab,hc]
  apply hinc.seq (K₂ := 2)
  intro st₂ he
  subst st₂
  exact (tblNatMin_do (W := W) (w := w) 0 1 5 N).mono (fun st' he => by
    rw [he]
    by_cases hab : a < b <;> simp [N,R,dyadicCountNext,hab,hb]) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
