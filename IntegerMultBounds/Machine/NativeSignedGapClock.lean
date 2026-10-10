import IntegerMultBounds.Machine.NativeSignedGapScan
import IntegerMultBounds.Machine.NativeReturnOneTape

/-! Physical erasure of the reusable gap clock and its preparation sentinel. -/
namespace IntegerMultBounds.Machine.NativeSignedGapClock
open RadixDigits

def program : Program 1 4 2 := seq (seq MarkedWordCleanup.clearProgram
  (Rewind.program (separator:Fin 6))) MarkedWordCleanup.unmarkProgram

theorem clock_eq (d : ℕ) : NativeSignedGapScan.clock d=
    MarkedWordCleanup.marked (List.replicate d (digitSymbol (0:Fin 2))) := rfl

theorem fill_clock_eq (d : ℕ) : RadixZeroFill.radixZeros (by decide : 2≤2) d=
    NativeSignedGapScan.clock d := rfl

theorem empty_eq : RadixZeroFill.radixEmpty (q:=2)=NativeSignedGapScan.clock 0 := rfl

theorem runs (d : ℕ) : HoareTime program
    (fun v => v=MarkedWordCleanup.one (NativeSignedGapScan.clock d) 1)
    (fun v => v=MarkedWordCleanup.one (fun _ => blank) 0) (2*d+5) := by
  have hc := MarkedWordCleanup.clear_hoare (List.replicate d (digitSymbol (0:Fin 2))) (by
    intro x hx; simp only [List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    decide)
  simp only [List.length_replicate] at hc
  have hr := Rewind.rewind_hoare (separator:Fin 6) (MarkedWordCleanup.empty (a:=2)) (d+1) (d+1)
    (by intro j hj; simp [MarkedWordCleanup.empty,show (d:ℤ)+1-j≠0 by omega,blank,separator])
    (by simp [MarkedWordCleanup.empty])
  have hrr : HoareTime (Rewind.program (separator:Fin 6))
      (fun v => v=MarkedWordCleanup.one (MarkedWordCleanup.empty (a:=2)) (1+d))
      (fun v => v=MarkedWordCleanup.one (MarkedWordCleanup.empty (a:=2)) 0) (d+1) := by
    simpa only [Rewind.cfg,Config.tapes,MarkedWordCleanup.one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr
  have hu := MarkedWordCleanup.unmark_hoare ([]:List (Fin 6))
  have hh := (hc.seq hrr).seq hu
  simpa only [program,List.length_replicate,clock_eq,MarkedWordCleanup.marked,putWord,
    MarkedWordCleanup.word] using hh.consequence (fun _ h => h) (fun _ h => h)
      (show d+1+(d+1)+1+1≤2*d+5 by omega)

end IntegerMultBounds.Machine.NativeSignedGapClock
