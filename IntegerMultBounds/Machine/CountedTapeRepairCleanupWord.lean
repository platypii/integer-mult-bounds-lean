import IntegerMultBounds.Machine.CountedTapeRepairRun

/-! Physical removal of complete marked and unmarked stage words, including
left sentinels, with literal return to the blank origin. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairCleanupWord
noncomputable section
open SharedPlacementAlphabet

def one (f : ℤ → Fin 5) (p : ℤ) : Tapes 1 1 := ⟨fun _ => p,fun _ => f⟩
def marked (xs : List (Fin 5)) := putWord (PartitionMarked.markedTape 0 []) 0 xs

theorem marked_full (xs : List (Fin 5)) :
    putWord (fun _ => blank) (-1) (PartitionMarked.marker::xs)=marked xs := by
  rw [putWord_cons]
  change putWord (Function.update (fun _ => blank) (-1) PartitionMarked.marker) 0 xs=_
  have h : Function.update (fun _ : ℤ => (blank : Fin 5)) (-1) PartitionMarked.marker=PartitionMarked.markedTape 0 [] := by
    funext z
    by_cases hz : z = -1 <;> simp [PartitionMarked.markedTape,putWord,hz,PartitionMarked.encoding,Alphabet.widen]
    rfl
  rw [h]
  rfl

def markedEndProgram := seq (EraseBack.program (a := 1)) StepRight.program
def markedScanProgram := seq (ScanEnd.program (a := 1)) markedEndProgram

theorem marked_end (xs : List (Fin 5)) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime markedEndProgram (fun v => v=one (marked xs) xs.length)
      (fun v => v=one (fun _ => blank) 0) (xs.length+5) := by
  have h := EraseBack.erase_hoare (a := 1) (fun _ => blank) (-1) (PartitionMarked.marker::xs)
    (by intro x hx'; rcases List.mem_cons.mp hx' with rfl | hx' <;> first | decide | exact hx x hx') rfl (by intro _ _; rfl)
  rw [marked_full] at h
  simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at h
  have hp : (-1 : ℤ)+(xs.length+1)=xs.length := by omega
  rw [hp] at h
  have h2 := StepRight.step_hoare (a := 1) (fun _ => blank) (-1)
  exact (h.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem marked_scan (xs : List (Fin 5))
    (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime markedScanProgram (fun v => v=one (marked xs) 0)
      (fun v => v=one (fun _ => blank) 0) (2*xs.length+6) := by
  have h1 := ScanEnd.scan_hoare (a := 1) (PartitionMarked.markedTape 0 []) 0 xs hx (by
    exact RepairStage.markedTape_nil xs.length (by omega))
  simp only [zero_add] at h1
  exact (h1.seq (marked_end xs hx)).consequence (fun _ h => h) (fun _ h => h) (by omega)

def plainEndProgram := EraseBack.program (a := 1)
def plainBackProgram := ReturnOrigin.program (a := 1)

theorem plain_end (xs : List (Fin 5)) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime plainEndProgram (fun v => v=one (putWord (fun _ => blank) 0 xs) xs.length)
      (fun v => v=one (fun _ => blank) 0) (xs.length+2) := by
  have h := EraseBack.erase_hoare (a := 1) (fun _ => blank) 0 xs hx rfl (by intro _ _; rfl)
  simpa only [plainEndProgram,zero_add,one,EraseBack.cfg,Config.tapes] using h

theorem plain_back (xs : List (Fin 5)) (hx : ∀ x ∈ xs,x≠blank) :
    HoareTime plainBackProgram (fun v => v=one (putWord (fun _ => blank) 0 xs) xs.length)
      (fun v => v=one (putWord (fun _ => blank) 0 xs) 0) (xs.length+2) :=
  ReturnOrigin.return_hoare xs hx

def counterProgram := seq (ScanEnd.program (a := 1)) (EraseBack.program (a := 1))

theorem counter_full (cs : List Bool) :
    putWord (fun _ => blank) 0 (separator::cs.map bitSymbol)=RepairScan.ctrTape cs := by
  rw [putWord_cons,IntegerMultBounds.Compact.PowerTwo.ctrTape_eq]
  congr 1
  funext z
  by_cases hz : z=0 <;>
    simp [IntegerMultBounds.Compact.PowerTwo.ctrBg,GrowingCounter.emptyTape,
      PartitionMarked.encoding,Alphabet.widen,hz]
  all_goals rfl

theorem counter_runs (cs : List Bool) :
    HoareTime counterProgram (fun v => v=one (RepairScan.ctrTape cs) 1)
      (fun v => v=one (fun _ => blank) 0) (2*cs.length+4) := by
  have h1 := ScanEnd.scan_hoare (a := 1) IntegerMultBounds.Compact.PowerTwo.ctrBg 1
    (cs.map bitSymbol) (ReturnOrigin.bits_nonblank cs) (by
      unfold IntegerMultBounds.Compact.PowerTwo.ctrBg GrowingCounter.emptyTape
      simp only [show (1 : ℤ)+(cs.map bitSymbol).length ≠0 by simp; omega,ite_false]
      rfl)
  rw [← IntegerMultBounds.Compact.PowerTwo.ctrTape_eq] at h1
  have h2 := EraseBack.erase_hoare (a := 1) (fun _ => blank) 0 (separator::cs.map bitSymbol)
    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx <;> first | decide | exact ReturnOrigin.bits_nonblank cs x hx)
    rfl (by intro _ _; rfl)
  rw [counter_full] at h2
  simp only [List.length_cons,List.length_map,Nat.cast_add,Nat.cast_one,zero_add,add_comm] at h1 h2
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedTapeRepairCleanupWord
