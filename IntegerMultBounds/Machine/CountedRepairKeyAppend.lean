import IntegerMultBounds.Machine.CountedRepairKeyAppendMoves

/-! Conditional key writing by actual scans, followed by physical head returns. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyAppend
noncomputable section
open CountedRepairKeyAppendMoves
open CountedGuardGadgetRecord (word)
open SharedPlacementAlphabet

theorem set_bank0 (F K V W G : ℤ → Fin 5) (pf pk pv pw pg : ℤ) :
    setTape (bank F K V W pf pk pv pw) 0 G pg = bank G K V W pg pk pv pw := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem set_bank1 (F K V W G : ℤ → Fin 5) (pf pk pv pw pg : ℤ) :
    setTape (bank F K V W pf pk pv pw) 1 G pg = bank F G V W pf pg pv pw := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem set_bank2 (F K V W G : ℤ → Fin 5) (pf pk pv pw pg : ℤ) :
    setTape (bank F K V W pf pk pv pw) 2 G pg = bank F K G W pf pk pg pw := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem set_bank3 (F K V W G : ℤ → Fin 5) (pf pk pv pw pg : ℤ) :
    setTape (bank F K V W pf pk pv pw) 3 G pg = bank F K V G pf pk pv pg := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def input (fl : Bool) (V W : List Bool) := bank (word [fl]) (FlagCopy.keyTape []) (word V) (word W) 1 0 0 0
def ready (fl : Bool) (V W : List Bool) := bank (word [fl]) (FlagCopy.keyTape [bitSymbol fl]) (word V) (word W) 0 1 0 0
def output (fl : Bool) (V W : List Bool) := bank (word [fl])
  (FlagCopy.keyTape (FlagCopy.keyWord fl (V++W))) (word V) (word W) 0 0 0 0

def setup := seq (seq (leftAt 0) copyFlag) (leftAt 0)
def yes := seq (seq (seq (seq copyV copyW) keyBack) (backAt 2)) (backAt 3)
def no := keyBack
def test (s : Fin 4 → Fin 5) : Bool := decide (s 0=bitSymbol true)
def conditional := branch test yes no
def program := seq setup conditional

theorem setup_runs (fl : Bool) (V W : List Bool) :
    HoareTime setup (fun v => v=input fl V W) (fun v => v=ready fl V W) 5 := by
  have h1 := left_runs (input fl V W) 0
  have h2 := copyFlag_runs (FlagCopy.keyTape []) (word V) (word W) 0 0 0 fl
  have h3 := left_runs (bank (word [fl]) (FlagCopy.keyTape [bitSymbol fl]) (word V) (word W) 1 1 0 0) 0
  simp only [input,set_bank0] at h1
  change HoareTime copyFlag _ (fun v => v=bank (word [fl]) (FlagCopy.keyTape [bitSymbol fl]) (word V) (word W) 1 1 0 0) 1 at h2
  simp only [set_bank0] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem yes_runs (fl : Bool) (V W : List Bool) :
    HoareTime yes (fun v => v=ready fl V W)
      (fun v => v=bank (word [fl]) (FlagCopy.keyTape (bitSymbol fl :: (V++W).map bitSymbol)) (word V) (word W) 0 0 0 0)
      (3*(V.length+W.length)+11) := by
  let K := FlagCopy.keyTape (bitSymbol fl :: (V++W).map bitSymbol)
  have h1 := copyV_runs (word [fl]) (FlagCopy.keyTape [bitSymbol fl]) (word W) 0 1 0 V
  rw [KeyRoutine.keyTape_append1] at h1
  have h2 := copyW_runs (word [fl]) (FlagCopy.keyTape (bitSymbol fl :: V.map bitSymbol)) (word V) 0 (1+V.length) V.length W
  have hk : putWord (FlagCopy.keyTape (bitSymbol fl :: V.map bitSymbol)) (1+V.length) (W.map bitSymbol)=K := by
    have h := putWord_append_forward (PartitionMarked.markedTape 0 []) 0 (bitSymbol (a := 1) fl :: V.map bitSymbol) (W.map bitSymbol)
    simpa [K,FlagCopy.keyTape,List.map_append,add_comm] using h
  rw [hk] at h2
  let A := bank (word [fl]) K (word V) (word W) 0 (1+V.length+W.length) V.length W.length
  have h3 := keyBack_runs A (bitSymbol fl :: (V++W).map bitSymbol) rfl
    (by change (1+(V.length : ℤ)+W.length)=_; simp only [List.length_cons,List.length_map,List.length_append]; push_cast; omega) (KeyRoutine.keyWord_interior fl (V++W))
  have h4 := back_runs (bank (word [fl]) K (word V) (word W) 0 0 V.length W.length) 2 V rfl rfl
  have h5 := back_runs (bank (word [fl]) K (word V) (word W) 0 0 0 W.length) 3 W rfl rfl
  simp only [A,set_bank1] at h3
  simp only [set_bank2] at h4
  simp only [set_bank3] at h5
  have hh := (((h1.seq h2).seq h3).seq h4).seq h5
  simp only [List.length_cons,List.length_map,List.length_append] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem no_runs (fl : Bool) (V W : List Bool) :
    HoareTime no (fun v => v=ready fl V W)
      (fun v => v=bank (word [fl]) (FlagCopy.keyTape [bitSymbol fl]) (word V) (word W) 0 0 0 0) 3 := by
  have h := keyBack_runs (ready fl V W) [bitSymbol fl] rfl rfl (KeyRoutine.keyWord_interior_single fl)
  simpa only [CountedRepairKeyAppend.no,ready,set_bank1,List.length_singleton] using h

theorem reads_test (fl : Bool) (V W : List Bool) : test (ready fl V W).reads=fl := by
  cases fl <;> simp [test,Tapes.reads,ready,bank,word,putWord_head,bitSymbol]

theorem conditional_runs (fl : Bool) (V W : List Bool) :
    HoareTime conditional (fun v => v=ready fl V W) (fun v => v=output fl V W)
      (3*(V.length+W.length)+12) := by
  have ht := yes_runs fl V W
  have hf := no_runs fl V W
  cases fl with
  | false =>
    have hbad : HoareTime yes (fun v => v=ready false V W ∧ test v.reads=true) (fun v => v=output false V W) (3*(V.length+W.length)+11) := by
      rintro v ⟨rfl,h⟩; rw [reads_test] at h; contradiction
    have hgood : HoareTime no (fun v => v=ready false V W ∧ test v.reads=false) (fun v => v=output false V W) 3 :=
      hf.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
    exact (branch_hoare test hbad hgood).consequence (fun _ h => h) (fun _ h => h) (by omega)
  | true =>
    have hbad : HoareTime no (fun v => v=ready true V W ∧ test v.reads=false) (fun v => v=output true V W) 3 := by
      rintro v ⟨rfl,h⟩; rw [reads_test] at h; contradiction
    have hgood : HoareTime yes (fun v => v=ready true V W ∧ test v.reads=true) (fun v => v=output true V W) (3*(V.length+W.length)+11) :=
      ht.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
    exact (branch_hoare test hgood hbad).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs (fl : Bool) (V W : List Bool) :
    HoareTime program (fun v => v=input fl V W) (fun v => v=output fl V W)
      (3*(V.length+W.length)+18) := by
  exact ((setup_runs fl V W).seq (conditional_runs fl V W)).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRepairKeyAppend
