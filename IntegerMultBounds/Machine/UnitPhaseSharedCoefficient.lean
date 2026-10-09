import IntegerMultBounds.Machine.UnitPhaseRecordIO
import IntegerMultBounds.Machine.UnitPhaseCoreReset
import IntegerMultBounds.Machine.PlacementBank

/-! One coefficient consumes retained physical phase flags and leaves them
unchanged. Arithmetic, IO, and source erasure are charged independently of
address width; this is the inner body for a polynomial row. -/
namespace IntegerMultBounds.Machine.UnitPhaseSharedCoefficient
noncomputable section
open UnitPhaseNumerator (flags coreInput coreOutput words)
open SharedPlacementAlphabet (setTape)
open DelimitedRadixRecord (Context)

def slots : Fin 8 → Fin 60 := fun i => ⟨48+i.val,by omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [slots] at this
  omega
def placement := InjectivePlacement.placement slots slots_injective (by decide : 8+52=60)
def coreSlots : Fin 6 → Fin 60 := fun i => ⟨50+i.val,by omega⟩
theorem coreSlots_injective : Function.Injective coreSlots := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [coreSlots] at this
  omega
def corePlacement := InjectivePlacement.placement coreSlots coreSlots_injective (by decide : 6+54=60)
def multiply := Placement.placed UnitPhaseNumerator.program placement
def cleanup := Placement.placed UnitPhaseCoreReset.program corePlacement
def program := seq (seq (seq UnitPhaseRecordIO.readProgram multiply) UnitPhaseRecordIO.emitProgram) cleanup

def sources (a : Context 2) : ℕ → List (Fin 2) := fun j => if j=0 then a.re else a.im
def read (v : Tapes 60 2) (a : Context 2) := UnitPhaseRecordIO.readOutput v a
def applied (v : Tapes 60 2) (a : Context 2) (p : Fin 4) :=
  Placement.replace placement (read v a) ((flags p).append (coreOutput p (sources a)))
def emitted (v : Tapes 60 2) (a : Context 2) (p : Fin 4) :=
  UnitPhaseRecordIO.emitOutput (applied v a p) (words p 0 (sources a)) (words p 1 (sources a))
def output (v : Tapes 60 2) (a : Context 2) (p : Fin 4) :=
  Placement.replace corePlacement (emitted v a p) (SharedBank.empty 6 2)

private theorem read_active (v : Tapes 60 2) (a : Context 2) (p : Fin 4)
    (hflags : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=(flags p).head i ∧
      v.tape ⟨48+i.val,by omega⟩=(flags p).tape i)
    (hcore : ∀ i : Fin 6,v.head (coreSlots i)=0 ∧ v.tape (coreSlots i)=(fun _ => blank)) :
    Placement.active placement (read v a)=(flags p).append (coreInput (sources a)) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,
    TwoTapeAt.result,setTape,slots,Tapes.append,Fin.addCases,coreInput,RadixLinearCombinationRefresh.controls,sources]
  all_goals first
    | rfl
    | exact (hflags 0).1 | exact (hflags 1).1 | exact (hflags 0).2 | exact (hflags 1).2
    | exact (hcore 2).1 | exact (hcore 3).1 | exact (hcore 4).1 | exact (hcore 5).1
    | exact (hcore 2).2 | exact (hcore 3).2 | exact (hcore 4).2 | exact (hcore 5).2

private theorem applied_core (v : Tapes 60 2) (a : Context 2) (p : Fin 4) :
    Placement.active corePlacement (emitted v a p)=coreInput (sources a) := by
  rw [corePlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [emitted,UnitPhaseRecordIO.emitOutput,setTape,coreSlots]
  all_goals first
    | rfl
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 2
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 3
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 5
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 7
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 2
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 3
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 5
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) (read v a)
        ((flags p).append (coreOutput p (sources a))) 7

theorem runs (v : Tapes 60 2) (a : Context 2) (p : Fin 4) (w : ℕ)
    (hw : a.re.length=w ∧ a.im.length=w)
    (hs : v.tape 56=a.tape ∧ v.head 56=a.start)
    (hflags : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=(flags p).head i ∧
      v.tape ⟨48+i.val,by omega⟩=(flags p).tape i)
    (hcore : ∀ i : Fin 6,v.head (coreSlots i)=0 ∧ v.tape (coreSlots i)=(fun _ => blank)) :
    HoareTime program (fun z => z=v) (fun z => z=output v a p) (24*w+83) := by
  have hx : ∀ j,(sources a j).length=w := by intro j; dsimp [sources]; split_ifs <;> first | exact hw.1 | exact hw.2
  have h0 := UnitPhaseRecordIO.read_runs v a hs ⟨(hcore 0).2,(hcore 0).1⟩ ⟨(hcore 1).2,(hcore 1).1⟩
  have hsmall := Placement.hoare_at (UnitPhaseNumerator.runs p (sources a) w hx) placement
    (read v a) (read_active v a p hflags hcore)
  have h1 : HoareTime multiply (fun z => z=read v a) (fun z => z=applied v a p) (12*w+45) := by
    apply hsmall.consequence (fun _ h => h) _ le_rfl
    rintro z ⟨small,rfl,rfl⟩
    rfl
  have h2 := UnitPhaseRecordIO.emit_runs (applied v a p) (words p 0 (sources a)) (words p 1 (sources a))
    ⟨InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) _ _ 4,
      InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) _ _ 4⟩
    ⟨InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) _ _ 6,
      InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) _ _ 6⟩
  have h3 := Placement.hoare_at (UnitPhaseCoreReset.runs (sources a) w hx) corePlacement
    (emitted v a p) (applied_core v a p)
  apply (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) _ _
  · rintro z ⟨small,rfl,rfl⟩
    rfl
  · rw [hw.1,hw.2,UnitPhaseNumerator.words_length _ _ _ _ hx,UnitPhaseNumerator.words_length _ _ _ _ hx]
    omega

theorem core_blank (v : Tapes 60 2) (a : Context 2) (p : Fin 4) (i : Fin 6) :
    (output v a p).head (coreSlots i)=0 ∧ (output v a p).tape (coreSlots i)=(fun _ => blank) := by
  exact ⟨InjectivePlacement.replace_head_slot coreSlots coreSlots_injective (by decide : 6+54=60) _ _ i,
    InjectivePlacement.replace_tape_slot coreSlots coreSlots_injective (by decide : 6+54=60) _ _ i⟩

theorem flags_retained (v : Tapes 60 2) (a : Context 2) (p : Fin 4) (i : Fin 2) :
    (output v a p).head ⟨48+i.val,by omega⟩=(flags p).head i ∧
      (output v a p).tape ⟨48+i.val,by omega⟩=(flags p).tape i := by
  have hx : ∀ j : Fin 6,coreSlots j≠(⟨48+i.val,by omega⟩ : Fin 60) := by
    intro j h; have := congrArg Fin.val h; simp only [coreSlots] at this; omega
  unfold output corePlacement
  rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ hx,
    InjectivePlacement.replace_tape_other _ _ _ _ _ _ hx]
  fin_cases i
  all_goals simp only [emitted,UnitPhaseRecordIO.emitOutput,setTape,Function.update_apply]
  all_goals norm_num
  all_goals constructor
  all_goals first
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) _ _ 0
    | exact InjectivePlacement.replace_head_slot slots slots_injective (by decide : 8+52=60) _ _ 1
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) _ _ 0
    | exact InjectivePlacement.replace_tape_slot slots slots_injective (by decide : 8+52=60) _ _ 1

def streamOutput (v : Tapes 60 2) (a : Context 2) (p : Fin 4) :=
  setTape (setTape v 56 a.tape (a.start+a.re.length+a.im.length+2)) 58
    (putWord (v.tape 58) (v.head 58) (DelimitedRadixRecord.complex (words p 0 (sources a)) (words p 1 (sources a))))
    (v.head 58+(words p 0 (sources a)).length+(words p 1 (sources a)).length+2)

theorem output_eq (v : Tapes 60 2) (a : Context 2) (p : Fin 4)
    (hflags : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=(flags p).head i ∧
      v.tape ⟨48+i.val,by omega⟩=(flags p).tape i)
    (hcore : ∀ i : Fin 6,v.head (coreSlots i)=0 ∧ v.tape (coreSlots i)=(fun _ => blank)) :
    output v a p=streamOutput v a p := by
  have hs58 : ∀ j : Fin 8,slots j≠(58 : Fin 60) := by
    intro j h
    have := congrArg Fin.val h
    simp only [slots] at this
    omega
  have h58h : (applied v a p).head 58=v.head 58 := by
    rw [applied,placement,InjectivePlacement.replace_head_other _ _ _ _ _ _ hs58]
    simp [read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,setTape]
  have h58t : (applied v a p).tape 58=v.tape 58 := by
    rw [applied,placement,InjectivePlacement.replace_tape_other _ _ _ _ _ _ hs58]
    simp [read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,TwoTapeAt.result,setTape]
  apply Placement.Tapes.ext'
  all_goals
    intro i
    by_cases hc : 50 ≤ i.val ∧ i.val < 56
    · let j : Fin 6 := ⟨i.val-50,by omega⟩
      have hj : coreSlots j=i := by apply Fin.ext; simp only [coreSlots]; dsimp [j]; omega
      rw [←hj]
      have hn56 : 50+j.val≠56 := by omega
      have hn58 : 50+j.val≠58 := by omega
      first
        | rw [(core_blank v a p j).1]; simpa (disch := omega) [streamOutput,setTape,coreSlots,Function.update_apply,Fin.ext_iff,hn56,hn58] using (hcore j).1.symm
        | rw [(core_blank v a p j).2]; simpa (disch := omega) [streamOutput,setTape,coreSlots,Function.update_apply,Fin.ext_iff,hn56,hn58] using (hcore j).2.symm
    · by_cases hf : 48 ≤ i.val ∧ i.val < 50
      · let j : Fin 2 := ⟨i.val-48,by omega⟩
        have hj : (⟨48+j.val,by omega⟩ : Fin 60)=i := by apply Fin.ext; dsimp [j]; omega
        rw [←hj]
        first
          | rw [(flags_retained v a p j).1]; simpa (disch := omega) [streamOutput,setTape,Function.update_apply,Fin.ext_iff] using (hflags j).1.symm
          | rw [(flags_retained v a p j).2]; simpa (disch := omega) [streamOutput,setTape,Function.update_apply,Fin.ext_iff] using (hflags j).2.symm
      · have hx : ∀ j : Fin 6,coreSlots j≠i := by
          intro j h
          have := congrArg Fin.val h
          simp only [coreSlots] at this
          omega
        have hy : ∀ j : Fin 8,slots j≠i := by
          intro j h
          have := congrArg Fin.val h
          simp only [slots] at this
          omega
        have hn50 : i.val≠50 := by omega
        have hn51 : i.val≠51 := by omega
        have hn52 : i.val≠52 := by omega
        have hn54 : i.val≠54 := by omega
        unfold output corePlacement
        first
          | rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ hx]
          | rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hx]
        simp only [emitted,UnitPhaseRecordIO.emitOutput,setTape,Function.update_apply,h58h,h58t]
        have hh : (applied v a p).head i=(read v a).head i :=
          InjectivePlacement.replace_head_other slots slots_injective (by decide : 8+52=60) _ _ i hy
        have ht : (applied v a p).tape i=(read v a).tape i :=
          InjectivePlacement.replace_tape_other slots slots_injective (by decide : 8+52=60) _ _ i hy
        simp (disch := omega) [hh,ht,read,UnitPhaseRecordIO.readOutput,UnitPhaseRecordIO.readFirst,
          TwoTapeAt.result,streamOutput,setTape,Function.update_apply,Fin.ext_iff,hn50,hn51,hn52,hn54]
        split_ifs <;> simp_all

end
end IntegerMultBounds.Machine.UnitPhaseSharedCoefficient
