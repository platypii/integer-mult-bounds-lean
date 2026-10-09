import IntegerMultBounds.Machine.ActiveRepairEarlyFieldsRun
import IntegerMultBounds.Machine.CountedRepairKeyCleanup

/-! Retain only the extracted originals, actual guard flag and recovered
repair destination fields; physically erase the four inverse intermediates. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyFieldsCleanup
noncomputable section
open SharedPlacementAlphabet (setTape)
open CountedRepairKeyCleanup (clearAt clears)
open CountedGuardGadgetRecord (word)
open ActiveRepairEarlyFieldsBank

def result (v : Tapes 30 1) :=
  setTape (setTape (setTape (setTape v 3 (fun _ => blank) 0) 4 (fun _ => blank) 0)
    5 (fun _ => blank) 0) 8 (fun _ => blank) 0

def program := seq (seq (seq (clearAt 3) (clearAt 4)) (clearAt 5)) (clearAt 8)

theorem clears_four (v : Tapes 30 1) (x3 x4 x5 x8 : List Bool)
    (h3 : v.tape 3=word x3) (p3 : v.head 3=0)
    (h4 : v.tape 4=word x4) (p4 : v.head 4=0)
    (h5 : v.tape 5=word x5) (p5 : v.head 5=0)
    (h8 : v.tape 8=word x8) (p8 : v.head 8=0) :
    HoareTime program (fun z => z=v) (fun z => z=result v)
      (2*(x3.length+x4.length+x5.length+x8.length)+15) := by
  let A := setTape v 3 (fun _ => blank) 0
  let B := setTape A 4 (fun _ => blank) 0
  let C := setTape B 5 (fun _ => blank) 0
  have h1 := clears v 3 x3 h3 p3
  have h2 := clears A 4 x4 (by simpa [A,setTape] using h4) (by simpa [A,setTape] using p4)
  have h3' := clears B 5 x5 (by simpa [B,A,setTape] using h5) (by simpa [B,A,setTape] using p5)
  have h4' := clears C 8 x8 (by simpa [C,B,A,setTape] using h8) (by simpa [C,B,A,setTape] using p8)
  exact (((h1.seq h2).seq h3').seq h4').consequence (fun _ h => h) (fun _ h => h) (by omega)

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  setTape (setTape (setTape (before V W Z cs hs) 6
    (word (PackedInverse.w q b hb hbq V W Z)) 0) 28
    (CountedGuardGadgetFinish.key (CountedGuardGadget.flags q b Z.length V W
      (CountedGuardConstantsData.c1 q b) (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b))) 1)
    29 (word (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)) 0

theorem result_eq (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    result (toggled q b hb hbq V W Z cs hs)=output q b hb hbq V W Z cs hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    HoareTime program (fun z => z=toggled q b hb hbq V W Z cs hs)
      (fun z => z=output q b hb hbq V W Z cs hs) (30*((Z.length+1)*(q+b+1))) := by
  have h := clears_four (toggled q b hb hbq V W Z cs hs)
    (PackedInverse.w1 q b hb hbq V W Z) (PackedInverse.t q b hb hbq V W Z)
    (PackedInverse.v1 q b hb hbq V W Z) (PackedInverse.v q b hb hbq V W Z)
    rfl rfl rfl rfl rfl rfl rfl rfl
  rw [result_eq] at h
  obtain ⟨_,hw1,_,ht,_,hv1,_,_,_,hv⟩ := PackedInverse.lengths q b hb hbq V W Z hV hW
  apply h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [hw1,ht,hv1,hv]
  nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairEarlyFieldsCleanup
