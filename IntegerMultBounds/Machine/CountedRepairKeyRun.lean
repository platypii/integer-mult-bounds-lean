import IntegerMultBounds.Machine.CountedRepairKeyCleanup

/-! A fixed-control repair key machine from the original headers and actual
short scan counter, with all generated words erased at its endpoint. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyRun
noncomputable section
open CountedRepairKeyBank

def bits (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z : List Bool) :=
  CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z ++ PackedInverse.w q b hb hbq V W Z

def output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  bank (PackedInverse.input [] [] Z (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0)
    hs cs (FlagCopy.keyTape (FlagCopy.keyWord (flag q b V W Z) (bits q b hb hbq V W Z)))
    (fun _ => blank) (fun _ => blank) 0 0 0

def program := seq (seq CountedRepairKeyPrefix.program CountedRepairKeyWrite.program) CountedRepairKeyCleanup.program

theorem cleanup_output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    CountedRepairKeyCleanup.output (CountedRepairKeyWrite.output q b hb hbq V W Z cs hs)=output q b hb hbq V W Z cs hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleanup_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    HoareTime CountedRepairKeyCleanup.program
      (fun v => v=CountedRepairKeyWrite.output q b hb hbq V W Z cs hs)
      (fun v => v=output q b hb hbq V W Z cs hs) (60*((Z.length+1)*(q+b+1))) := by
  have h := CountedRepairKeyCleanup.runs (CountedRepairKeyWrite.output q b hb hbq V W Z cs hs)
    V W (PackedInverse.w1 q b hb hbq V W Z) (PackedInverse.t q b hb hbq V W Z)
    (PackedInverse.v1 q b hb hbq V W Z) (PackedInverse.w q b hb hbq V W Z)
    (PackedInverse.v q b hb hbq V W Z) (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)
    [flag q b V W Z] rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [cleanup_output] at h
  obtain ⟨_,hw1,_,ht,_,hv1,_,hw,_,hv⟩ := PackedInverse.lengths q b hb hbq V W Z hV hW
  refine h.consequence (fun _ h => h) (fun _ h => h) ?_
  rw [hV,hW,hw1,ht,hv1,hw,hv,CountedIdealToggle.word_length q _ Z (by omega) hv,hv]
  simp only [List.length_singleton]
  nlinarith

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=CountedRepairKeyBank.input Z cs hs)
      (fun v => v=output q b hb hbq (V q Z cs) (W q b Z cs) Z cs hs)
      (5100*((Z.length+1)*(q+b+1))) := by
  have hV : (V q Z cs).length=Z.length*q := Gather.field_length _ _ _
  have hW : (W q b Z cs).length=Z.length*b := Gather.field_length _ _ _
  have h1 := CountedRepairKeyPrefix.runs q b hb hbq hbq3 Z cs hs hv hc
  have h2 := CountedRepairKeyWrite.runs q b hb hbq (V q Z cs) (W q b Z cs) Z cs hs hV hW
  have h3 := cleanup_runs q b hb hbq (V q Z cs) (W q b Z cs) Z cs hs hV hW
  have hp : 1≤(Z.length+1)*(q+b+1) := by
    have hpos := Nat.mul_pos (by omega : 0<Z.length+1) (by omega : 0<q+b+1)
    omega
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRepairKeyRun
