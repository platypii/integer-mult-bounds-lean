import IntegerMultBounds.Machine.CountedRepairKeyBank

/-! Fixed-control rank splitting, inverse, original guard and ideal toggle on
one thirty-tape bank. The actual growing counter may have a short blank tail. -/
namespace IntegerMultBounds.Machine.CountedRepairKeyPrefix
noncomputable section
open CountedRepairKeyBank
open CountedRankSplitBank (placed_exact)

theorem rank_input (Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active rankPlace (CountedRepairKeyBank.input Z cs hs)=CountedRankSplitBank.bank (RepairScan.ctrTape cs)
      (fun _ => blank) (fun _ => blank) 1 0 0 hs none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rank_output (q b : ℕ) (Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active rankPlace (split q b Z cs hs)=CountedRankSplitBank.bank (RepairScan.ctrTape cs)
      (putWord (fun _ => blank) 0 ((V q Z cs).map bitSymbol))
      (putWord (fun _ => blank) 0 ((W q b Z cs).map bitSymbol)) 1 0 0 hs none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rank_extra (q b : ℕ) (Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra rankPlace (CountedRepairKeyBank.input Z cs hs)=Placement.extra rankPlace (split q b Z cs hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem rank_runs (q b : ℕ) (Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hq : 0<q) (hb : 0<b) (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime rankProgram (fun v => v=CountedRepairKeyBank.input Z cs hs) (fun v => v=split q b Z cs hs)
      (400*((Z.length+1)*(q+b+1))) := by
  exact placed_exact rankPlace _ _ _ _ (rank_input Z cs hs) (rank_output q b Z cs hs)
    (rank_extra q b Z cs hs) (CountedRankSplitEndpoint.runs_linear (fun _ => blank) (fun _ => blank) 0 0 cs hs q b Z.length hq hb hv hc)

theorem inverse_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime inverseProgram (fun v => v=before V W Z cs hs)
      (fun v => v=inverted q b hb hbq V W Z cs hs) (2669*((Z.length+1)*(q+b+1))) := by
  have h := CountedPackedInverse.inverse_hoare (a := 1) q b hb hbq V W Z
    (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 0 0 0 0 hs
    hV hW rfl rfl rfl rfl rfl hv hc
  exact hoare_extend_eq h (⟨![1,0,0,0],![RepairScan.ctrTape cs,FlagCopy.keyTape [],fun _ => blank,fun _ => blank]⟩ : Tapes 4 1)

theorem guard_input (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active guardPlace (inverted q b hb hbq V W Z cs hs)=CountedGuardOriginal.input V W (hs 1) (hs 2) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change RadixZeroFill.encodedBinary _=CountedLoopReuseAlphabet.binary _; exact (CountedGuardGadgetHeaders.binary_eq _).symm)

theorem guard_output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active guardPlace (guarded q b hb hbq V W Z cs hs)=CountedGuardOriginal.output q b Z.length V W (hs 1) (hs 2) (hs 0) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change RadixZeroFill.encodedBinary _=CountedLoopReuseAlphabet.binary _; exact (CountedGuardGadgetHeaders.binary_eq _).symm)

theorem guard_extra (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra guardPlace (inverted q b hb hbq V W Z cs hs)=Placement.extra guardPlace (guarded q b hb hbq V W Z cs hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem guard_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime guardProgram (fun v => v=inverted q b hb hbq V W Z cs hs)
      (fun v => v=guarded q b hb hbq V W Z cs hs) (1000*((Z.length+1)*(q+b+1))) := by
  have hcost : Z.length*(45*q+16*b+174)+52*q+82*b+433 ≤
      1000*((Z.length+1)*(q+b+1)) := by
    simpa only [Nat.mul_assoc] using CountedGuardOriginal.cost_volume q b Z.length
  have h0 := CountedGuardOriginal.runs (a := 1) q b Z.length V W (hs 1) (hs 2) (hs 0)
    (hv 0) (hc 0) (hv 1) (hc 1) (hv 2) (hc 2) hb hbq3 hV hW
  have h1 := h0.consequence (fun _ h => h) (fun _ h => h) hcost
  exact placed_exact guardPlace _ _ _ _ (guard_input q b hb hbq V W Z cs hs)
    (guard_output q b hb hbq V W Z cs hs) (guard_extra q b hb hbq V W Z cs hs) h1

theorem toggle_input (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active togglePlace (guarded q b hb hbq V W Z cs hs)=CountedIdealToggle.bank
      (PackedLine.bank (CountedGuardGadgetRecord.word (PackedInverse.w q b hb hbq V W Z))
        (CountedGuardGadgetRecord.word Z) (fun _ => blank)
        (CountedGuardGadgetRecord.word (PackedInverse.v q b hb hbq V W Z)) (fun _ => blank) 0 0 0 0 0) hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem toggle_output (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.active togglePlace (toggled q b hb hbq V W Z cs hs)=CountedIdealToggle.bank
      (PackedLine.bank (CountedGuardGadgetRecord.word (PackedInverse.w q b hb hbq V W Z))
        (CountedGuardGadgetRecord.word Z) (fun _ => blank)
        (CountedGuardGadgetRecord.word (PackedInverse.v q b hb hbq V W Z))
        (CountedGuardGadgetRecord.word (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)) 0 0 0 0 0) hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem toggle_extra (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    Placement.extra togglePlace (guarded q b hb hbq V W Z cs hs)=Placement.extra togglePlace (toggled q b hb hbq V W Z cs hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem toggle_runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime toggleProgram (fun v => v=guarded q b hb hbq V W Z cs hs)
      (fun v => v=toggled q b hb hbq V W Z cs hs) (533*((Z.length+1)*(q+b+1))) := by
  obtain ⟨_,_,_,_,_,_,_,hw,_,hvlen⟩ := PackedInverse.lengths q b hb hbq V W Z hV hW
  exact placed_exact togglePlace _ _ _ _ (toggle_input q b hb hbq V W Z cs hs)
    (toggle_output q b hb hbq V W Z cs hs) (toggle_extra q b hb hbq V W Z cs hs)
    (CountedIdealToggle.runs (a := 1) q b hb hbq (PackedInverse.w q b hb hbq V W Z) Z (PackedInverse.v q b hb hbq V W Z)
      (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 0 0 hs hw hvlen hv hc rfl rfl rfl rfl)

def program := seq (seq (seq rankProgram inverseProgram) guardProgram) toggleProgram

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q) (Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=CountedRepairKeyBank.input Z cs hs)
      (fun v => v=toggled q b hb hbq (V q Z cs) (W q b Z cs) Z cs hs)
      (5000*((Z.length+1)*(q+b+1))) := by
  have h1 := rank_runs q b Z cs hs (by omega) (by omega) hv hc
  have hV : (V q Z cs).length=Z.length*q := Gather.field_length _ _ _
  have hW : (W q b Z cs).length=Z.length*b := Gather.field_length _ _ _
  have h2 := inverse_runs q b hb hbq (V q Z cs) (W q b Z cs) Z cs hs hV hW hv hc
  have h3 := guard_runs q b hb hbq hbq3 (V q Z cs) (W q b Z cs) Z cs hs hV hW hv hc
  have h4 := toggle_runs q b hb hbq (V q Z cs) (W q b Z cs) Z cs hs hV hW hv hc
  have hp : 1≤(Z.length+1)*(q+b+1) := by
    have hpos := Nat.mul_pos (by omega : 0<Z.length+1) (by omega : 0<q+b+1)
    omega
  exact (((h1.seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedRepairKeyPrefix
