import IntegerMultBounds.Machine.ActiveRepairRankHeadersData

/-! Physical original-width descriptor producer and matching post-use eraser.
Parser8 and patch7 outputs retain canonical marked words, all scratch is blank. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankHeadersRun
noncomputable section
open ActiveRepairRankHeadersCommands ActiveRepairRankHeadersData
variable {a : ℕ}

def input (hs : Fin 10 → List Bool) : Tapes 43 a :=
  CleanSubbank.bank (s := 15) ((FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 18 a))
def program (side : SourceSide) := (compile (a := a) (schedule side)).2

theorem input_eq (d : Widths) (hs : Fin 10 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    input (a := a) hs=bank (initial d) := by
  have he (i : Fin 10) : hs i=RecursiveChildQuotientsConstant.bits (originalValues d i) :=
    CompactGadgetReservationHeadersCore.canonical_bits _ _ (hc i) (hv i)
  unfold input bank CleanSubbank.bank
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [initial,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,RecursiveDimensionBank.head,RecursiveDimensionBank.tape,SharedBank.empty,Fin.addCases,he]

 theorem produces (side : SourceSide) (d : Widths) (hw : d.w≤d.H)
    (hs : Fin 10 → List Bool) (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : ∀ i, originalValues d i≤d.addressBits) :
    HoareTime (program (a := a) side) (fun x => x=input hs)
      (fun x => x=bank (finished side d)) (constant*(d.addressBits+1)) := by
  have h := schedule_runs (a := a) (schedule side) (initial d) (schedule_valid side d hw)
  rw [execute_eq] at h
  exact h.consequence (fun _ h => (h.trans (input_eq d hs hv hc))) (fun _ h => h) (cost_bound side d hb)

def cleanupSchedule : List Command :=
  [.erase 10,.erase 11,.erase 12,.erase 13,.erase 14,.erase 15,.erase 16,.erase 17,
    .erase 18,.erase 19,.erase 20,.erase 21,.erase 22,.erase 23,.erase 24]
def cleanupProgram := (compile (a := a) cleanupSchedule).2

theorem cleanup_valid (side : SourceSide) (d : Widths) : validSchedule cleanupSchedule (finished side d) := by
  simp [cleanupSchedule,validSchedule,valid,eval,Function.update,finished]

theorem cleanup_eq (side : SourceSide) (d : Widths) :
    execute cleanupSchedule (finished side d)=initial d := by
  funext i
  fin_cases i <;> simp [cleanupSchedule,execute,eval,Function.update,finished,initial,originalValues]

theorem finished_bounded (side : SourceSide) (d : Widths)
    (hb : ∀ i, originalValues d i≤d.addressBits) : Bounded (finished side d) (8*d.addressBits) := by
  have h0 : d.H≤d.addressBits := hb 0
  have h1 : d.B≤d.addressBits := hb 1
  have h2 : d.F≤d.addressBits := hb 2
  have h3 : d.before≤d.addressBits := hb 3
  have h4 : d.after≤d.addressBits := hb 4
  have h5 : d.m≤d.addressBits := hb 5
  have h6 : d.w≤d.addressBits := hb 6
  have h7 : d.sourceOffset≤d.addressBits := hb 7
  have h8 : d.sourceWidth≤d.addressBits := hb 8
  have hsub := Nat.sub_le d.H d.w
  intro i
  cases side <;> fin_cases i
  all_goals simp [finished,sourceStart,targetStart,prefixStart,tStart,uStart]
  all_goals omega

def cleanupConstant := 2400*3^15

theorem cleans (side : SourceSide) (d : Widths) (hs : Fin 10 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : ∀ i, originalValues d i≤d.addressBits) :
    HoareTime (cleanupProgram (a := a)) (fun x => x=bank (finished side d))
      (fun x => x=input hs) (cleanupConstant*(d.addressBits+1)) := by
  have h := schedule_runs (a := a) cleanupSchedule (finished side d) (cleanup_valid side d)
  rw [cleanup_eq,←input_eq d hs hv hc] at h
  have ht := scheduleCost_bounded cleanupSchedule (finished side d) (8*d.addressBits) (finished_bounded side d hb)
  have hl : cleanupSchedule.length=15 := rfl
  rw [hl] at ht
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold cleanupConstant; nlinarith)

end
end IntegerMultBounds.Machine.ActiveRepairRankHeadersRun
