import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyData

/-! Genuine early low payload execution followed by formatting/repair/decode.
The actual low output supplies the repair input on the same physical tape. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open Networks.Shared50ModularControl (prime)
open ActiveRepairLayoutRecordsData (Array)
open ActiveRepairLayoutRecordsPayloadEarlyData
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

abbrev lowCount := ActivePrefixEarlySequenceOriginalRun.count
abbrev count := 243+lowCount
def lowProgram := ActivePrefixEarlySequenceOriginalPlaced.program focus focus_injective
def repairProgram := extend (extend ActiveRepairLayoutRecordsOriginalEarlyAlphabet.program 8) lowCount
def two {t a q r : ℕ} (M : Program t q a) (N : Program t r a) := seq M N

theorem two_runs {t a q r b c : ℕ} {M : Program t q a} {N : Program t r a}
    {P Q R : TapePred t a} (hM : HoareTime M P Q b) (hN : HoareTime N Q R c) :
    HoareTime (two M N) P R (b+c+1) :=
  (hM.seq hN).consequence (fun _ h => h) (fun _ h => h) (by omega)

def program := two lowProgram repairProgram
def outputSlot : Fin count := Fin.castAdd lowCount (Fin.castAdd 8 (223 : Fin 235))
theorem outputSlot_value : outputSlot.val=223 := rfl
def cost (d : Inputs s p offset rows) (x : Array s rows) :=
  ActivePrefixEarlySequenceOriginalRun.cost s p rows+
  ActiveRepairLayoutRecordsAssemblyOriginalEarly.cost d
    (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.chunks d x)+1

theorem repair_runs (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    HoareTime repairProgram
      (fun v => v=CleanSubbank.bank (s:=lowCount) (repairedInput d x))
      (fun v => v=CleanSubbank.bank (s:=lowCount) (output d x))
      (ActiveRepairLayoutRecordsAssemblyOriginalEarly.cost d
        (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.chunks d x)) := by
  have h := ActiveRepairLayoutRecordsAlphabet.map_hoare_eq
    (ActiveRepairLayoutRecordsAssemblyOriginalEarly.runs d
      (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d x) hfit hq3
      (ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks_lengths _ _ _ _ _ _ _ _ _ _)
      (ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks_count _ _ _ _ _ _ _ _ _ _))
  exact hoare_extend_eq (hoare_extend_eq h (controls d)) (SharedBank.empty lowCount prime)

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    HoareTime program (fun v => v=CleanSubbank.bank (s:=lowCount) (ActiveRepairLayoutRecordsPayloadEarlyData.input d x))
      (fun v => v=CleanSubbank.bank (s:=lowCount) (output d x)) (cost d x) := by
  have h := ActivePrefixEarlySequenceOriginalPlaced.runs (ActiveRepairLayoutRecordsPayloadEarlyData.input d x) focus focus_injective hfit d x (sources d x)
  rw [low_output d x hfit] at h
  exact two_runs h (repair_runs d x hfit hq3)

theorem output_ideal (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    (CleanSubbank.bank (s:=lowCount) (output d x)).tape outputSlot=
      ActiveTargetRotation.word (a:=prime)
        (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
          p.compactFits p.activeSize
          (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
            (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive
              (ActiveRepairLayoutRecordsHeadersData.repair d))) x) := by
  have h := ActiveRepairLayoutRecordsOriginalEarlyAlphabet.output_ideal d x hfit hq3
  simp only [CleanSubbank.bank,output,outputSlot,Tapes.append,Fin.addCases_left]
  simpa only [List.map_ofFn,ActiveTargetRotation.word,Function.comp_def] using h

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyRun
