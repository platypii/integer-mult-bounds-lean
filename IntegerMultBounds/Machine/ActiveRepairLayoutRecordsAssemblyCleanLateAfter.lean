import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanCommon

/-! Original-header raw repair with actual final erasure of every copied
consumer descriptor. Only the original headers and two raw array tapes remain. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanLateAfter
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsBankHeaders (words)
open ActiveRepairLayoutRecordsAssemblyCleanCommon
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def focus : Fin 15 → Fin 244 := ![88,89,90,91,92,93,94,95,96,97,70,71,72,73,74]
theorem focus_injective : Function.Injective focus := by decide
def cleanProgram := ActiveRepairLayoutRecordsAssemblyCleanCommon.program focus focus_injective
  (show 15+229=244 from rfl)
def program := seq ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.program cleanProgram
def output (d : Inputs s p offset rows) (cs : List (List Bool)) :=
  SharedBank.strip (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs) focus
def cost (d : Inputs s p offset rows) (cs : List (List Bool)) :=
  ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.cost d cs+1+FixedHeaderBankCopy.cleanupCost (t:=0) (words d)

theorem metadata (d : Inputs s p offset rows) (cs : List (List Bool)) :
    SharedBank.payload (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs) focus=FixedHeaderBankCopy.headerBank (words d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleans (d : Inputs s p offset rows) (cs : List (List Bool)) :
    HoareTime cleanProgram (fun v => v=ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs)
      (fun v => v=output d cs) (FixedHeaderBankCopy.cleanupCost (t:=0) (words d)) :=
  ActiveRepairLayoutRecordsAssemblyCleanCommon.runs focus focus_injective rfl
    (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs) (words d) (metadata d cs)

theorem runs (d : Inputs s p offset rows) (cs : List (List Bool))
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q)
    (hw : ∀xs∈cs,xs.length=s.payload) (hn : cs.length=rows*2^s.bits) :
    HoareTime program (fun v => v=ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d cs)
      (fun v => v=output d cs) (cost d cs) :=
  (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.runs d cs hfit hq3 hw hn).seq (cleans d cs)


theorem output_heads (d : Inputs s p offset rows) (cs : List (List Bool)) :
    (output d cs).head=(SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d cs) 232
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs).tape 232) 0).head := by
  dsimp only [output,SharedBank.strip]
  funext i; fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)]; rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem output_tapes (d : Inputs s p offset rows) (cs : List (List Bool)) :
    (output d cs).tape=(SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d cs) 232
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs).tape 232) 0).tape := by
  dsimp only [output,SharedBank.strip]
  funext i; fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)]; rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem output_literal (d : Inputs s p offset rows) (cs : List (List Bool)) :
    output d cs=SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d cs) 232
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs).tape 232) 0 :=
  congrArg₂ Tapes.mk (output_heads d cs) (output_tapes d cs)

theorem raw_output_retained (d : Inputs s p offset rows) (cs : List (List Bool)) :
    (output d cs).tape 232=(ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output d cs).tape 232 := by
  dsimp only [output,SharedBank.strip]
  rw [ite_eq_right (show ¬∃j,focus j=(232:Fin 244) from by decide)]

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) :
    (output d (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array)).tape 232=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d))) array)).map bitSymbol) := by
  rw [raw_output_retained]
  exact ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.output_ideal d array hfit hq3


theorem cost_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    cost d (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array)≤
      (ActiveRepairLayoutRecordsHeadersAfterBudget.constant+ActiveRepairLateOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+1017)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
  have hp : 0<s.payload := by omega
  have hV : 0<ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
    unfold ActiveRepairLayoutRecordsHeadersBudget.volume Shape.recordWidth; positivity
  have hP := ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.cost_linear d array hfit hq3 hrows hR D hdensity
  have hQ := ActiveRepairLayoutRecordsAssemblyCleanCommon.cost_linear_after d hrows hp hfit
  unfold cost
  exact final_cost_absorb _ _ _ _ hV hP hQ

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.input d (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array))
      (fun v => v=output d (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array))
      ((ActiveRepairLayoutRecordsHeadersAfterBudget.constant+ActiveRepairLateOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankAfterBudget.eraseConstant+1017)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows) :=
  ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.runs d (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array) hfit hq3
    (ActiveRepairLayoutRecordsAssemblyLayoutLate.chunks_lengths _ _ _ _ _ _ _ _ _ _)
    (ActiveRepairLayoutRecordsAssemblyLayoutLate.chunks_count _ _ _ _ _ _ _ _ _ _)).seq
    (cleans d (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.chunks d array))).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear d array hfit hq3 hrows hR D hdensity)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanLateAfter
