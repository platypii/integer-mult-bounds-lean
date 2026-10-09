import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanCommon

/-! Original-header raw repair with actual final erasure of every copied
consumer descriptor. Only the original headers and two raw array tapes remain. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanEarly
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsBankHeaders (words)
open ActiveRepairLayoutRecordsAssemblyCleanCommon
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def focus : Fin 15 → Fin 235 := ![87,88,89,90,91,92,93,94,95,96,70,71,72,73,74]
theorem focus_injective : Function.Injective focus := by decide
def cleanProgram := ActiveRepairLayoutRecordsAssemblyCleanCommon.program focus focus_injective
  (show 15+220=235 from rfl)
def program := seq ActiveRepairLayoutRecordsAssemblyOriginalEarly.program cleanProgram
def output (d : Inputs s p offset rows) (cs : List (List Bool)) :=
  SharedBank.strip (ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs) focus
def cost (d : Inputs s p offset rows) (cs : List (List Bool)) :=
  ActiveRepairLayoutRecordsAssemblyOriginalEarly.cost d cs+1+FixedHeaderBankCopy.cleanupCost (t:=0) (words d)

theorem metadata (d : Inputs s p offset rows) (cs : List (List Bool)) :
    SharedBank.payload (ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs) focus=FixedHeaderBankCopy.headerBank (words d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleans (d : Inputs s p offset rows) (cs : List (List Bool)) :
    HoareTime cleanProgram (fun v => v=ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs)
      (fun v => v=output d cs) (FixedHeaderBankCopy.cleanupCost (t:=0) (words d)) :=
  ActiveRepairLayoutRecordsAssemblyCleanCommon.runs focus focus_injective rfl
    (ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs) (words d) (metadata d cs)

theorem runs (d : Inputs s p offset rows) (cs : List (List Bool))
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q)
    (hw : ∀xs∈cs,xs.length=s.payload) (hn : cs.length=rows*2^s.bits) :
    HoareTime program (fun v => v=ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d cs)
      (fun v => v=output d cs) (cost d cs) :=
  (ActiveRepairLayoutRecordsAssemblyOriginalEarly.runs d cs hfit hq3 hw hn).seq (cleans d cs)


theorem output_heads (d : Inputs s p offset rows) (cs : List (List Bool)) :
    (output d cs).head=(SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d cs) 223
      ((ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs).tape 223) 0).head := by
  dsimp only [output,SharedBank.strip]
  funext i; fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)]; rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem output_tapes (d : Inputs s p offset rows) (cs : List (List Bool)) :
    (output d cs).tape=(SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d cs) 223
      ((ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs).tape 223) 0).tape := by
  dsimp only [output,SharedBank.strip]
  funext i; fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)]; rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem output_literal (d : Inputs s p offset rows) (cs : List (List Bool)) :
    output d cs=SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d cs) 223
      ((ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs).tape 223) 0 :=
  congrArg₂ Tapes.mk (output_heads d cs) (output_tapes d cs)

theorem raw_output_retained (d : Inputs s p offset rows) (cs : List (List Bool)) :
    (output d cs).tape 223=(ActiveRepairLayoutRecordsAssemblyOriginalEarly.output d cs).tape 223 := by
  dsimp only [output,SharedBank.strip]
  rw [ite_eq_right (show ¬∃j,focus j=(223:Fin 235) from by decide)]

theorem output_ideal (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    (output d (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array)).tape 223=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize
        (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
          (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive (ActiveRepairLayoutRecordsHeadersData.repair d))) array)).map bitSymbol) := by
  rw [raw_output_retained]
  exact ActiveRepairLayoutRecordsAssemblyOriginalEarly.output_ideal d array hfit hq3


theorem cost_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    cost d (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array)≤
      (ActiveRepairLayoutRecordsHeadersBudget.constant+ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankBudget.eraseConstant+1017)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
  have hp : 0<s.payload := by omega
  have hV : 0<ActiveRepairLayoutRecordsHeadersBudget.volume s rows := by
    unfold ActiveRepairLayoutRecordsHeadersBudget.volume Shape.recordWidth; positivity
  have hP := ActiveRepairLayoutRecordsAssemblyOriginalEarly.cost_linear d array hfit hq3 hrows hR D hdensity
  have hQ := ActiveRepairLayoutRecordsAssemblyCleanCommon.cost_linear d hrows hp hfit
  unfold cost
  exact final_cost_absorb _ _ _ _ hV hP hQ

theorem runs_linear (d : Inputs s p offset rows) (array : ActiveRepairLayoutRecordsData.Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=ActiveRepairLayoutRecordsAssemblyOriginalEarly.input d (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array))
      (fun v => v=output d (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array))
      ((ActiveRepairLayoutRecordsHeadersBudget.constant+ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+
        ActiveRepairLayoutRecordsBankBudget.eraseConstant+1017)*
        ActiveRepairLayoutRecordsHeadersBudget.volume s rows) :=
  ((ActiveRepairLayoutRecordsAssemblyOriginalEarly.runs d (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array) hfit hq3
    (ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks_lengths _ _ _ _ _ _ _ _ _ _)
    (ActiveRepairLayoutRecordsAssemblyLayoutEarly.chunks_count _ _ _ _ _ _ _ _ _ _)).seq
    (cleans d (ActiveRepairLayoutRecordsAssemblyOriginalEarly.chunks d array))).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear d array hfit hq3 hrows hR D hdensity)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyCleanEarly
