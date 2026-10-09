import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyRun
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsCleanAlphabet
import IntegerMultBounds.Machine.ActiveRepairArrayRecycle
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalBudget

/-! Actual early payload followed by clean original-input repair on one raw
tape. Every repair descriptor/work tape is erased; the sole extra output is
the ideal raw array on tape 223, while source 228 retains the actual low result. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyClean
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open Networks.Shared50ModularControl (prime)
open ActiveRepairLayoutRecordsData (Array)
open ActiveRepairLayoutRecordsPayloadEarlyData
open ActiveRepairLayoutRecordsPayloadEarlyRun (lowCount outputSlot lowProgram two two_runs)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def repairProgram := extend (extend ActiveRepairLayoutRecordsCleanAlphabet.Early.program 8) lowCount
def program := two lowProgram repairProgram
def output (d : Inputs s p offset rows) (x : Array s rows) :=
  (ActiveRepairLayoutRecordsCleanAlphabet.Early.output d
    (ActiveRepairLayoutRecordsCleanAlphabet.Early.chunks d x)).append (controls d)
def repairCoefficient (D : ℕ) := ActiveRepairLayoutRecordsHeadersBudget.constant+
  ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+ActiveRepairLayoutRecordsBankBudget.eraseConstant+1017
def cost (D : ℕ) (_d : Inputs s p offset rows) :=
  ActivePrefixEarlySequenceOriginalRun.cost s p rows+
    repairCoefficient D*ActiveRepairLayoutRecordsHeadersBudget.volume s rows+1

theorem runs_linear (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime program
      (fun v => v=CleanSubbank.bank (s:=lowCount) (ActiveRepairLayoutRecordsPayloadEarlyData.input d x))
      (fun v => v=CleanSubbank.bank (s:=lowCount) (output d x)) (cost D d) := by
  have hl := ActivePrefixEarlySequenceOriginalPlaced.runs
    (ActiveRepairLayoutRecordsPayloadEarlyData.input d x) focus focus_injective hfit d x (sources d x)
  rw [low_output d x hfit] at hl
  have hr := hoare_extend_eq (hoare_extend_eq
    (ActiveRepairLayoutRecordsCleanAlphabet.Early.runs_linear d x hfit hq3 hrows hR D hdensity)
    (controls d)) (SharedBank.empty lowCount prime)
  exact two_runs hl hr

theorem repairedInput_actual (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) :
    repairedInput d x=ActiveRepairLayoutRecordsPayloadEarlyData.input d
      (ActivePrefixEarlySequenceData.result s p offset hfit rows x) := by
  have h := low_output d x hfit
  rw [ActivePrefixEarlySequenceOriginalPlaced.result] at h
  change SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsPayloadEarlyData.input d x) 228
    (ActiveTargetRotation.word (ActivePrefixEarlySequenceData.result s p offset hfit rows x)) 0=_ at h
  rw [input_set] at h
  exact h.symm

theorem output_literal (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    CleanSubbank.bank (s:=lowCount) (output d x)=
      SharedPlacementAlphabet.setTape
        (CleanSubbank.bank (s:=lowCount) (ActiveRepairLayoutRecordsPayloadEarlyData.input d
          (ActivePrefixEarlySequenceData.result s p offset hfit rows x))) outputSlot
        (ActiveTargetRotation.word (a:=prime)
          (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
            p.compactFits p.activeSize
            (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
              (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive
                (ActiveRepairLayoutRecordsHeadersData.repair d))) x)) 0 := by
  have h := ActiveRepairLayoutRecordsCleanAlphabet.Early.output_literal d
    (ActiveRepairLayoutRecordsCleanAlphabet.Early.chunks d x)
  have hi := ActiveRepairLayoutRecordsOriginalEarlyAlphabet.output_ideal d x hfit hq3
  have hn : output d x=SharedPlacementAlphabet.setTape (repairedInput d x)
      (Fin.castAdd 8 (223 : Fin 235))
      (ActiveTargetRotation.word (a:=prime)
        (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
          p.compactFits p.activeSize
          (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
            (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive
              (ActiveRepairLayoutRecordsHeadersData.repair d))) x)) 0 := by
    unfold output
    rw [h,hi,←SharedPlacementAlphabet.setTape_append_left]
    simp only [repairedInput,ActiveTargetRotation.word,List.map_ofFn,Function.comp_def]
  rw [hn,repairedInput_actual d x hfit]
  exact (SharedPlacementAlphabet.setTape_append_left _ _ _ _ _).symm

abbrev count := ActiveRepairLayoutRecordsPayloadEarlyRun.count
def rawSlot : Fin count := Fin.castAdd lowCount (Fin.castAdd 8 (228 : Fin 235))
theorem rawSlot_value : rawSlot.val=228 := rfl
theorem slots_ne : outputSlot≠rawSlot := by
  intro h
  have hh := congrArg Fin.val h
  change 223=228 at hh
  omega

def ideal (d : Inputs s p offset rows) (x : Array s rows) :=
  ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize
    (ActiveRepairLayoutPermutation.earlyIdeal s p.q p.b p.n p.before p.after rows p.rho offset
      (p.f*p.q) .before (ActiveRepairLayoutKeysEarly.positive
        (ActiveRepairLayoutRecordsHeadersData.repair d))) x

def bank (d : Inputs s p offset rows) (x : Array s rows) :=
  CleanSubbank.bank (s:=lowCount) (ActiveRepairLayoutRecordsPayloadEarlyData.input d x)

theorem bank_set (d : Inputs s p offset rows) (x y : Array s rows) :
    SharedPlacementAlphabet.setTape (bank d x) rawSlot (ActiveTargetRotation.word y) 0=bank d y := by
  rw [bank,rawSlot,CleanSubbank.bank,SharedPlacementAlphabet.setTape_append_left]
  change CleanSubbank.bank (s:=lowCount)
    (SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsPayloadEarlyData.input d x) 228
      (ActiveTargetRotation.word y) 0)=_
  rw [input_set]
  rfl

theorem bank_raw (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d x).tape rawSlot=ActiveTargetRotation.word x := by
  simp only [bank,rawSlot,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
    ActiveRepairLayoutRecordsPayloadEarlyData.input,ActiveRepairLayoutRecordsPayloadEarlyData.native,
    ActiveRepairLayoutRecordsPayloadEarlyData.rawBank]
  rfl

theorem bank_raw_head (d : Inputs s p offset rows) (x : Array s rows) : (bank d x).head rawSlot=0 := by
  simp only [bank,rawSlot,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
    ActiveRepairLayoutRecordsPayloadEarlyData.input,ActiveRepairLayoutRecordsPayloadEarlyData.native,
    ActiveRepairLayoutRecordsPayloadEarlyData.rawBank]
  rfl

theorem bank_output_blank (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d x).tape outputSlot=fun _ => blank := by
  simp only [bank,ActiveRepairLayoutRecordsPayloadEarlyRun.outputSlot,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
    ActiveRepairLayoutRecordsPayloadEarlyData.input,ActiveRepairLayoutRecordsPayloadEarlyData.native]
  rfl

theorem bank_output_head (d : Inputs s p offset rows) (x : Array s rows) : (bank d x).head outputSlot=0 := by
  simp only [bank,ActiveRepairLayoutRecordsPayloadEarlyRun.outputSlot,CleanSubbank.bank,Tapes.append,Fin.addCases_left,
    ActiveRepairLayoutRecordsPayloadEarlyData.input,ActiveRepairLayoutRecordsPayloadEarlyData.native]
  rfl

theorem recycle_result (d : Inputs s p offset rows) (x y : Array s rows) :
    ActiveRepairArrayRecycle.result
      (SharedPlacementAlphabet.setTape (bank d x) outputSlot (ActiveTargetRotation.word y) 0)
      outputSlot rawSlot y=bank d y := by
  rw [←bank_set d x y]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hs : i=outputSlot
  all_goals by_cases hd : i=rawSlot
  all_goals first
    | (subst i; exact (slots_ne hd).elim)
    | simp [WordBankCleanup.write,SharedPlacementAlphabet.setTape,
        Function.update_apply,hs,hd,bank_output_blank,bank_output_head,bank_raw_head,slots_ne,Ne.symm slots_ne]

def recycleProgram := ActiveRepairArrayRecycle.program outputSlot rawSlot slots_ne
  (by change 2≤243+lowCount; omega) prime
def fullProgram := two program recycleProgram
def totalCost (D : ℕ) (s : Shape) (p : Parameters s) (rows : ℕ) :=
  ActivePrefixEarlySequenceOriginalRun.cost s p rows+
    (repairCoefficient D+5)*(rows*s.recordWidth)+12

theorem full_runs (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) (hrows : 0<rows)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime fullProgram (fun v => v=bank d x) (fun v => v=bank d (ideal d x)) (totalCost D s p rows) := by
  have h := runs_linear d x hfit hq3 hrows hR D hdensity
  rw [output_literal d x hfit hq3] at h
  let a := ActivePrefixEarlySequenceData.result s p offset hfit rows x
  have hr := ActiveRepairArrayRecycle.runs
    (SharedPlacementAlphabet.setTape (bank d a) outputSlot (ActiveTargetRotation.word (ideal d x)) 0)
    outputSlot rawSlot slots_ne (by change 2≤243+lowCount; omega)
    a (ideal d x)
    (by simp [SharedPlacementAlphabet.setTape])
    (by simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne (Ne.symm slots_ne)]; exact bank_raw d a)
    (by simp [SharedPlacementAlphabet.setTape])
    (by simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne (Ne.symm slots_ne)]; exact bank_raw_head d a)
  rw [recycle_result] at hr
  apply (two_runs h hr).consequence (fun _ hv => hv) (fun _ hv => hv) _
  unfold cost totalCost ActiveRepairLayoutRecordsHeadersBudget.volume
  simp only [Nat.add_mul]
  omega

theorem bank_heads (d : Inputs s p offset rows) (x y : Array s rows) :
    (bank d x).head=(bank d y).head := by
  rw [←bank_set d x y]
  change (bank d x).head=Function.update (bank d x).head rawSlot 0
  rw [←bank_raw_head d x,Function.update_eq_self]

theorem full_source_head (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d (ideal d x)).head rawSlot=0 := bank_raw_head d _
theorem full_output_head (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d (ideal d x)).head outputSlot=0 := bank_output_head d _
theorem full_output_blank (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d (ideal d x)).tape outputSlot=fun _ => blank := bank_output_blank d _

theorem uniform_bound (D : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (p : Parameters s) (rows : ℕ),
    0<rows → 0<s.payload → (totalCost D s p rows : ℝ)≤
      C*(rows*s.recordWidth : ℕ)*((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixEarlySequenceOriginalBudget.uniform_bound
  refine ⟨C+(repairCoefficient D+5)+12,by positivity,?_⟩
  intro s p rows hr hp
  have hi := hbound s p rows hr hp
  have hv : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have he : (1 : ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(repairCoefficient D+5 : ℕ)+12 by positivity)
  unfold totalCost
  push_cast at hi hv hrest ⊢
  nlinarith only [hi,hv,hrest]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyClean
