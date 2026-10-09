import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyData

/-! Actual full early low/high execution on one original array: clean repaired
low payload followed by original-header highest-bit action, with all private
storage blank and every original descriptor/head retained. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveRepairLayoutRecordsFullEarlyData
open ActiveTargetHighestPairLayoutGeometry (sourceHigh early)
open ActiveRepairLayoutRecordsPayloadEarlyRun (two two_runs)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

abbrev lowCount := ActiveRepairLayoutRecordsPayloadEarlyRun.lowCount
abbrev highCount := ActiveTargetHighestLayoutOriginalData.count
abbrev count := 243+lowCount+highCount
theorem low_le : 243+lowCount≤count := by unfold count; omega
theorem high_le : 243+highCount≤count := by unfold count; omega

def lowProgram := SharedBankFamily.padProgram ActiveRepairLayoutRecordsPayloadEarlyClean.fullProgram low_le
def highProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) := SharedBankFamily.padProgram
  (ActiveTargetHighestLayoutOriginalPlaced.earlierProgramFor m focus focus_injective) high_le
def programFor (m : ActivePrefixDirtyControlLoadProducer.Mode) := two lowProgram (highProgramFor m)
def program := programFor .pure

def bank (d : Inputs s p offset rows) (x : Array s rows) :=
  SharedBankStageInput.raw (ActiveRepairLayoutRecordsPayloadEarlyData.input d x) count

theorem permanent_le : 243≤count := by change 243≤243+lowCount+highCount; omega
def rawSlot : Fin count := Fin.castLE permanent_le (228 : Fin 243)
theorem rawSlot_value : rawSlot.val=228 := rfl

theorem raw_array (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d x).tape rawSlot=ActiveTargetRotation.word (a:=prime) x := by
  change (if h : 228<243 then
    (ActiveRepairLayoutRecordsPayloadEarlyData.input d x).tape ⟨228,h⟩ else fun _ => blank)=_
  rw [dite_eq_left (by decide)]
  rfl

theorem raw_head (d : Inputs s p offset rows) (x : Array s rows) : (bank d x).head rawSlot=0 := by
  change (if h : 228<243 then
    (ActiveRepairLayoutRecordsPayloadEarlyData.input d x).head ⟨228,h⟩ else 0)=0
  rw [dite_eq_left (by decide)]
  rfl

def highCost (s : Shape) (p : Parameters s) (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :=
  ActiveTargetHighestLayoutOriginalRun.earlierCost (ActivePrefixLayoutHeadersGeometry.inputs s p offset rows)
    (early s p offset rows hfit hsource hH hr hp)
def cost (D : ℕ) (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H)
    (hr : 0<rows) (hp : 0<s.payload) :=
  ActiveRepairLayoutRecordsPayloadEarlyClean.totalCost D s p rows+
    highCost s p offset rows hfit hsource hH hr hp+1

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H)
    (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=bank d x) (fun v => v=bank d (result d hfit hsource hH x))
      (cost D s p offset rows hfit hsource hH d.hr (by have := d.hrecord; omega)) := by
  have hl := SharedBankFamily.pad_clean_realizes low_le _ _ _
    (ActiveRepairLayoutRecordsPayloadEarlyClean.full_runs d x hfit hq3 d.hr hR D hdensity)
  have hh := ActiveTargetHighestLayoutOriginalGlobal.earlier_runs
    (ActiveRepairLayoutRecordsPayloadEarlyData.input d (ActiveRepairLayoutRecordsPayloadEarlyClean.ideal d x))
    focus focus_injective s p offset rows hfit hsource hH d.hr d.hrecord d.hs
    (ActiveRepairLayoutRecordsPayloadEarlyClean.ideal d x) (sources d _) d.hv d.hc
  rw [input_set] at hh
  have hp := SharedBankFamily.pad_clean_realizes high_le _ _ _ hh
  exact two_runs (M:=lowProgram) (N:=highProgramFor .pure) hl hp

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyRun
