import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateData

/-! Actual full later low/high execution on the original array: clean repaired
low payload followed by original-header highest-bit action. Every original
numeric word survives, and all independent private banks start and end blank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlConjugationData (Kind)
open ActiveRepairLayoutRecordsFullLateData
open ActiveTargetHighestPairLayoutGeometry (late)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

abbrev lowCount := ActivePrefixDirtyControlSequenceOriginalRun.count
abbrev highCount := ActiveTargetHighestLayoutOriginalData.count
abbrev count := 252+lowCount+highCount
theorem low_le : 252+lowCount≤count := by unfold count; omega
theorem high_le : 252+highCount≤count := by unfold count; omega

def two {t a q r : ℕ} (M : Program t q a) (N : Program t r a) := seq M N
theorem two_runs {t a q r b c : ℕ} {M : Program t q a} {N : Program t r a}
    {P Q R : TapePred t a} (hM : HoareTime M P Q b) (hN : HoareTime N Q R c) :
    HoareTime (two M N) P R (b+c+1) :=
  (hM.seq hN).consequence (fun _ h => h) (fun _ h => h) (by omega)

def lowProgramFor (a b c e : Kind) := SharedBankFamily.padProgram
  (ActiveRepairLayoutRecordsPayloadLateRun.programFor a b c e) low_le
def lowProgram := lowProgramFor .tPure .tNegative .uPure .uNegative
def highProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) := SharedBankFamily.padProgram
  (ActiveTargetHighestLayoutOriginalPlaced.laterProgramFor m focus focus_injective) high_le
def programFor (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  two (lowProgramFor a b c e) (highProgramFor m)
def program := programFor .tPure .tNegative .uPure .uNegative .pure

theorem pair_runs (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    {B C : ℕ} {P Q R : TapePred count prime}
    (hl : HoareTime (lowProgramFor a b c e) P Q B) (hh : HoareTime (highProgramFor m) Q R C) :
    HoareTime (programFor a b c e m) P R (B+C+1) :=
  two_runs (M:=lowProgramFor a b c e) (N:=highProgramFor m) hl hh

theorem pad_high_runs (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (v w : Tapes 252 prime) (B : ℕ)
    (h : HoareTime (ActiveTargetHighestLayoutOriginalPlaced.laterProgramFor m focus focus_injective)
      (fun u => u=CleanSubbank.bank (s:=highCount) v)
      (fun u => u=CleanSubbank.bank (s:=highCount) w) B) :
    HoareTime (highProgramFor m) (fun u => u=SharedBankStageInput.raw v count)
      (fun u => u=SharedBankStageInput.raw w count) B :=
  SharedBankFamily.pad_clean_realizes
    (M:=ActiveTargetHighestLayoutOriginalPlaced.laterProgramFor m focus focus_injective)
    high_le v w B h

def bank (d : Inputs s p offset rows) (x : Array s rows) :=
  SharedBankStageInput.raw (ActiveRepairLayoutRecordsPayloadLateData.caller d x) count

theorem permanent_le : 252≤count := by change 252≤252+lowCount+highCount; omega
def rawSlot : Fin count := Fin.castLE permanent_le (237:Fin 252)
theorem rawSlot_value : rawSlot.val=237 := rfl

theorem raw_array (d : Inputs s p offset rows) (x : Array s rows) :
    (bank d x).tape rawSlot=ActiveTargetRotation.word (a:=prime) x := by
  change (if h : 237<252 then
    (ActiveRepairLayoutRecordsPayloadLateData.caller d x).tape ⟨237,h⟩ else fun _ => blank)=_
  rw [dite_eq_left (by decide)]
  exact ActiveRepairLayoutRecordsPayloadLateData.caller_tape_raw d x

theorem raw_head (d : Inputs s p offset rows) (x : Array s rows) : (bank d x).head rawSlot=0 := by
  change (if h : 237<252 then
    (ActiveRepairLayoutRecordsPayloadLateData.caller d x).head ⟨237,h⟩ else 0)=0
  rw [dite_eq_left (by decide)]
  exact ActiveRepairLayoutRecordsPayloadLateData.caller_head_raw d x


def slots (i : Fin 23) : Fin count := Fin.castLE permanent_le (ActiveRepairLayoutRecordsPayloadLateData.focus i)

theorem slots_injective : Function.Injective slots :=
  (Fin.castLE_injective permanent_le).comp ActiveRepairLayoutRecordsPayloadLateData.focus_injective

theorem bank_payload (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.payload (bank d x) slots=ActiveRepairLayoutRecordsPayloadLatePlaced.common d x :=
  (raw_payload permanent_le (ActiveRepairLayoutRecordsPayloadLateData.caller d x)).trans
    (ActiveRepairLayoutRecordsPayloadLateData.caller_sources d x)

theorem all_private_blank (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.strip (bank d x) slots=SharedBank.empty count prime :=
  raw_private permanent_le (ActiveRepairLayoutRecordsPayloadLateData.caller d x)
    (ActiveRepairLayoutRecordsPayloadLateData.caller_private d x)

def highCost (s : Shape) (p : Parameters s) (offset rows : ℕ) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :=
  ActiveTargetHighestLayoutOriginalRun.laterCost (ActivePrefixLayoutHeadersGeometry.inputs s p offset rows)
    (late s p offset rows hfit hbefore hH hr hp)
def costFor (a b c e : Kind) (D : ℕ) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (hbefore : 1≤p.before) (hH : 1≤s.H) :=
  ActiveRepairLayoutRecordsPayloadLateRun.costFor a b c e hfit hn hb d D+
    highCost s p offset rows hfit hbefore hH d.hr (by have := d.hrecord; omega)+1

def cost (D : ℕ) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (hbefore : 1≤p.before) (hH : 1≤s.H) :=
  costFor .tPure .tNegative .uPure .uNegative D hfit hn hb d hbefore hH

theorem runs_for (a b c e : Kind) (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hactual : ActivePrefixDirtyControlSequenceRun.laterFor a b c e
      (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) x=
        ActiveRepairLayoutRecordsPayloadLateData.actual d x)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime (programFor a b c e .pure) (fun v => v=bank d x) (fun v => v=bank d (result d hfit hbefore hH x))
      (costFor a b c e D hfit hn hb d hbefore hH) := by
  have hl : HoareTime (lowProgramFor a b c e) (fun v => v=bank d x)
      (fun v => v=bank d (ActiveRepairLayoutRecordsPayloadLateData.ideal d x))
      (ActiveRepairLayoutRecordsPayloadLateRun.costFor a b c e hfit hn hb d D) :=
    SharedBankFamily.pad_clean_realizes low_le _ _ _
      (ActiveRepairLayoutRecordsPayloadLateRun.runs_for a b c e hfit hn hb d x hactual hq3 hR D hdensity)
  have hh := ActiveTargetHighestLayoutOriginalGlobal.later_runs
    (ActiveRepairLayoutRecordsPayloadLateData.caller d (ActiveRepairLayoutRecordsPayloadLateData.ideal d x))
    focus focus_injective s p offset rows hfit hbefore hH d.hr d.hrecord d.hs
    (ActiveRepairLayoutRecordsPayloadLateData.ideal d x) (sources d _) d.hv d.hc
  have hm := input_set d (ActiveRepairLayoutRecordsPayloadLateData.ideal d x) (result d hfit hbefore hH x)
  have hh' := hh.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg (CleanSubbank.bank (s:=highCount)) hm)) le_rfl
  have hp : HoareTime (highProgramFor .pure)
      (fun v => v=bank d (ActiveRepairLayoutRecordsPayloadLateData.ideal d x))
      (fun v => v=bank d (result d hfit hbefore hH x))
      (highCost s p offset rows hfit hbefore hH d.hr (by have := d.hrecord; omega)) :=
    pad_high_runs .pure _ _ _ hh'
  exact pair_runs a b c e .pure hl hp

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime program (fun v => v=bank d x) (fun v => v=bank d (result d hfit hbefore hH x))
      (cost D hfit hn hb d hbefore hH) :=
  runs_for .tPure .tNegative .uPure .uNegative d x hfit hn hb
    (ActiveRepairLayoutRecordsPayloadLateRun.actual_result hfit hn hb d x)
    hbefore hH hq3 hR D hdensity

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateRun
