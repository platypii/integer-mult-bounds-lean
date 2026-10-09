import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelinePrepareCount
import IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelineRun

/-! Literal source stream plus original metadata prepares all scan sentinels,
the unary pass width, and an actual zero rank counter. No sentinel/counter is
an input. The counter width is the original geometric addressBits. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelinePrepare
noncomputable section
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
open ActiveRepairEarlyOriginalPipelinePrepareCount
open SharedPlacementAlphabet (setTape setTape_append_left)

def source (rs : List Partition.Record) := RepairScan.srcTape rs
def initial (d : Data) (rs : List Partition.Record) : Tapes 189 1 :=
  (CountedRepairScanSeed.input (source rs)).append (ActiveRepairLateOriginalScan.scratch d)
def seeded (d : Data) (rs : List Partition.Record) : Tapes 189 1 :=
  (CountedRepairScanSeed.output (source rs)).append (ActiveRepairLateOriginalScan.scratch d)
def selectorFilled (d : Data) (rs : List Partition.Record) :=
  setTape (seeded d rs) 7 (KeySelect.selector d.geom.addressBits) d.geom.addressBits
def selectorReady (d : Data) (rs : List Partition.Record) :=
  setTape (seeded d rs) 7 (KeySelect.selector d.geom.addressBits) 0
def counterFilled (d : Data) (rs : List Partition.Record) :=
  setTape (selectorReady d rs) 13 (RepairScan.ctrTape (List.replicate d.geom.addressBits false))
    (1+d.geom.addressBits)

def selectorFocus : Fin 2 → Fin 189 := ![7,54]
def counterFocus : Fin 2 → Fin 189 := ![13,54]
theorem selector_injective : Function.Injective selectorFocus := by decide
theorem counter_injective : Function.Injective counterFocus := by decide
def seedProgram := extend CountedRepairScanSeed.program 178
def selectorProgram := fill true selectorFocus selector_injective
def selectorBack := back selectorFocus selector_injective
def counterProgram := fill false counterFocus counter_injective
def counterBack := back counterFocus counter_injective
def program := seq (seq (seq (seq seedProgram selectorProgram) selectorBack) counterProgram) counterBack

def input (d : Data) (rs : List Partition.Record) := CleanSubbank.bank (s := 3) (initial d rs)
def output (d : Data) (rs : List Partition.Record) :=
  (ActiveRepairLateOriginalPipelineRun.input d d.geom.addressBits rs).append (SharedBank.empty 3 1)

theorem seed_runs (d : Data) (rs : List Partition.Record) :
    HoareTime seedProgram (fun v => v=input d rs)
      (fun v => v=CleanSubbank.bank (s := 3) (seeded d rs)) 2 := by
  have h := hoare_extend_eq (CountedRepairScanSeed.runs (source rs))
    ((ActiveRepairLateOriginalScan.scratch d).append (SharedBank.empty 3 1))
  have hi : (CountedRepairScanSeed.input (source rs)).append
      ((ActiveRepairLateOriginalScan.scratch d).append (SharedBank.empty 3 1))=input d rs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have ho : (CountedRepairScanSeed.output (source rs)).append
      ((ActiveRepairLateOriginalScan.scratch d).append (SharedBank.empty 3 1))=
        CleanSubbank.bank (s := 3) (seeded d rs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hi,ho] at h
  exact h

theorem width_value (d : Data) (h : Valid d) : Counter.value (d.originals 9)=d.geom.addressBits := h.hv 9

theorem selector_runs (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime selectorProgram (fun v => v=CleanSubbank.bank (s := 3) (seeded d rs))
      (fun v => v=CleanSubbank.bank (s := 3) (selectorFilled d rs))
      (7*d.geom.addressBits+7*(d.originals 9).length+23) := by
  have hp : SharedBank.payload (seeded d rs) selectorFocus=
      sources (KeySelect.selector 0) 0 (d.originals 9) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := fills true (seeded d rs) selectorFocus selector_injective (KeySelect.selector 0)
    0 (d.originals 9) d.geom.addressBits hp (width_value d h)
  have he := CountedRepairScanPrepare.selector_filled d.geom.addressBits
  change putWord (KeySelect.selector 0) 0 (List.replicate d.geom.addressBits (bitSymbol true))=
    KeySelect.selector d.geom.addressBits at he
  rw [he] at hh
  simpa only [selectorProgram,selectorFilled,show selectorFocus 0=7 from rfl,zero_add] using hh

theorem selector_back (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime selectorBack (fun v => v=CleanSubbank.bank (s := 3) (selectorFilled d rs))
      (fun v => v=CleanSubbank.bank (s := 3) (selectorReady d rs))
      (7*d.geom.addressBits+7*(d.originals 9).length+23) := by
  have hp : SharedBank.payload (selectorFilled d rs) selectorFocus=
      sources (KeySelect.selector d.geom.addressBits) d.geom.addressBits (d.originals 9) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := returns (selectorFilled d rs) selectorFocus selector_injective
    (KeySelect.selector d.geom.addressBits) d.geom.addressBits (d.originals 9) d.geom.addressBits hp (width_value d h)
  have he : setTape (selectorFilled d rs) (selectorFocus 0) (KeySelect.selector d.geom.addressBits)
      ((d.geom.addressBits : ℤ)-d.geom.addressBits)=selectorReady d rs := by
    simp [selectorFilled,selectorReady,selectorFocus,setTape]
  rw [he] at hh
  exact hh

theorem counter_runs (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime counterProgram (fun v => v=CleanSubbank.bank (s := 3) (selectorReady d rs))
      (fun v => v=CleanSubbank.bank (s := 3) (counterFilled d rs))
      (7*d.geom.addressBits+7*(d.originals 9).length+23) := by
  have hp : SharedBank.payload (selectorReady d rs) counterFocus=
      sources (RepairScan.ctrTape []) 1 (d.originals 9) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := fills false (selectorReady d rs) counterFocus counter_injective (RepairScan.ctrTape [])
    1 (d.originals 9) d.geom.addressBits hp (width_value d h)
  have he := CountedRepairScanPrepare.ctr_filled d.geom.addressBits
  change putWord (RepairScan.ctrTape []) 1 (List.replicate d.geom.addressBits (bitSymbol false))=
    RepairScan.ctrTape (List.replicate d.geom.addressBits false) at he
  rw [he] at hh
  simpa only [counterProgram,counterFilled,show counterFocus 0=13 from rfl] using hh

theorem counter_back (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime counterBack (fun v => v=CleanSubbank.bank (s := 3) (counterFilled d rs))
      (fun v => v=output d rs) (7*d.geom.addressBits+7*(d.originals 9).length+23) := by
  have hp : SharedBank.payload (counterFilled d rs) counterFocus=
      sources (RepairScan.ctrTape (List.replicate d.geom.addressBits false))
        (1+d.geom.addressBits) (d.originals 9) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := returns (counterFilled d rs) counterFocus counter_injective
    (RepairScan.ctrTape (List.replicate d.geom.addressBits false))
    (1+d.geom.addressBits) (d.originals 9) d.geom.addressBits hp (width_value d h)
  have he : CleanSubbank.bank (s := 3)
      (setTape (counterFilled d rs) (counterFocus 0)
        (RepairScan.ctrTape (List.replicate d.geom.addressBits false))
        (1+d.geom.addressBits-d.geom.addressBits))=output d rs := by
    simp only [add_sub_cancel_right]
    have he14 : setTape (setTape (CountedRepairScanSeed.output (source rs)) 7
        (KeySelect.selector d.geom.addressBits) 0) 13
        (RepairScan.ctrTape (List.replicate d.geom.addressBits false)) 1=
      RepairScan.scanBank d.geom.addressBits rs
        (ActiveRepairLateOriginalScan.flag d d.geom.addressBits)
        (ActiveRepairLateOriginalScan.bits d d.geom.addressBits) d.geom.addressBits 0 [] 0 := by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    have he189 : setTape (counterFilled d rs) (counterFocus 0)
        (RepairScan.ctrTape (List.replicate d.geom.addressBits false)) 1=
        ActiveRepairLateOriginalPipelineRun.input d d.geom.addressBits rs := by
      unfold counterFilled selectorReady seeded
      change setTape (setTape (setTape
        ((CountedRepairScanSeed.output (source rs)).append (ActiveRepairLateOriginalScan.scratch d))
        (Fin.castAdd 175 (7 : Fin 14)) _ 0) (Fin.castAdd 175 (13 : Fin 14)) _ _)
        (Fin.castAdd 175 (13 : Fin 14)) _ 1=_
      rw [setTape_append_left,setTape_append_left,setTape_append_left]
      have heReset : setTape (setTape (setTape (CountedRepairScanSeed.output (source rs)) 7
          (KeySelect.selector d.geom.addressBits) 0) 13
          (RepairScan.ctrTape (List.replicate d.geom.addressBits false)) (1+d.geom.addressBits))
          13 (RepairScan.ctrTape (List.replicate d.geom.addressBits false)) 1=
        setTape (setTape (CountedRepairScanSeed.output (source rs)) 7
          (KeySelect.selector d.geom.addressBits) 0) 13
          (RepairScan.ctrTape (List.replicate d.geom.addressBits false)) 1 := by
        simp [setTape]
      rw [heReset,he14]
      rfl
    rw [he189]
    rfl
  rw [he] at hh
  exact hh

theorem runs_linear (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime program (fun v => v=input d rs) (fun v => v=output d rs)
      (200*(d.geom.addressBits+1)) := by
  have hl := GrowingCounterData.canonical_width (d.originals 9) (h.hc 9)
  rw [width_value d h] at hl
  have hg := Nat.log2_le_self d.geom.addressBits
  exact (((((seed_runs d rs).seq (selector_runs d h rs)).seq (selector_back d h rs)).seq
    (counter_runs d h rs)).seq (counter_back d h rs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelinePrepare
