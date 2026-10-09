import IntegerMultBounds.Machine.ButterflyInverseAxisRouting

/-! Physical inverse selected-axis execution. Its charged merge reads the two
computed role streams in exchanged order, giving inverse complex butterfly
outputs with exactly the forward tape count, cleanup and linear cost. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisRun
noncomputable section
open ButterflyStreamData ButterflyAxisBank
open ButterflyStreamSemantics (transformed)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (groups rowLength)
variable {v : Descriptor} {N : ℕ}

def mergeProgram := Placement.placed (RecursiveRowsClean.mergeProgram (by decide : 2≤2) ButterflyAxisKernel.swapBit)
  (CleanSubbank.placement (RecursiveRowsRoleBank.ports (c:=2)) mergePorts mergePorts_injective)
def program := seq (seq ButterflyAxisRun.splitProgram ButterflyAxisRun.scanProgram) mergeProgram

theorem merge_runs (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) (bs ls : List Bool) :
    HoareTime mergeProgram (fun z => z=bank (outputStreams xs) (fun _ => blank) bs ls hs)
      (fun z => z=bank blankStreams (word (ButterflyInverseAxisRouting.swapped xs)) bs ls hs)
      (RecursiveRowsClean.bound 2 (volume 2 v)) := by
  apply CleanSubbank.realizes (c:=9) (s:=LocalTapes) (k:=63)
    (RecursiveRowsClean.mergeProgram (by decide : 2≤2) ButterflyAxisKernel.swapBit) (RecursiveRowsRoleBank.ports (c:=2)) mergePorts
    RecursiveRowsRoleBank.ports_injective mergePorts_injective
    (common (outputStreams xs) (fun _ => blank) bs ls hs) (common blankStreams (word (ButterflyInverseAxisRouting.swapped xs)) bs ls hs)
    (RecursiveRowsClean.bank hs (ButterflyAxisRouting.rolePayload xs))
    (RecursiveRowsClean.bank hs (ButterflyAxisRouting.sourcePayload (ButterflyInverseAxisRouting.swapped xs))) _
  · rw [RecursiveRowsRoleBank.local_payload,merge_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · rw [RecursiveRowsRoleBank.local_payload,merge_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · exact RecursiveRowsRoleBank.local_clean _ _
  · exact RecursiveRowsRoleBank.local_clean _ _
  · exact merge_frame _ _ _ _ bs ls hs rfl rfl
  · exact ButterflyInverseAxisRouting.merges hs hv hp hd xs w hw hB

/-- Uniform finite-machine execution of one selected-axis butterfly, including
literal splitting/merging, arithmetic, counters, source erasure and rewinds. -/
theorem runs (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) (bs ls : List Bool)
    (hn : 0<groups 2 v*N) (hb : Counter.value bs=groups 2 v*N)
    (hl : Counter.value ls=ButterflyStreamCleanData.streamLength (groups 2 v*N) w)
    (hbc : GrowingCounterData.Canonical bs) (hlc : GrowingCounterData.Canonical ls) :
    HoareTime program (fun z => z=bank blankStreams (word xs) bs ls hs)
      (fun z => z=bank blankStreams (word (ButterflyInverseAxisRouting.transformed xs)) bs ls hs)
      (2*RecursiveRowsClean.bound 2 (volume 2 v)+400*volume 2 v+2) := by
  have h0 := ButterflyAxisRun.split_runs hs hv hp hd xs w hw hB bs ls
  have h1 := ButterflyAxisRun.scan_runs xs w hw bs ls hs hn hb hl hbc hlc
  have h2 := merge_runs hs hv hp hd (transformed xs) w
    (ButterflyStreamSemantics.transformed_width xs w hw) hB bs ls
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
    (by rw [ButterflyAxisRouting.volume_eq hd w hB]; omega)

/-- One uniform constant covers both native routing passes and all arithmetic.
It is independent of axis, shape, coefficient width and runtime stream length. -/
abbrev constant := ButterflyAxisRun.constant

theorem runs_linear (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) (bs ls : List Bool)
    (hb : Counter.value bs=groups 2 v*N)
    (hl : Counter.value ls=ButterflyStreamCleanData.streamLength (groups 2 v*N) w)
    (hbc : GrowingCounterData.Canonical bs) (hlc : GrowingCounterData.Canonical ls) :
    HoareTime program (fun z => z=bank blankStreams (word xs) bs ls hs)
      (fun z => z=bank blankStreams (word (ButterflyInverseAxisRouting.transformed xs)) bs ls hs)
      (constant*volume 2 v) :=
  (runs hs hv hp hd xs w hw hB bs ls (ButterflyAxisRun.paired_pos hp hd w hB) hb hl hbc hlc).consequence
    (fun _ h => h) (fun _ h => h) (ButterflyAxisRun.bound_linear _ (ButterflyAxisRun.volume_pos hp))

end
end IntegerMultBounds.Machine.ButterflyInverseAxisRun
