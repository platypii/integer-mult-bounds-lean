import IntegerMultBounds.Machine.ButterflyAxisBank

/-! One actual selected-axis machine: clean native-symbol split, all paired
coefficient arithmetic, paid normalization, and destructive merge. Every
private bank is blank at both boundaries, and the sole common stream contains
the exact transformed records. Original count and shape headers are retained. -/
namespace IntegerMultBounds.Machine.ButterflyAxisRun
noncomputable section
open ButterflyStreamData ButterflyAxisBank
open ButterflyStreamSemantics (transformed)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeRows (groups rowLength)
variable {v : Descriptor} {N : ℕ}

def splitProgram := Placement.placed (RecursiveRowsClean.splitProgram (by decide : 2≤2) (c:=2))
  (CleanSubbank.placement (RecursiveRowsRoleBank.ports (c:=2)) splitPorts splitPorts_injective)
def mergeProgram := Placement.placed (RecursiveRowsClean.mergeProgram (by decide : 2≤2) (Equiv.refl (Fin 2)))
  (CleanSubbank.placement (RecursiveRowsRoleBank.ports (c:=2)) mergePorts mergePorts_injective)
def scanProgram := extend (extend ButterflyStreamClean.program 7) LocalTapes
def program := seq (seq splitProgram scanProgram) mergeProgram

theorem split_runs (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) (bs ls : List Bool) :
    HoareTime splitProgram (fun z => z=bank blankStreams (word xs) bs ls hs)
      (fun z => z=bank (inputStreams xs) (fun _ => blank) bs ls hs)
      (RecursiveRowsClean.bound 2 (volume 2 v)) := by
  apply CleanSubbank.realizes (c:=9) (s:=LocalTapes) (k:=63)
    (RecursiveRowsClean.splitProgram (by decide : 2≤2) (c:=2)) (RecursiveRowsRoleBank.ports (c:=2)) splitPorts
    RecursiveRowsRoleBank.ports_injective splitPorts_injective
    (common blankStreams (word xs) bs ls hs) (common (inputStreams xs) (fun _ => blank) bs ls hs)
    (RecursiveRowsClean.bank hs (ButterflyAxisRouting.sourcePayload xs))
    (RecursiveRowsClean.bank hs (ButterflyAxisRouting.rolePayload xs)) _
  · rw [RecursiveRowsRoleBank.local_payload,split_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · rw [RecursiveRowsRoleBank.local_payload,split_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · exact RecursiveRowsRoleBank.local_clean _ _
  · exact RecursiveRowsRoleBank.local_clean _ _
  · exact split_frame _ _ _ _ bs ls hs rfl rfl
  · exact ButterflyAxisRouting.splits hs hv hp hd xs w hw hB

theorem merge_runs (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) (bs ls : List Bool) :
    HoareTime mergeProgram (fun z => z=bank (outputStreams xs) (fun _ => blank) bs ls hs)
      (fun z => z=bank blankStreams (word xs) bs ls hs)
      (RecursiveRowsClean.bound 2 (volume 2 v)) := by
  apply CleanSubbank.realizes (c:=9) (s:=LocalTapes) (k:=63)
    (RecursiveRowsClean.mergeProgram (by decide : 2≤2) (Equiv.refl (Fin 2))) (RecursiveRowsRoleBank.ports (c:=2)) mergePorts
    RecursiveRowsRoleBank.ports_injective mergePorts_injective
    (common (outputStreams xs) (fun _ => blank) bs ls hs) (common blankStreams (word xs) bs ls hs)
    (RecursiveRowsClean.bank hs (ButterflyAxisRouting.rolePayload xs))
    (RecursiveRowsClean.bank hs (ButterflyAxisRouting.sourcePayload xs)) _
  · rw [RecursiveRowsRoleBank.local_payload,merge_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · rw [RecursiveRowsRoleBank.local_payload,merge_payload]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · exact RecursiveRowsRoleBank.local_clean _ _
  · exact RecursiveRowsRoleBank.local_clean _ _
  · exact merge_frame _ _ _ _ bs ls hs rfl rfl
  · exact ButterflyAxisRouting.merges hs hv hp hd xs w hw hB

theorem scan_runs (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) (hn : 0<groups 2 v*N)
    (hb : Counter.value bs=groups 2 v*N)
    (hl : Counter.value ls=ButterflyStreamCleanData.streamLength (groups 2 v*N) w)
    (hbc : GrowingCounterData.Canonical bs) (hlc : GrowingCounterData.Canonical ls) :
    HoareTime scanProgram (fun z => z=bank (inputStreams xs) (fun _ => blank) bs ls hs)
      (fun z => z=bank (outputStreams (transformed xs)) (fun _ => blank) bs ls hs)
      (400*(4*(groups 2 v*N)*(w+1))) := by
  have hi : ButterflyStreamCleanData.input (ButterflyAxisSerialization.paired xs 0)
      (ButterflyAxisSerialization.paired xs 1)=data (inputStreams xs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using (Fin.addCases (m:=4) (n:=48)) with
    | left i => fin_cases i <;> rfl
    | right i => simp
  have ho : ButterflyStreamCleanData.output (ButterflyAxisSerialization.paired xs 0)
      (ButterflyAxisSerialization.paired xs 1)=data (outputStreams (transformed xs)) := by
    rfl
  have hh := ButterflyStreamClean.runs_linear (ButterflyAxisSerialization.paired xs 0)
    (ButterflyAxisSerialization.paired xs 1) w
    (fun i => hw _ 0 _) (fun i => hw _ 1 _) bs ls hn hb hl hbc hlc
  rw [hi,ho] at hh
  exact hoare_extend_eq (hoare_extend_eq hh
    ((CountedLoopReuseAlphabet.one (fun _ => blank) 0).append (RecursiveRowsRoleBank.headers hs)))
    (SharedBank.empty LocalTapes 2)

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
      (fun z => z=bank blankStreams (word (transformed xs)) bs ls hs)
      (2*RecursiveRowsClean.bound 2 (volume 2 v)+400*volume 2 v+2) := by
  have h0 := split_runs hs hv hp hd xs w hw hB bs ls
  have h1 := scan_runs xs w hw bs ls hs hn hb hl hbc hlc
  have h2 := merge_runs hs hv hp hd (transformed xs) w
    (ButterflyStreamSemantics.transformed_width xs w hw) hB bs ls
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
    (by rw [ButterflyAxisRouting.volume_eq hd w hB]; omega)

/-- One uniform constant covers both native routing passes and all arithmetic.
It is independent of axis, shape, coefficient width and runtime stream length. -/
def constant := 2*((2+5*RecursiveRowsMove.TapeCount 2)*(RecursiveRowsQuotient.constant 2+1099)+
  11*RecursiveRowsMove.TapeCount 2+4)+402

theorem bound_linear (V : ℕ) (hV : 0<V) :
    2*RecursiveRowsClean.bound 2 V+400*V+2 ≤ constant*V := by
  have hh := RecursiveRowsClean.bound_linear 2 V hV
  unfold constant
  nlinarith

theorem volume_pos (hp : v.Positive) : 0<volume 2 v := by
  rcases hp with ⟨ha,hr,hb,hc,hd⟩
  unfold volume
  positivity

theorem paired_pos (hp : v.Positive) (hd : 2 ∣ v.rows) (w : ℕ)
    (hB : rowLength 2 v=N*(2*(w+1))) : 0<groups 2 v*N := by
  have hh := volume_pos hp
  rw [ButterflyAxisRouting.volume_eq hd w hB] at hh
  by_contra hn
  have he : groups 2 v*N=0 := by omega
  rw [he] at hh
  simp at hh

theorem runs_linear (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : 2 ∣ v.rows)
    (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h j k,(xs h j k).1.length=w ∧ (xs h j k).2.length=w)
    (hB : rowLength 2 v=N*(2*(w+1))) (bs ls : List Bool)
    (hb : Counter.value bs=groups 2 v*N)
    (hl : Counter.value ls=ButterflyStreamCleanData.streamLength (groups 2 v*N) w)
    (hbc : GrowingCounterData.Canonical bs) (hlc : GrowingCounterData.Canonical ls) :
    HoareTime program (fun z => z=bank blankStreams (word xs) bs ls hs)
      (fun z => z=bank blankStreams (word (transformed xs)) bs ls hs)
      (constant*volume 2 v) :=
  (runs hs hv hp hd xs w hw hB bs ls (paired_pos hp hd w hB) hb hl hbc hlc).consequence
    (fun _ h => h) (fun _ h => h) (bound_linear _ (volume_pos hp))

end
end IntegerMultBounds.Machine.ButterflyAxisRun
