import IntegerMultBounds.Machine.ActiveRepairRankFieldsGeometry

/-! Actual original-layout parsing endpoint: V/T/U/full source and selected
source bits are physically extracted from the genuine short record counter.
Record payload width is separate; the address shape has payload one. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsEndpoint
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankFieldsGeometry ActiveRepairRankFieldsBank
open BinaryAddressTableData (row)

def beforeStarts (s : Shape) (w m before after offset : ℕ) : Fin 4 → ℕ :=
  ![targetStart s after,tStart s w m before after,uStart s w m before after,prefixStart s m after+offset]
def afterStarts (s : Shape) (w m before after offset : ℕ) : Fin 4 → ℕ :=
  ![targetStart s after,tStart s w m before after,uStart s w m before after,tailBits s+offset]
def widths (w m sourceWidth : ℕ) : Fin 4 → ℕ := ![m,w,w,sourceWidth]

def beforeFull (s : Shape) (w m before after rows : ℕ) (x : Address s w m before after rows)
    (offset sourceWidth : ℕ) := Gather.field (row before x.activeBefore.val) offset sourceWidth
def afterFull (s : Shape) (w m before after rows : ℕ) (x : Address s w m before after rows)
    (offset sourceWidth : ℕ) := Gather.field (row after x.activeAfter.val) offset sourceWidth

def expected (s : Shape) (w m before after rows : ℕ) (x : Address s w m before after rows)
    (xs : List Bool) (q rho n : ℕ) : Fin 5 → List Bool :=
  ![row m x.target.val,row w x.t.val,row w x.u.val,xs,SelectedSourceBitsData.selected xs q rho n]

variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (hactive : before+m+after=s.active*s.chunk) (hp : s.payload=1)
variable (x : Address s w m before after rows) (cs : List Bool)
variable (hcs : Counter.value cs=(index s w m before after rows hw hactive x).val)

include hcs hp in
theorem finished_before (offset sourceWidth q rho n : ℕ) (hplace : offset+sourceWidth≤before) :
    ActiveRepairRankFieldsRun.finished cs (beforeStarts s w m before after offset) (widths w m sourceWidth) q rho n=
      expected s w m before after rows x (beforeFull s w m before after rows x offset sourceWidth) q rho n := by
  have h0 := target_word s w m before after rows hw hactive hp x cs hcs
  have h1 := t_word s w m before after rows hw hactive hp x cs hcs
  have h2 := u_word s w m before after rows hw hactive hp x cs hcs
  have h3 := before_source s w m before after rows hw hactive hp x cs hcs offset sourceWidth hplace
  funext i
  fin_cases i
  all_goals dsimp [ActiveRepairRankFieldsRun.finished,ActiveRepairRankFieldsRun.outputs,
    ActiveRepairRankFieldsRun.source,beforeStarts,widths,expected,beforeFull,Function.update]
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact congrArg (fun xs => SelectedSourceBitsData.selected xs q rho n) h3

include hcs hp in
theorem finished_after (offset sourceWidth q rho n : ℕ) (hplace : offset+sourceWidth≤after) :
    ActiveRepairRankFieldsRun.finished cs (afterStarts s w m before after offset) (widths w m sourceWidth) q rho n=
      expected s w m before after rows x (afterFull s w m before after rows x offset sourceWidth) q rho n := by
  have h0 := target_word s w m before after rows hw hactive hp x cs hcs
  have h1 := t_word s w m before after rows hw hactive hp x cs hcs
  have h2 := u_word s w m before after rows hw hactive hp x cs hcs
  have h3 := after_source s w m before after rows hw hactive hp x cs hcs offset sourceWidth hplace
  funext i
  fin_cases i
  all_goals dsimp [ActiveRepairRankFieldsRun.finished,ActiveRepairRankFieldsRun.outputs,
    ActiveRepairRankFieldsRun.source,afterStarts,widths,expected,afterFull,Function.update]
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact congrArg (fun xs => SelectedSourceBitsData.selected xs q rho n) h3

include hw hactive in
theorem before_fits (offset sourceWidth : ℕ) (hplace : offset+sourceWidth≤before) :
    ∀ i, beforeStarts s w m before after offset i+widths w m sourceWidth i≤s.bits := by
  intro i
  fin_cases i
  all_goals dsimp [beforeStarts,widths,targetStart,tStart,uStart,prefixStart,tailBits,Shape.bits]
  all_goals omega

include hw hactive in
theorem after_fits (offset sourceWidth : ℕ) (hplace : offset+sourceWidth≤after) :
    ∀ i, afterStarts s w m before after offset i+widths w m sourceWidth i≤s.bits := by
  intro i
  fin_cases i
  all_goals dsimp [afterStarts,widths,targetStart,tStart,uStart,prefixStart,tailBits,Shape.bits]
  all_goals omega

include hcs hp in
theorem runs_before (offset q rho n f : ℕ) (hplace : offset+f*q≤before) (hnf : n+1=f) (hr : rho<q)
    (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool)
    (hv0 : ∀ i, Counter.value (hs (offsetSlot i))=beforeStarts s w m before after offset i)
    (hv1 : ∀ i, Counter.value (hs (widthSlot i))=widths w m (f*q) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i)) :
    HoareTime ActiveRepairRankFieldsRun.program
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs ActiveRepairRankFieldsRun.empty hs ss))
      (fun v => v=CleanSubbank.bank (s := 9)
        (bank cs (expected s w m before after rows x (beforeFull s w m before after rows x offset (f*q)) q rho n) hs ss))
      (1200*(s.bits+1)+4) := by
  have h := ActiveRepairRankFieldsRun.runs_linear cs (beforeStarts s w m before after offset) (widths w m (f*q))
    hs ss hv0 hv1 hc q rho n f s.bits rfl hnf hr sv sc
    (before_fits s w m before after hw hactive offset (f*q) hplace)
  rw [finished_before s w m before after rows hw hactive hp x cs hcs offset (f*q) q rho n hplace] at h
  exact h

include hcs hp in
theorem runs_after (offset q rho n f : ℕ) (hplace : offset+f*q≤after) (hnf : n+1=f) (hr : rho<q)
    (hs : Fin 8 → List Bool) (ss : Fin 4 → List Bool)
    (hv0 : ∀ i, Counter.value (hs (offsetSlot i))=afterStarts s w m before after offset i)
    (hv1 : ∀ i, Counter.value (hs (widthSlot i))=widths w m (f*q) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (sv : ∀ i, Counter.value (ss i)=SelectedSourceBitsRun.values q n rho f i)
    (sc : ∀ i, GrowingCounterData.Canonical (ss i)) :
    HoareTime ActiveRepairRankFieldsRun.program
      (fun v => v=CleanSubbank.bank (s := 9) (bank cs ActiveRepairRankFieldsRun.empty hs ss))
      (fun v => v=CleanSubbank.bank (s := 9)
        (bank cs (expected s w m before after rows x (afterFull s w m before after rows x offset (f*q)) q rho n) hs ss))
      (1200*(s.bits+1)+4) := by
  have h := ActiveRepairRankFieldsRun.runs_linear cs (afterStarts s w m before after offset) (widths w m (f*q))
    hs ss hv0 hv1 hc q rho n f s.bits rfl hnf hr sv sc
    (after_fits s w m before after hw hactive offset (f*q) hplace)
  rw [finished_after s w m before after rows hw hactive hp x cs hcs offset (f*q) q rho n hplace] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsEndpoint
