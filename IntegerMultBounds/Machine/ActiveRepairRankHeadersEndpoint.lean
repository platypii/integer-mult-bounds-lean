import IntegerMultBounds.Machine.ActiveRepairRankHeadersRun
import IntegerMultBounds.Machine.ActiveRepairRankFieldsEndpoint
import IntegerMultBounds.Machine.ActiveRepairDestinationPatchEndpoint

/-! Original active-layout widths physically generate the exact parser and
patch descriptors. No target/T/U start or completed destination is an input. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankHeadersEndpoint
noncomputable section
open CompactGadgetReservationShape
open ActiveRepairRankHeadersCommands ActiveRepairRankHeadersData
variable {a : ℕ}

def geometry (s : Shape) (w m before after offset width rho : ℕ) : Widths :=
  ⟨s.H,s.B,s.F,before,after,m,w,offset,width,s.bits+rho⟩

def sourceFits (side : SourceSide) (before after offset width : ℕ) :=
  offset+width≤match side with | .before => before | .after => after

theorem geometry_bounded (side : SourceSide) (s : Shape) (w m before after offset width rho : ℕ)
    (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk) (hf : sourceFits side before after offset width) :
    ∀ i, originalValues (geometry s w m before after offset width rho) i≤s.bits+rho := by
  intro i
  cases side <;> fin_cases i
  all_goals dsimp [originalValues,geometry,sourceFits,Shape.bits] at *
  all_goals omega

theorem patch_values (s : Shape) (w m before after offset width rho : ℕ) (hw : w≤s.H) :
    patchValues (geometry s w m before after offset width rho)=
      ActiveRepairDestinationPatchEndpoint.headerValues s w m before after rho := by
  funext i
  fin_cases i
  all_goals dsimp [patchValues,geometry,ActiveRepairDestinationPatchEndpoint.headerValues,
    targetStart,prefixStart,tStart,uStart,ActiveRepairRankFieldsGeometry.targetStart,
    ActiveRepairRankFieldsGeometry.prefixStart,ActiveRepairRankFieldsGeometry.tStart,
    ActiveRepairRankFieldsGeometry.uStart,ActiveRepairRankFieldsGeometry.tailBits]
  all_goals omega

theorem parser_before_values (s : Shape) (w m before after offset width rho : ℕ) (hw : w≤s.H) :
    ∀ i, parserValues .before (geometry s w m before after offset width rho)
        (ActiveRepairRankFieldsBank.offsetSlot i)=ActiveRepairRankFieldsEndpoint.beforeStarts s w m before after offset i ∧
      parserValues .before (geometry s w m before after offset width rho)
        (ActiveRepairRankFieldsBank.widthSlot i)=ActiveRepairRankFieldsEndpoint.widths w m width i := by
  intro i
  fin_cases i
  all_goals dsimp [parserValues,geometry,ActiveRepairRankFieldsBank.offsetSlot,ActiveRepairRankFieldsBank.widthSlot,
    ActiveRepairRankFieldsEndpoint.beforeStarts,ActiveRepairRankFieldsEndpoint.widths,
    targetStart,prefixStart,tStart,uStart,sourceStart,ActiveRepairRankFieldsGeometry.targetStart,
    ActiveRepairRankFieldsGeometry.prefixStart,ActiveRepairRankFieldsGeometry.tStart,
    ActiveRepairRankFieldsGeometry.uStart,ActiveRepairRankFieldsGeometry.tailBits]
  all_goals constructor <;> omega

theorem parser_after_values (s : Shape) (w m before after offset width rho : ℕ) (hw : w≤s.H) :
    ∀ i, parserValues .after (geometry s w m before after offset width rho)
        (ActiveRepairRankFieldsBank.offsetSlot i)=ActiveRepairRankFieldsEndpoint.afterStarts s w m before after offset i ∧
      parserValues .after (geometry s w m before after offset width rho)
        (ActiveRepairRankFieldsBank.widthSlot i)=ActiveRepairRankFieldsEndpoint.widths w m width i := by
  intro i
  fin_cases i
  all_goals dsimp [parserValues,geometry,ActiveRepairRankFieldsBank.offsetSlot,ActiveRepairRankFieldsBank.widthSlot,
    ActiveRepairRankFieldsEndpoint.afterStarts,ActiveRepairRankFieldsEndpoint.widths,
    targetStart,prefixStart,tStart,uStart,sourceStart,ActiveRepairRankFieldsGeometry.targetStart,
    ActiveRepairRankFieldsGeometry.prefixStart,ActiveRepairRankFieldsGeometry.tStart,
    ActiveRepairRankFieldsGeometry.uStart,ActiveRepairRankFieldsGeometry.tailBits]
  all_goals constructor <;> omega

def parserSlot (i : Fin 8) : Fin 43 := ⟨10+i.val,by omega⟩
def patchSlot (i : Fin 7) : Fin 43 := ⟨18+i.val,by omega⟩

theorem parser_headers (side : SourceSide) (d : Widths) :
    ∀ i, (bank (a := a) (finished side d)).tape (parserSlot i)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (parserValues side d i)) ∧
      (bank (a := a) (finished side d)).head (parserSlot i)=1 := by
  intro i
  fin_cases i <;> constructor <;> rfl

theorem patch_headers (side : SourceSide) (d : Widths) :
    ∀ i, (bank (a := a) (finished side d)).tape (patchSlot i)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (patchValues d i)) ∧
      (bank (a := a) (finished side d)).head (patchSlot i)=1 := by
  intro i
  fin_cases i <;> constructor <;> rfl

def originalSlot (i : Fin 10) : Fin 43 := Fin.castAdd 33 i
def temporarySlot (i : Fin 3) : Fin 43 := ⟨25+i.val,by omega⟩

theorem originals_retained (side : SourceSide) (d : Widths) (hs : Fin 10 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, (bank (a := a) (finished side d)).tape (originalSlot i)=RadixZeroFill.encodedBinary (hs i) ∧
      (bank (a := a) (finished side d)).head (originalSlot i)=1 := by
  intro i
  have he := CompactGadgetReservationHeadersCore.canonical_bits (hs i) (originalValues d i) (hc i) (hv i)
  rw [he]
  fin_cases i <;> constructor <;> rfl

theorem temporaries_blank (side : SourceSide) (d : Widths) :
    ∀ i, (bank (a := a) (finished side d)).tape (temporarySlot i)=(fun _ => blank) ∧
      (bank (a := a) (finished side d)).head (temporarySlot i)=0 := by
  intro i
  fin_cases i <;> constructor <;> rfl

theorem workspace_blank (side : SourceSide) (d : Widths) :
    ∀ i : Fin 15, (bank (a := a) (finished side d)).tape (Fin.natAdd 28 i)=(fun _ => blank) ∧
      (bank (a := a) (finished side d)).head (Fin.natAdd 28 i)=0 := by
  intro i
  fin_cases i <;> constructor <;> rfl

 theorem produces (side : SourceSide) (s : Shape) (w m before after offset width rho : ℕ)
    (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk) (hf : sourceFits side before after offset width)
    (hs : Fin 10 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues (geometry s w m before after offset width rho) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (ActiveRepairRankHeadersRun.program (a := a) side)
      (fun x => x=ActiveRepairRankHeadersRun.input hs)
      (fun x => x=bank (finished side (geometry s w m before after offset width rho)))
      (constant*(s.bits+rho+1)) :=
  ActiveRepairRankHeadersRun.produces side _ hw hs hv hc
    (geometry_bounded side s w m before after offset width rho hw ha hf)

 theorem cleans (side : SourceSide) (s : Shape) (w m before after offset width rho : ℕ)
    (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk) (hf : sourceFits side before after offset width)
    (hs : Fin 10 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues (geometry s w m before after offset width rho) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (ActiveRepairRankHeadersRun.cleanupProgram (a := a))
      (fun x => x=bank (finished side (geometry s w m before after offset width rho)))
      (fun x => x=ActiveRepairRankHeadersRun.input hs)
      (ActiveRepairRankHeadersRun.cleanupConstant*(s.bits+rho+1)) :=
  ActiveRepairRankHeadersRun.cleans side _ hs hv hc
    (geometry_bounded side s w m before after offset width rho hw ha hf)

end
end IntegerMultBounds.Machine.ActiveRepairRankHeadersEndpoint
