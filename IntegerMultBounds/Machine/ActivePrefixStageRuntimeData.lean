import IntegerMultBounds.Machine.ActivePrefixStageRuntimePlaced

/-! Runtime width and source order select among three finite implementations.
Only the non-singleton execution needs the packed-repair hypotheses. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs descriptors)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

structure Packed (d : Inputs s) (D : ℕ) : Prop where
  guard : 2≤s.guard
  chunk : s.guard+3≤s.chunk
  earlyRecord : (ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1≤s.payload
  lateRecord : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1≤s.payload
  earlyDensity : VaryingControlRepairDensity.earlyDensity s.chunk s.guard (d.stage.f-1)*
    ((ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits+1)≤D
  lateDensity : VaryingControlRepairDensity.lateDensity s.chunk s.guard (d.stage.f-1)*
    ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits+1)≤D

abbrev singleton (d : Inputs s) (h : ¬1<d.stage.f) : ActivePrefixStageSingletonData.Inputs s :=
  ⟨d,by have := d.stage.positiveWidth; omega⟩

def result (d : Inputs s) (x : Array s d.rows) :=
  if h : 1<d.stage.f then ActivePrefixStageDispatchData.result d x
  else ActivePrefixStageSingletonDispatch.result (singleton d h) x

def cost (D : ℕ) (d : Inputs s) (hp : 1<d.stage.f → Packed d D) :=
  ActivePrefixStageWidthSelector.cost (RecursiveChildQuotientsConstant.bits d.stage.f)+
  (if h : 1<d.stage.f then ActivePrefixStageDispatchRun.cost D d (by omega) (hp h).guard
  else ActivePrefixStageSingletonDispatch.cost (singleton d h))+4

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeData
