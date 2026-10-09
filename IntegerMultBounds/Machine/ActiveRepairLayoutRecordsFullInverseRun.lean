import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseData

/-! Two actual full low/high executions restore the entire caller and its
blank private bank, with both native runtimes and the sequence join paid. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape setTape_self setTape_setTape)
variable {s : Shape} {p : Parameters s} {offset rows t : ℕ}

def twice {t q a : ℕ} (M : Program t q a) := seq M M

theorem twice_runs {t q a B : ℕ} {M : Program t q a} {P Q R : TapePred t a}
    (hl : HoareTime M P Q B) (hr : HoareTime M Q R B) :
    HoareTime (twice M) P R (2*B+1) :=
  (hl.seq hr).consequence (fun _ h => h) (fun _ h => h) (by omega)

namespace Early
open ActiveRepairLayoutRecordsFullEarlyRun (count)
def programFor (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  twice (ActiveRepairLayoutRecordsFullEarlyPlaced.programFor m focus hf)
def program (focus : Fin 23 → Fin t) (hf : Function.Injective focus) := programFor .pure focus hf

theorem pair_runs (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    {B : ℕ} {P Q R : TapePred (t+count) prime}
    (hl : HoareTime (ActiveRepairLayoutRecordsFullEarlyPlaced.programFor m focus hf) P Q B)
    (hr : HoareTime (ActiveRepairLayoutRecordsFullEarlyPlaced.programFor m focus hf) Q R B) :
    HoareTime (programFor m focus hf) P R (2*B+1) :=
  twice_runs (M:=ActiveRepairLayoutRecordsFullEarlyPlaced.programFor m focus hf) hl hr

theorem restore (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullEarlyPlaced.common d x) :
    setTape v (focus 22) (ActiveTargetRotation.word x) 0=v := by
  have hh : v.head (focus 22)=0 := congrFun (congrArg Tapes.head hsrc) 22
  have ht : v.tape (focus 22)=ActiveTargetRotation.word x := congrFun (congrArg Tapes.tape hsrc) 22
  rw [←hh,←ht,setTape_self]

/-- The same actual stage implements the recursive return action. -/
theorem undo_runs (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullEarlyPlaced.common d x)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H)
    (hoff : 0<offset) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime (ActiveRepairLayoutRecordsFullEarlyPlaced.program focus hf)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22)
        (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH x)) 0))
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (ActiveRepairLayoutRecordsFullEarlyRun.cost D s p offset rows hfit hsource hH d.hr
        (by have := d.hrecord; omega)) := by
  let y := ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH x
  let w := setTape v (focus 22) (ActiveTargetRotation.word y) 0
  have hs : SharedBank.payload w focus=ActiveRepairLayoutRecordsFullEarlyPlaced.common d y := by
    simp only [w,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,
      ActiveRepairLayoutRecordsFullEarlyPlaced.common_set]
  have hr := ActiveRepairLayoutRecordsFullEarlyPlaced.runs d y w focus hf hs hfit hsource hH hq3 hR D hdensity
  have he : setTape w (focus 22)
      (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH y)) 0=v := by
    rw [show ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH y=x from
      ActiveRepairLayoutRecordsFullInverseData.early d x hfit hsource hH hoff]
    simp only [w,setTape_setTape]
    exact restore d x v focus hsrc
  exact hr.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg (CleanSubbank.bank (s:=count)) he)) le_rfl

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullEarlyPlaced.common d x)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H)
    (hoff : 0<offset) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime (program focus hf) (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (2*ActiveRepairLayoutRecordsFullEarlyRun.cost D s p offset rows hfit hsource hH d.hr
        (by have := d.hrecord; omega)+1) := by
  let y := ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH x
  let w := setTape v (focus 22) (ActiveTargetRotation.word y) 0
  have hs : SharedBank.payload w focus=ActiveRepairLayoutRecordsFullEarlyPlaced.common d y := by
    simp only [w,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,
      ActiveRepairLayoutRecordsFullEarlyPlaced.common_set]
  have hl := ActiveRepairLayoutRecordsFullEarlyPlaced.runs d x v focus hf hsrc hfit hsource hH hq3 hR D hdensity
  have hr := ActiveRepairLayoutRecordsFullEarlyPlaced.runs d y w focus hf hs hfit hsource hH hq3 hR D hdensity
  have he : setTape w (focus 22)
      (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH y)) 0=v := by
    rw [show ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH y=x from
      ActiveRepairLayoutRecordsFullInverseData.early d x hfit hsource hH hoff]
    simp only [w,setTape_setTape]
    exact restore d x v focus hsrc
  have hr' := hr.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg (CleanSubbank.bank (s:=count)) he)) le_rfl
  exact pair_runs .pure focus hf hl hr'
end Early

namespace Late
open ActiveRepairLayoutRecordsFullLateRun (count)
def programFor (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  twice (ActiveRepairLayoutRecordsFullLatePlaced.programFor a b c e m focus hf)
def program (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  programFor .tPure .tNegative .uPure .uNegative .pure focus hf

theorem pair_runs (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    {B : ℕ} {P Q R : TapePred (t+count) prime}
    (hl : HoareTime (ActiveRepairLayoutRecordsFullLatePlaced.programFor a b c e m focus hf) P Q B)
    (hr : HoareTime (ActiveRepairLayoutRecordsFullLatePlaced.programFor a b c e m focus hf) Q R B) :
    HoareTime (programFor a b c e m focus hf) P R (2*B+1) :=
  twice_runs (M:=ActiveRepairLayoutRecordsFullLatePlaced.programFor a b c e m focus hf) hl hr

theorem restore (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullLatePlaced.common d x) :
    setTape v (focus 22) (ActiveTargetRotation.word x) 0=v := by
  have hh : v.head (focus 22)=0 := congrFun (congrArg Tapes.head hsrc) 22
  have ht : v.tape (focus 22)=ActiveTargetRotation.word x := congrFun (congrArg Tapes.tape hsrc) 22
  rw [←hh,←ht,setTape_self]

/-- The same actual stage implements the recursive return action. -/
theorem undo_runs (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullLatePlaced.common d x)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime (ActiveRepairLayoutRecordsFullLatePlaced.program focus hf)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22)
        (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x)) 0))
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (ActiveRepairLayoutRecordsFullLateRun.cost D hfit hn hb d hbefore hH) := by
  let y := ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x
  let w := setTape v (focus 22) (ActiveTargetRotation.word y) 0
  have hs : SharedBank.payload w focus=ActiveRepairLayoutRecordsFullLatePlaced.common d y := by
    simp only [w,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,
      ActiveRepairLayoutRecordsFullLatePlaced.common_set]
  have hr := ActiveRepairLayoutRecordsFullLatePlaced.runs d y w focus hf hs hfit hn hb hbefore hH hq3 hR D hdensity
  have he : setTape w (focus 22)
      (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH y)) 0=v := by
    rw [show ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH y=x from
      ActiveRepairLayoutRecordsFullInverseData.late d x hfit hbefore hH]
    simp only [w,setTape_setTape]
    exact restore d x v focus hsrc
  exact hr.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg (CleanSubbank.bank (s:=count)) he)) le_rfl

theorem runs_for (a b c e : Kind) (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullLatePlaced.common d x)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D)
    (hactual : ∀ z : Array s rows,ActivePrefixDirtyControlSequenceRun.laterFor a b c e
      (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) z=
        ActiveRepairLayoutRecordsPayloadLateData.actual d z) :
    HoareTime (programFor a b c e .pure focus hf) (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (2*ActiveRepairLayoutRecordsFullLateRun.costFor a b c e D hfit hn hb d hbefore hH+1) := by
  let y := ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x
  let w := setTape v (focus 22) (ActiveTargetRotation.word y) 0
  have hs : SharedBank.payload w focus=ActiveRepairLayoutRecordsFullLatePlaced.common d y := by
    simp only [w,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,
      ActiveRepairLayoutRecordsFullLatePlaced.common_set]
  have hl := ActiveRepairLayoutRecordsFullLatePlaced.runs_for a b c e d x v focus hf hsrc hfit hn hb
    (hactual x) hbefore hH hq3 hR D hdensity
  have hr := ActiveRepairLayoutRecordsFullLatePlaced.runs_for a b c e d y w focus hf hs hfit hn hb
    (hactual y) hbefore hH hq3 hR D hdensity
  have he : setTape w (focus 22)
      (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH y)) 0=v := by
    rw [show ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH y=x from
      ActiveRepairLayoutRecordsFullInverseData.late d x hfit hbefore hH]
    simp only [w,setTape_setTape]
    exact restore d x v focus hsrc
  have hr' := hr.consequence (fun _ h => h)
    (fun _ h => h.trans (congrArg (CleanSubbank.bank (s:=count)) he)) le_rfl
  exact pair_runs a b c e .pure focus hf hl hr'

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=ActiveRepairLayoutRecordsFullLatePlaced.common d x)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime (program focus hf) (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (2*ActiveRepairLayoutRecordsFullLateRun.cost D hfit hn hb d hbefore hH+1) :=
  runs_for .tPure .tNegative .uPure .uNegative d x v focus hf hsrc hfit hn hb hbefore hH hq3 hR D hdensity
    (ActiveRepairLayoutRecordsPayloadLateRun.actual_result hfit hn hb d)
end Late

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullInverseRun
