import IntegerMultBounds.Machine.SparsePhaseHeadersData
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced
import IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
import IntegerMultBounds.Machine.FlatCoordinateDimensions

/-! Paid stage metadata lifecycle for the polynomial phase caller. Original
thirteen headers produce all computed geometry; an immutable caller ordinal
is physically copied only after stage synthesis has released its scratch.
Final metadata/ordinal erasure restores exactly the original numeric bank.
Native coefficient streams and outer controller storage can be framed by
placing/extending these actual header machines. -/
namespace IntegerMultBounds.Machine.UnitPhaseStageHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order initial finished)
open ActivePrefixStageHeadersSchedule (Ordered)
open ActiveRepairRankHeadersCommands (bank)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {a : ℕ}

def axisBank (axis : ℕ) : Tapes 1 a :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (bits axis)⟩
def input (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  (bank (a := a) (initial v rows)).append (axisBank axis.val)
def prepared (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  (bank (a := a) (finished order v rows)).append (axisBank axis.val)
def ready (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  (bank (a := a) (SparsePhaseHeadersData.initial order v rows axis)).append (axisBank axis.val)

def focus : Fin 2 → Fin 44 := ![43,25]
theorem injective : Function.Injective focus := by decide
def setup (order : Order) := seq (extend (ActivePrefixStageHeadersRun.program (a := a) order) 1)
  (BinaryDescriptorCopyPlaced.program focus injective)

theorem setup_runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (hG : 1≤s.guard) (horder : Ordered order v) :
    HoareTime (setup (a := a) order) (fun z => z=input v rows axis)
      (fun z => z=ready order v rows axis)
      (ActivePrefixStageHeadersRun.cost order v rows+2*(bits axis.val).length+6) := by
  have h0 := hoare_extend_eq (ActivePrefixStageHeadersRun.runs (a := a) order v rows hG horder) (axisBank axis.val)
  have h1 := BinaryDescriptorCopyPlaced.copies (prepared (a := a) order v rows axis) focus injective
    (bits axis.val) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  have he : setTape (prepared (a := a) order v rows axis) (focus 1)
      (RadixZeroFill.encodedBinary (bits axis.val)) 1=ready order v rows axis := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

def eraseSchedule : List ActivePrefixStageHeadersOps.Op :=
  [.command (.erase 13),.command (.erase 14),.command (.erase 15),.command (.erase 16),
    .command (.erase 17),.command (.erase 18),.command (.erase 19),.command (.erase 20),
    .command (.erase 21),.command (.erase 25)]
def cleanup := (ActivePrefixStageHeadersOps.compile (a := a) eraseSchedule).2

theorem cleanup_runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    HoareTime (cleanup (a := a))
      (fun z => z=bank (SparsePhaseHeadersData.initial order v rows axis))
      (fun z => z=bank (initial v rows))
      (ActivePrefixStageHeadersOps.scheduleCost eraseSchedule (SparsePhaseHeadersData.initial order v rows axis)) := by
  have hv : ActivePrefixStageHeadersOps.validSchedule eraseSchedule
      (SparsePhaseHeadersData.initial order v rows axis) := by
    simp [eraseSchedule,ActivePrefixStageHeadersOps.validSchedule,ActivePrefixStageHeadersOps.valid,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
      ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
      SparsePhaseHeadersData.initial,finished,Function.update]
  have he : ActivePrefixStageHeadersOps.execute eraseSchedule
      (SparsePhaseHeadersData.initial order v rows axis)=initial v rows := by
    funext i; fin_cases i
    all_goals simp [eraseSchedule,ActivePrefixStageHeadersOps.execute,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
      SparsePhaseHeadersData.initial,initial,finished,Function.update]
  have h := ActivePrefixStageHeadersOps.schedule_runs (a := a) eraseSchedule _ hv
  rw [he] at h
  exact h

private theorem cleanup_bound (order : Order) (v : Stage s) (rows A : ℕ) (axis : Fin v.f)
    (hv : ∀ i,ActivePrefixStageHeadersData.outputs order v i≤A) (ha : axis.val≤A) :
    ActivePrefixStageHeadersOps.scheduleCost eraseSchedule (SparsePhaseHeadersData.initial order v rows axis)≤
      1000*(A+1)+10 := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  have h8 := hv 8
  change s.H≤A at h0
  change s.B≤A at h1
  change s.F≤A at h2
  change ActivePrefixStageParameters.before v≤A at h3
  change ActivePrefixStageParameters.after v≤A at h4
  change (v.f-1)*s.chunk≤A at h5
  change (v.f-1)*s.guard≤A at h6
  change v.f-1≤A at h7
  change ActivePrefixStageHeadersData.offset order v≤A at h8
  simp [eraseSchedule,ActivePrefixStageHeadersOps.scheduleCost,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    SparsePhaseHeadersData.initial,finished,ActivePrefixStageHeadersData.outputs,Function.update]
  omega

/-- Stage synthesis and physical ordinal copying have linear full-volume cost. -/
theorem setup_linear (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (ho : Ordered order v)
    (hr : 0<rows) (hrecord : s.bits+1≤s.payload) :
    ActivePrefixStageHeadersRun.cost order v rows+2*(bits axis.val).length+6≤800010*(rows*s.recordWidth) := by
  obtain ⟨hvalues,houtputs⟩ := ActivePrefixStageHeadersBudget.original_bounds order v rows hG hGK ho hr hrecord
  have hcost := ActivePrefixStageHeadersBudget.arithmetic_bound order v rows (rows*s.recordWidth) hG hvalues houtputs
  have ha : axis.val≤rows*s.recordWidth := by
    have h := houtputs 7
    change v.f-1≤rows*s.recordWidth at h
    have := axis.isLt
    omega
  have hp : 0<rows*s.recordWidth := by
    have hpay : 0<s.payload := by omega
    unfold Shape.recordWidth
    positivity
  have hbits := FlatCoordinateDimensions.bits_length_le_twice ha hp
  have hbits' : (bits axis.val).length≤2*(rows*s.recordWidth) := by
    simpa only [RecursiveChildQuotientsConstant.bits_eq_advance,FlatCoordinateSchedule.bits] using hbits
  omega

/-- All computed geometry and the copied ordinal are physically erased at
linear full-volume cost, including the erasure sequencing transitions. -/
theorem cleanup_linear (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (ho : Ordered order v)
    (hr : 0<rows) (hrecord : s.bits+1≤s.payload) :
    ActivePrefixStageHeadersOps.scheduleCost eraseSchedule (SparsePhaseHeadersData.initial order v rows axis)≤
      2010*(rows*s.recordWidth) := by
  have hv := (ActivePrefixStageHeadersBudget.original_bounds order v rows hG hGK ho hr hrecord).2
  have ha : axis.val≤rows*s.recordWidth := by
    have h := hv 7
    change v.f-1≤rows*s.recordWidth at h
    have := axis.isLt
    omega
  have hp : 0<rows*s.recordWidth := by
    have hpay : 0<s.payload := by omega
    unfold Shape.recordWidth
    positivity
  have h := cleanup_bound order v rows (rows*s.recordWidth) axis hv ha
  omega

end
end IntegerMultBounds.Machine.UnitPhaseStageHeaders
