import IntegerMultBounds.Machine.ActivePrefixStageHeadersPlaced
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs

/-! Physically generated separate descriptor words are the exact caller words
accepted by the existing complete early and later stages. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData
open ActivePrefixStageHeadersPlaced
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ} {s : Shape}

def values (order : Order) (v : Stage s) (rows : ℕ) : Fin 22 → ℕ :=
  ![s.chunk,s.axes,s.guard,v.f-1,s.active,rows,s.payload,s.guard,
    s.H,s.B,s.F,before v,after v,(v.f-1)*s.chunk,(v.f-1)*s.guard,
    s.chunk,s.guard,v.f-1,v.rho,offset order v,rows,s.payload]
def words (order : Order) (v : Stage s) (rows : ℕ) (i : Fin 22) := bits (values order v rows i)

theorem numeric (order : Order) (v : Stage s) (rows : ℕ) (i : Fin 22) :
    finished order v rows (consumerSlots i)=some (values order v rows i) := by
  fin_cases i <;> rfl

theorem consumer (order : Order) (v : Stage s) (rows : ℕ) :
    SharedBank.payload (ActivePrefixStageHeadersRouting.caller (a := a) (finished order v rows)) consumerSlots=
      FixedHeaderBankCopy.headerBank (words order v rows) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals dsimp only [SharedBank.payload,ActivePrefixStageHeadersRouting.caller,FixedHeaderBankCopy.headerBank,words]
  all_goals rw [numeric]
  all_goals rfl

def inputs (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk)
    (hrows : 0<rows) (hrecord : s.bits+1≤s.payload) :
    ActivePrefixEarlySequenceOriginalInputs.Inputs s (parameters v hG hGK) (offset order v) rows where
  gs := fun i => bits (CompactGadgetReservationHeadersCarvedSchedule.originalValues s (v.f-1) rows i)
  bw := bits s.guard
  hs := fun i => bits (ActivePrefixLayoutHeadersData.originalValues
    (ActivePrefixLayoutHeadersGeometry.inputs s (parameters v hG hGK) (offset order v) rows) i)
  gv := fun _ => RecursiveChildQuotientsConstant.bits_value _
  gc := fun _ => RecursiveChildQuotientsConstant.bits_canonical _
  gb := RecursiveChildQuotientsConstant.bits_value _
  cb := RecursiveChildQuotientsConstant.bits_canonical _
  hv := fun _ => RecursiveChildQuotientsConstant.bits_value _
  hc := fun _ => RecursiveChildQuotientsConstant.bits_canonical _
  hr := hrows
  hK := by have := v.selectedFits; omega
  hd := positive_axes v
  hg := hG
  hrecord := hrecord

theorem consumer_inputs (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard)
    (hGK : s.guard+1≤s.chunk) (hrows : 0<rows) (hrecord : s.bits+1≤s.payload) :
    SharedBank.payload (ActivePrefixStageHeadersRouting.caller (a := a) (finished order v rows)) consumerSlots=
      ((FixedHeaderBankCopy.headerBank (inputs order v rows hG hGK hrows hrecord).gs).append
        (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => (inputs order v rows hG hGK hrows hrecord).bw))).append
          (FixedHeaderBankCopy.headerBank (inputs order v rows hG hGK hrows hrecord).hs) := by
  rw [consumer]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem originals (order : Order) (v : Stage s) (rows : ℕ) (i : Fin 13) :
    finished order v rows (Fin.castAdd 52 i)=some (originalValues v rows i) := by
  simp [ActivePrefixStageHeadersPlaced.finished,i.isLt]

theorem erased (order : Order) (v : Stage s) (rows : ℕ) (i : Fin 65)
    (hl : 13 ≤ i.val) (hh : i.val<43) : finished order v rows i=none := by
  simp [ActivePrefixStageHeadersPlaced.finished,show ¬i.val<13 by omega,show ¬ 43 ≤ i.val by omega]

end
end IntegerMultBounds.Machine.ActivePrefixStageHeadersEndpoint
