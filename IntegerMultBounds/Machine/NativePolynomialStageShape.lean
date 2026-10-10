import IntegerMultBounds.Machine.ActivePrefixStageNativePolynomial
import IntegerMultBounds.Machine.CompactSpectatorLeafSetup

/-! A native polynomial row is encoded as three bits per native symbol by the
physical stage converters. Its stage payload descriptor is therefore three
times the entire serialized polynomial row, rather than the reservation's
single coordinate payload. Address geometry and original role rows are retained. -/
namespace IntegerMultBounds.Machine.NativePolynomialStageShape
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageNativePolynomial (symbols)

def width (s : Shape) (p : ℕ) := ButterflyGuard.width p s.bits

def payload (s : Shape) (ell p : ℕ) := symbols (2^ell) (width s p)*3

def shape (s : Shape) (ell p : ℕ) : Shape := { s with payload := payload s ell p }

def stage {s : Shape} (v : Stage s) (ell p : ℕ) : Stage (shape s ell p) where
  slots := v.slots
  f := v.f
  left := v.left
  right := v.right
  rho := v.rho
  source := v.source
  target := v.target
  distinct := v.distinct
  activeAxes := v.activeAxes
  positiveWidth := v.positiveWidth
  widthFits := v.widthFits
  selectedFits := v.selectedFits

theorem bits (s : Shape) (ell p : ℕ) : (shape s ell p).bits=s.bits := rfl

theorem payload_fits (s : Shape) (ell p : ℕ) : s.bits+1≤payload s ell p := by
  have hR : 1≤2^ell := Nat.one_le_pow _ _ (by decide)
  unfold payload symbols width ButterflyGuard.width ButterflyGuard.halfWidth
  nlinarith

def inputs {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) :
    ActivePrefixStageFullData.Inputs (shape s ell p) where
  stage := stage v ell p
  rows := rows
  hG := hG
  hGK := hGK
  hr := hr
  hrecord := payload_fits s ell p

theorem code (s : Shape) (ell p : ℕ) :
    (shape s ell p).payload=symbols (2^ell) (width s p)*3+0 := rfl

theorem original_values {s : Shape} (v : Stage s) (rows ell p : ℕ) (i : Fin 13) :
    ActivePrefixStageHeadersData.originalValues (stage v ell p) rows i=
      if i=5 then payload s ell p else ActivePrefixStageHeadersData.originalValues v rows i := by
  fin_cases i <;> rfl

/-- Expanding the codec payload does not change the original address count. -/
theorem count {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) :
    ActivePrefixStageTripleWords.count (inputs v rows ell p hG hGK hr)=rows*2^s.bits := by
  simp only [ActivePrefixStageTripleWords.count,ActiveRepairLayoutRecordsShape.address_width]
  rfl

theorem volume (s : Shape) (rows ell p : ℕ) :
    rows*(shape s ell p).recordWidth=
      3*(rows*2^s.bits*symbols (2^ell) (width s p)) := by
  unfold Shape.recordWidth
  rw [bits]
  change rows*(2^s.bits*(symbols (2^ell) (width s p)*3))=_
  ring

end
end IntegerMultBounds.Machine.NativePolynomialStageShape
