import IntegerMultBounds.Machine.CompactReservedOriginal
import IntegerMultBounds.Machine.NativeZeroPaddingArray
import IntegerMultBounds.Machine.CompactGlobalReservation

/-! Original binary row axes are reserved before global row reinterpretation
and genuine native zero padding. Afterwards rows are arbitrary outer ranges:
role division changes row multiplicity, never immutable address dimension. -/
namespace IntegerMultBounds.Machine.CompactReservationNativeRows
noncomputable section
open CompactGlobalRowPadding
open CompactFallbackHeaders (bits polynomials reservation)
open CompactFallbackAxisRun (Array Width)

def shape (c m d D G K : ℕ) := CompactGlobalReservation.shape c m d D G K 1

theorem cardinality (c m d D G K ell : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    originalRows c m d K*2^(shape c m d D G K).bits*2^ell=2^(D*K)*2^ell := by
  have he := CompactGlobalReservation.original_bits c m d D G K 1 hK hD
  unfold originalRows
  rw [←pow_add]
  exact congrArg (fun n => 2^n*2^ell) he

/-- This is a cardinality reinterpretation of the original exact native word,
with no copying or address permutation. Reservation has already executed. -/
def rowView (c m d D G K ell : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : Array D K ell)
    (i : Fin (originalRows c m d K*2^(shape c m d D G K).bits*2^ell)) :=
  f (Fin.cast (cardinality c m d D G K ell hK hD) i)

theorem word_rowView (c m d D G K ell : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : Array D K ell) :
    NativeZeroPaddingArray.word (rowView c m d D G K ell hK hD f)=NativeZeroPaddingArray.word f := by
  have hh := List.ofFn_congr (cardinality c m d D G K ell hK hD)
    (fun i => ButterflyStreamData.encoded (rowView c m d D G K ell hK hD f i))
  have he := congrArg List.flatten hh
  apply he.trans
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  unfold rowView
  apply congrArg (fun j => ButterflyStreamData.encoded (f j))
  exact Fin.ext rfl

def width (D K q : ℕ) := ButterflyGuard.width (reservation D K q) (bits D K)

theorem row_width (c m d D G K ell q : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : Array D K ell) (hw : Width D K ell q f) :
    ∀ i,(rowView c m d D G K ell hK hD f i).1.length=width D K q ∧
      (rowView c m d D G K ell hK hD f i).2.length=width D K q := fun _ => hw _

/-- The complete original reservation result becomes the input to one global
native padding call. Padding produces exactly the initialRows representation,
with real signed zeros and the same immutable address bits. -/
theorem pad_reserved (inverse : Bool) (c m d D G K rho ell q : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : Array D K ell) :
    let g := CompactReservedOriginal.result inverse c m D K rho ell q d G f
    HoareTime NativeZeroPaddingPlaced.program
      (fun v => v=NativeZeroPaddingPlaced.bank
        (NativeZeroPaddingHeaders.initial (originalRows c m d K) (initialRows c m d K)
          (shape c m d D G K).bits ell (width D K q)) (NativeZeroPaddingArray.word g))
      (fun v => v=NativeZeroPaddingPlaced.bank
        (NativeZeroPaddingHeaders.initial (originalRows c m d K) (initialRows c m d K)
          (shape c m d D G K).bits ell (width D K q))
        (NativeZeroPaddingArray.word (NativeZeroPaddingArray.padded (originalRows c m d K) (initialRows c m d K)
          (shape c m d D G K).bits ell (width D K q) (initial_bounds c m d K hc hK).1
          (rowView c m d D G K ell hK hD g))))
      (NativeZeroPaddingPlaced.cost (originalRows c m d K) (initialRows c m d K)
        (shape c m d D G K).bits ell (width D K q) (NativeZeroPaddingArray.word g)) := by
  dsimp only
  have hh := NativeZeroPaddingArray.runs (originalRows c m d K) (initialRows c m d K)
    (shape c m d D G K).bits ell (width D K q) (initial_bounds c m d K hc hK).1
    (rowView c m d D G K ell hK hD (CompactReservedOriginal.result inverse c m D K rho ell q d G f))
  rwa [word_rowView] at hh

/-- The original role divisor is consumed only after padding. Descendants keep
all compact, slack and active address fields and every polynomial coefficient. -/
theorem descendant_count (c m d D G K ell j : ℕ) (hc : 0<c) (hK : 0<K) (hj : j<depth m d) :
    rowsAt c m d K (j+1)*2^(shape c m d D G K).bits*2^ell*c=
      rowsAt c m d K j*2^(shape c m d D G K).bits*2^ell := by
  have hh := role_volume c m d K j (2^(shape c m d D G K).bits*2^ell) hc hK hj
  simpa only [Nat.mul_assoc] using hh

end
end IntegerMultBounds.Machine.CompactReservationNativeRows
