import IntegerMultBounds.Machine.CompactGadgetReservationShape
import IntegerMultBounds.Machine.RoundedRowDescriptor
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! A subtraction/product-only recipe for the exact compact load headers.
Zero slack is allowed; canonical zero exponents represent complete unit ranges. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersData
open CompactGadgetReservationShape
open CompactGadgetReservationCapacity

def roundFront (s : Shape) := RoundedRowDescriptor.rounded (2*s.H) s.chunk
def roundBack (s : Shape) := RoundedRowDescriptor.rounded s.H s.chunk
def gapExponent (s : Shape) (n : ℕ) : Front → ℕ
  | .temp => roundFront s-s.width n
  | .control => (roundFront s-s.H)-s.width n
def suffixExponent (s : Shape) (n : ℕ) := roundBack s-s.width n

theorem roundFront_eq (s : Shape) (hH : 0 < s.H) (hK : 0 < s.chunk) :
    roundFront s = 2*s.H+s.F := by
  have h := front_exact s.axes s.guard s.chunk hK
  rw [roundFront,RoundedRowDescriptor.rounded_eq_ceiling _ _ (by omega) hK]
  simpa only [Shape.H,Shape.F,frontChunks,chunks,Nat.mul_comm] using h.symm

theorem roundBack_eq (s : Shape) (hH : 0 < s.H) (hK : 0 < s.chunk) :
    roundBack s = s.H+s.B := by
  have h := back_exact s.axes s.guard s.chunk hK
  rw [roundBack,RoundedRowDescriptor.rounded_eq_ceiling _ _ hH hK]
  simpa only [Shape.H,Shape.B,backChunks,chunks,Nat.mul_comm] using h.symm

theorem gap_exponent (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    gapExponent s n f+s.active*s.chunk = s.gapBits n f := by
  have hw := s.carved_le n hn
  cases f <;> simp only [gapExponent,Shape.gapBits,roundFront_eq s hH hK] <;> omega

theorem suffix_exponent (s : Shape) (n : ℕ) (hn : n ≤ s.axes)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    suffixExponent s n = s.afterBits n := by
  have hw := s.carved_le n hn
  rw [suffixExponent,roundBack_eq s hH hK]
  unfold Shape.afterBits
  omega

theorem gap_range (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    2^(gapExponent s n f)*2^(s.active*s.chunk) = s.gap n f := by
  rw [← pow_add,gap_exponent s n hn f hH hK]
  rfl

theorem suffix_range (s : Shape) (n : ℕ) (hn : n ≤ s.axes)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    2^(suffixExponent s n)*s.payload = s.suffix n := by
  rw [suffix_exponent s n hn hH hK]
  rfl

end IntegerMultBounds.Machine.CompactGadgetReservationHeadersData
