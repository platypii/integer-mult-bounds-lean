import IntegerMultBounds.Machine.CompactGadgetReservationCapacity
import IntegerMultBounds.Machine.RadixRangePadding

/-! Literal suffix geometry of the existing compact reservations. Temp/control
front fields and their shared dirty back field retain every unused address bit. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationShape
open CompactGadgetReservationCapacity

structure Shape where
  axes : ℕ
  guard : ℕ
  chunk : ℕ
  active : ℕ
  payload : ℕ

inductive Front where
  | temp
  | control
  deriving DecidableEq

inductive Slot where
  | temp
  | control
  | back
  deriving DecidableEq

namespace Shape

def H (s : Shape) := capacity s.axes s.guard
def F (s : Shape) := frontSlack s.axes s.guard s.chunk
def B (s : Shape) := backSlack s.axes s.guard s.chunk
def bits (s : Shape) := 2*s.H+s.F+s.active*s.chunk+s.H+s.B
def recordWidth (s : Shape) := 2^s.bits*s.payload
def width (s : Shape) (n : ℕ) := n*s.guard
def prefixBits (s : Shape) : Front → ℕ
  | .temp => 0
  | .control => s.H
def gapBits (s : Shape) (n : ℕ) : Front → ℕ
  | .temp => (s.H-s.width n)+s.H+s.F+s.active*s.chunk
  | .control => (s.H-s.width n)+s.F+s.active*s.chunk
def afterBits (s : Shape) (n : ℕ) := (s.H-s.width n)+s.B
def prefixRange (s : Shape) (rows : ℕ) (f : Front) := rows*2^(s.prefixBits f)
def gap (s : Shape) (n : ℕ) (f : Front) := 2^(s.gapBits n f)
def suffix (s : Shape) (n : ℕ) := 2^(s.afterBits n)*s.payload

def slotStart (s : Shape) : Slot → ℕ
  | .temp => 0
  | .control => s.H
  | .back => 2*s.H+s.F+s.active*s.chunk

theorem existing_bits (s : Shape) (hK : 0 < s.chunk) :
    s.bits = (frontChunks s.axes s.guard s.chunk+s.active+
      backChunks s.axes s.guard s.chunk)*s.chunk := by
  have hf := front_exact s.axes s.guard s.chunk hK
  have hb := back_exact s.axes s.guard s.chunk hK
  change 2*s.H+s.F = frontChunks s.axes s.guard s.chunk*s.chunk at hf
  change s.H+s.B = backChunks s.axes s.guard s.chunk*s.chunk at hb
  unfold bits
  nlinarith

theorem carved_le (s : Shape) (n : ℕ) (hn : n ≤ s.axes) : s.width n ≤ s.H :=
  carved n s.axes s.guard hn

theorem slot_fits (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (t : Slot) :
    s.slotStart t+s.width n ≤ s.bits := by
  have hw := s.carved_le n hn
  cases t <;> simp only [slotStart,bits] <;> omega

/-- The carved temp, control and back intervals are distinct existing bits. -/
theorem slots_disjoint (s : Shape) (n : ℕ) (hn : n ≤ s.axes)
    (u v : Slot) (huv : u ≠ v) (i j : Fin (s.width n)) :
    s.slotStart u+i.val ≠ s.slotStart v+j.val := by
  have hw := s.carved_le n hn
  have hi := i.isLt
  have hj := j.isLt
  cases u <;> cases v
  all_goals first | exact (huv rfl).elim | (simp only [slotStart]; omega)

/-- This decomposition only reinterprets consecutive existing bits. -/
theorem bits_decomposition (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front) :
    s.prefixBits f+s.width n+s.gapBits n f+s.width n+s.afterBits n = s.bits := by
  have hw := carved_le s n hn
  cases f <;> simp only [prefixBits,gapBits,afterBits,bits] <;> omega

/-- Exact volume equality used to feed the actual field-swap/rotation machine;
both dirty compact fields and every slack/payload coordinate are included. -/
theorem rectangle_volume (s : Shape) (n rows : ℕ) (hn : n ≤ s.axes) (f : Front) :
    RadixRangePadding.volume (s.prefixRange rows f) (2^(s.width n))
      (s.gap n f) (s.suffix n) = rows*s.recordWidth := by
  have he := bits_decomposition s n hn f
  unfold RadixRangePadding.volume prefixRange gap suffix recordWidth
  calc
    _ = rows*(2^(s.prefixBits f+s.width n+s.gapBits n f+s.width n+s.afterBits n)*s.payload) := by
      simp only [pow_add]
      ring
    _ = _ := by rw [he]

theorem gap_pos (s : Shape) (n : ℕ) (f : Front) : 0 < s.gap n f := by
  unfold gap
  positivity

theorem suffix_pos (s : Shape) (n : ℕ) (hp : 0 < s.payload) : 0 < s.suffix n := by
  unfold suffix
  positivity

theorem prefix_pos (s : Shape) (rows : ℕ) (f : Front) (hr : 0 < rows) :
    0 < s.prefixRange rows f := by
  unfold prefixRange
  positivity

end Shape
end IntegerMultBounds.Machine.CompactGadgetReservationShape
