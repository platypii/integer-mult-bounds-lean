import IntegerMultBounds.Machine.CompactGadgetReservationHeadersBudget

/-! Arbitrary carved width in one unchanged global reservation. Every unused
front/back bit, the active axis bits, and all slack/payload bits remain present. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedData
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersData
open CompactGadgetReservationData (rowCount)

def gapBits (s : Shape) (w : ℕ) : Front → ℕ
  | .temp => (s.H-w)+s.H+s.F+s.active*s.chunk
  | .control => (s.H-w)+s.F+s.active*s.chunk
def afterBits (s : Shape) (w : ℕ) := (s.H-w)+s.B
def gap (s : Shape) (w : ℕ) (f : Front) := 2^(gapBits s w f)
def suffix (s : Shape) (w : ℕ) := 2^(afterBits s w)*s.payload
def gapExponent (s : Shape) (w : ℕ) : Front → ℕ
  | .temp => roundFront s-w
  | .control => (roundFront s-s.H)-w
def suffixExponent (s : Shape) (w : ℕ) := roundBack s-w

theorem gap_exponent (s : Shape) (w : ℕ) (hw : w ≤ s.H) (f : Front)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    gapExponent s w f+s.active*s.chunk = gapBits s w f := by
  cases f <;> simp only [gapExponent,gapBits,roundFront_eq s hH hK] <;> omega

theorem suffix_exponent (s : Shape) (w : ℕ) (hw : w ≤ s.H)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    suffixExponent s w = afterBits s w := by
  rw [suffixExponent,roundBack_eq s hH hK]
  unfold afterBits
  omega

theorem gap_range (s : Shape) (w : ℕ) (hw : w ≤ s.H) (f : Front)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    2^(gapExponent s w f)*2^(s.active*s.chunk) = gap s w f := by
  rw [← pow_add,gap_exponent s w hw f hH hK]
  rfl

theorem suffix_range (s : Shape) (w : ℕ) (hw : w ≤ s.H)
    (hH : 0 < s.H) (hK : 0 < s.chunk) :
    2^(suffixExponent s w)*s.payload = suffix s w := by
  rw [suffix_exponent s w hw hH hK]
  rfl

theorem bits_decomposition (s : Shape) (w : ℕ) (hw : w ≤ s.H) (f : Front) :
    s.prefixBits f+w+gapBits s w f+w+afterBits s w = s.bits := by
  cases f <;> simp only [Shape.prefixBits,gapBits,afterBits,Shape.bits] <;> omega

theorem rectangle_volume (s : Shape) (w rows : ℕ) (hw : w ≤ s.H) (f : Front) :
    RadixRangePadding.volume (s.prefixRange rows f) (2^w) (gap s w f) (suffix s w) =
      rows*s.recordWidth := by
  have he := bits_decomposition s w hw f
  unfold RadixRangePadding.volume Shape.prefixRange gap suffix Shape.recordWidth
  calc
    _ = rows*(2^(s.prefixBits f+w+gapBits s w f+w+afterBits s w)*s.payload) := by
      simp only [pow_add]
      ring
    _ = _ := by rw [he]

theorem gap_pos (s : Shape) (w : ℕ) (f : Front) : 0 < gap s w f := by unfold gap; positivity
theorem suffix_pos (s : Shape) (w : ℕ) (hp : 0 < s.payload) : 0 < suffix s w := by unfold suffix; positivity

theorem slot_fits (s : Shape) (w : ℕ) (hw : w ≤ s.H) (t : Slot) :
    s.slotStart t+w ≤ s.bits := by cases t <;> simp only [Shape.slotStart,Shape.bits] <;> omega

theorem slots_disjoint (s : Shape) (w : ℕ) (hw : w ≤ s.H) (u v : Slot)
    (huv : u ≠ v) (i j : Fin w) : s.slotStart u+i.val ≠ s.slotStart v+j.val := by
  have hi := i.isLt
  have hj := j.isLt
  cases u <;> cases v
  all_goals first | exact (huv rfl).elim | (simp only [Shape.slotStart]; omega)

theorem packed_width_le (s : Shape) (n b : ℕ) (hn : n ≤ s.axes) (hb : b ≤ s.guard) :
    n*b ≤ s.H := by
  change n*b ≤ s.axes*s.guard
  exact Nat.mul_le_mul hn hb

theorem two_packed_widths (s : Shape) (n b q : ℕ) (hn : n ≤ s.axes)
    (hb : b ≤ s.guard) (hq : q ≤ s.guard) : n*b ≤ s.H ∧ n*q ≤ s.H :=
  ⟨packed_width_le s n b hn hb,packed_width_le s n q hn hq⟩

theorem slots_disjoint_mixed (s : Shape) (w₁ w₂ : ℕ) (hw₁ : w₁ ≤ s.H) (hw₂ : w₂ ≤ s.H)
    (u v : Slot) (huv : u ≠ v) (i : Fin w₁) (j : Fin w₂) :
    s.slotStart u+i.val ≠ s.slotStart v+j.val := by
  have hi := i.isLt
  have hj := j.isLt
  cases u <;> cases v
  all_goals first | exact (huv rfl).elim | (simp only [Shape.slotStart]; omega)

def rectangle {a c r : ℕ} (s : Shape) (w : ℕ) (hw : w ≤ s.H) (f : Front) (hc : 0 < c)
    (x : Fin (1*r*s.recordWidth) → Bool) (j : Fin c) :
    Fin (RadixRangePadding.volume (s.prefixRange (rowCount r c) f) (2^w) (gap s w f) (suffix s w)) → Bool :=
  fun i => CompactGadgetReservationData.roleBits (a := a) hc x j
    (Fin.cast ((rectangle_volume s w (rowCount r c) hw f).trans CompactGadgetReservationData.role_size.symm) i)

theorem role_tape {a c r : ℕ} (s : Shape) (w : ℕ) (hw : w ≤ s.H) (f : Front) (hc : 0 < c)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool) (j : Fin c) :
    (CompactRowReservationEndpoint.final (a := a) hc x rs ls).head (CompactGadgetReservationData.roleSlot c j) = 0 ∧
    (CompactRowReservationEndpoint.final (a := a) hc x rs ls).tape (CompactGadgetReservationData.roleSlot c j) =
      BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (rectangle (a := a) s w hw f hc x j i)) := by
  have h := CompactRowReservationEndpoint.role_word (a := a) hc x rs ls j
  refine ⟨h.1,h.2.trans ?_⟩
  unfold RecursiveRowsConstruct.word BinaryRadixRangePrepareAlphabet.word
  apply congrArg (putWord (fun _ => blank) 0)
  rw [List.ofFn_congr ((rectangle_volume s w (rowCount r c) hw f).trans
    (CompactGadgetReservationData.role_size (a := a)).symm).symm]
  apply congrArg List.ofFn
  funext i
  exact CompactGadgetReservationData.role_symbols hc x j _

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedData
