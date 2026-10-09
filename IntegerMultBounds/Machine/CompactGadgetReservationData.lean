import IntegerMultBounds.Machine.CompactGadgetReservationShape
import IntegerMultBounds.Machine.CompactRowReservationEndpoint

/-! The physically produced role word is the concrete temp/control/back
rectangle. The conversion below changes types, never tape cells or their order. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationData
noncomputable section
open CompactGadgetReservationShape
open CompactRowHeaders (descriptor)
open IntegerMultBounds.Compact.Layout (paddedRows)
open RecursiveInterchangeLayout (volume role)
open RecursiveInterchangeRows (pack)
variable {a c r l : ℕ}

def paddedBits (x : Fin (1*r*l) → Bool) : Fin (volume a (descriptor (paddedRows r c) l)) → Bool :=
  fun i => RecursiveRowPadding.pad (paddedRows r c) false x
    (Fin.cast (by simp [volume,descriptor]) i)

theorem padded_symbols (x : Fin (1*r*l) → Bool)
    (i : Fin (volume a (descriptor (paddedRows r c) l))) :
    CompactRowReservationData.padded (c := c) x i = bitSymbol (paddedBits (a := a) (c := c) x i) := by
  dsimp only [CompactRowReservationData.padded, paddedBits, RecursiveRowPadding.pad]
  split <;> simp_all

def roleBits (hc : 0 < c) (x : Fin (1*r*l) → Bool) (j : Fin c) :
    Fin (volume a (role (descriptor (paddedRows r c) l) c)) → Bool := fun z =>
  let ik := finProdFinEquiv.symm (Fin.cast
    (RecursiveInterchangeRows.role_volume a c (descriptor (paddedRows r c) l)) z)
  paddedBits (a := a) (c := c) x (Fin.cast
    (RecursiveInterchangeRows.volume_split a c (descriptor (paddedRows r c) l)
      (CompactRowPaddingRound.padded_bounds r c hc).2.2).symm
    (pack ik.1 (pack j ik.2)))

theorem role_symbols (hc : 0 < c) (x : Fin (1*r*l) → Bool) (j : Fin c)
    (z : Fin (volume a (role (descriptor (paddedRows r c) l) c))) :
    RecursiveInterchangeRows.roleArray a c (descriptor (paddedRows r c) l)
      (CompactRowPaddingRound.padded_bounds r c hc).2.2
      (CompactRowReservationData.padded (c := c) x) j z =
        bitSymbol (roleBits (a := a) hc x j z) := by
  exact padded_symbols _ _

def roleSlot (c : ℕ) (j : Fin c) :
    Fin (CompactRowReservationPlacement.CommonTapes c+CompactRowReservationPlacement.NativeTapes c) :=
  Fin.castAdd (CompactRowReservationPlacement.NativeTapes c) (Fin.natAdd 25 j)

def rowCount (r c : ℕ) := paddedRows r c/c

theorem rowCount_pos (hc : 0 < c) (hr : 0 < r) : 0 < rowCount r c := by
  have hcr : c ≤ paddedRows r c := by
    rw [← CompactRowPaddingRound.rounded_eq r c hr hc]
    exact RoundedRowDescriptor.divisor_le r c
  exact Nat.div_pos hcr hc

theorem role_size :
    volume a (role (descriptor (paddedRows r c) l) c) = rowCount r c*l := by
  simp [volume,role,descriptor,rowCount]

theorem rectangle_size (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front) :
    RadixRangePadding.volume (s.prefixRange (rowCount r c) f) (2^(s.width n))
      (s.gap n f) (s.suffix n) =
        volume a (role (descriptor (paddedRows r c) s.recordWidth) c) := by
  rw [role_size, s.rectangle_volume n (rowCount r c) hn f]

def rectangle (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front) (hc : 0 < c)
    (x : Fin (1*r*s.recordWidth) → Bool) (j : Fin c) :
    Fin (RadixRangePadding.volume (s.prefixRange (rowCount r c) f) (2^(s.width n))
      (s.gap n f) (s.suffix n)) → Bool :=
  fun i => roleBits (a := a) hc x j (Fin.cast (rectangle_size (a := a) s n hn f) i)

/-- Exact literal word at the reservation endpoint: both fronts, the active
slots, dirty unused bits, dirty back field and complete payload are present. -/
theorem role_tape (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front) (hc : 0 < c)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool) (j : Fin c) :
    (CompactRowReservationEndpoint.final (a := a) hc x rs ls).head (roleSlot c j) = 0 ∧
    (CompactRowReservationEndpoint.final (a := a) hc x rs ls).tape (roleSlot c j) =
      putWord (fun _ => blank) 0
        (List.ofFn (fun i => bitSymbol (rectangle (a := a) s n hn f hc x j i))) := by
  have h := CompactRowReservationEndpoint.role_word (a := a) hc x rs ls j
  refine ⟨h.1, h.2.trans ?_⟩
  unfold RecursiveRowsConstruct.word
  apply congrArg (putWord (fun _ => blank) 0)
  rw [List.ofFn_congr (rectangle_size (a := a) (r := r) (c := c) s n hn f).symm]
  apply congrArg List.ofFn
  funext i
  exact role_symbols hc x j _

end
end IntegerMultBounds.Machine.CompactGadgetReservationData
