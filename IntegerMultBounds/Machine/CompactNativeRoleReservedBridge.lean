import IntegerMultBounds.Machine.CompactNativeRoleOriginal
import IntegerMultBounds.Machine.CompactReservationNativeRows
import IntegerMultBounds.Machine.CompactReservationNativePadding

/-! The genuine globally padded reservation word has the exact native row
representation used by every descendant role. Original high binary coordinates
are retained by the outer row range; Shape.bits is immutable after reservation.
Changing row multiplicity never narrows the stored signed coefficient fields. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleReservedBridge
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactGlobalRowPadding
open NativeZeroPaddingArray (word)
open CompactReservationNativeRows (shape rowView)

theorem grouped_cardinality (rows c L : ℕ) (hd : c ∣ rows) :
    ((rows/c)*c)*L=rows*L := congrArg (fun r => r*L) (Nat.div_mul_cancel hd)

def grouped (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) :
    CompactNativeRoleGeometry.Array (rows/c) c (CompactNativeRoleOriginal.inner s ell) :=
  fun i => f (Fin.cast (grouped_cardinality rows c (CompactNativeRoleOriginal.inner s ell) hd) i)

theorem grouped_word (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) :
    word (grouped s rows c ell hd f)=word f := by
  have he := congrArg List.flatten (List.ofFn_congr
    (grouped_cardinality rows c (CompactNativeRoleOriginal.inner s ell) hd)
    (fun i => ButterflyStreamData.encoded (grouped s rows c ell hd f i)))
  apply he.trans
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  unfold grouped
  exact congrArg (fun z => ButterflyStreamData.encoded (f z)) (Fin.ext rfl)

theorem grouped_width (s : Shape) (rows c ell w : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ i,(grouped s rows c ell hd f i).1.length=w ∧ (grouped s rows c ell hd f i).2.length=w := fun _ => hw _

/-- The role's entire immutable binary/polynomial suffix is unchanged. -/
def role (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) (j : Fin c) :
    CompactSpectatorVisitGeometry.Array s (rows/c) ell := CompactNativeRoleGeometry.role (grouped s rows c ell hd f) j

theorem global_index (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) (i : Fin (rows/c)) (j : Fin c)
    (k : Fin (CompactNativeRoleOriginal.inner s ell)) :
    role s rows c ell hd f j (RecursiveInterchangeRows.pack i k)=
      f (Fin.cast (grouped_cardinality rows c (CompactNativeRoleOriginal.inner s ell) hd)
        (RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack i j) k)) := by
  exact CompactNativeRoleGeometry.role_index (grouped s rows c ell hd f) i j k

def precision (c m d D K q : ℕ) := q+2*(D*K)+2*(rowAxes c m d*K)

theorem precision_width (c m d D G K q : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    CompactNativeRoleHeaders.recordWidth (shape c m d D G K) (precision c m d D K q)=
      CompactReservationNativeRows.width D K q := by
  have he := CompactGlobalReservation.original_bits c m d D G K 1 hK hD
  unfold CompactNativeRoleHeaders.recordWidth CompactReservationNativeRows.width precision
    ButterflyGuard.width ButterflyGuard.halfWidth CompactFallbackHeaders.reservation CompactFallbackHeaders.bits
  change _=_ at he
  change _=_
  dsimp only [shape] at he ⊢
  omega

def padded (inverse : Bool) (c m d D G K rho ell q : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : CompactFallbackAxisRun.Array D K ell) :
    CompactSpectatorVisitGeometry.Array (shape c m d D G K) (initialRows c m d K) ell := fun i =>
  NativeZeroPaddingArray.padded (originalRows c m d K) (initialRows c m d K)
    (shape c m d D G K).bits ell (CompactReservationNativeRows.width D K q)
    (initial_bounds c m d K hc hK).1
    (rowView c m d D G K ell hK hD (CompactReservedOriginal.result inverse c m D K rho ell q d G f))
    (Fin.cast (by unfold ButterflySpectatorGeometry.Size; ring) i)

theorem padded_width (inverse : Bool) (c m d D G K rho ell q : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : CompactFallbackAxisRun.Array D K ell)
    (hw : CompactFallbackAxisRun.Width D K ell q f) :
    ∀ i,(padded inverse c m d D G K rho ell q hc hK hD f i).1.length=
      CompactNativeRoleHeaders.recordWidth (shape c m d D G K) (precision c m d D K q) ∧
      (padded inverse c m d D G K rho ell q hc hK hD f i).2.length=
      CompactNativeRoleHeaders.recordWidth (shape c m d D G K) (precision c m d D K q) := by
  rw [precision_width c m d D G K q hK hD]
  intro i
  exact NativeZeroPaddingArray.padded_width _ _ _ _ _ _ _
    (CompactReservationNativeRows.row_width c m d D G K ell q hK hD _
      (CompactReservedOriginal.width_result inverse c m D K rho ell q d G f hw)) _

theorem padded_word (inverse : Bool) (c m d D G K rho ell q : ℕ) (hc : 0<c) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (f : CompactFallbackAxisRun.Array D K ell) :
    word (padded inverse c m d D G K rho ell q hc hK hD f)=
      CompactReservationNativePadding.result inverse c m D K rho ell q d G f := by
  unfold padded word
  have he : ButterflySpectatorGeometry.Size (initialRows c m d K) (shape c m d D G K).bits (2^ell)=
      initialRows c m d K*2^(shape c m d D G K).bits*2^ell := by unfold ButterflySpectatorGeometry.Size; ring
  have hh := congrArg List.flatten (List.ofFn_congr he
    (fun i => ButterflyStreamData.encoded
      (NativeZeroPaddingArray.padded (originalRows c m d K) (initialRows c m d K)
        (shape c m d D G K).bits ell (CompactReservationNativeRows.width D K q)
        (initial_bounds c m d K hc hK).1
        (rowView c m d D G K ell hK hD (CompactReservedOriginal.result inverse c m D K rho ell q d G f))
        (Fin.cast he i))))
  rw [hh]
  change word (NativeZeroPaddingArray.padded _ _ _ _ _ _ _)=_
  rw [NativeZeroPaddingArray.padded_word,CompactReservationNativeRows.word_rowView]
  unfold CompactReservationNativePadding.result CompactReservationNativePadding.count
  have hbits := CompactReservationPaddingHeaders.remaining_bits c m d D G K hK hD
  have hwidth := CompactReservationPaddingHeaders.width_eq D K q
  simp only [shape,CompactReservationNativeRows.width,←hbits,←hwidth]

def sourcePayload (s : Shape) (rows ell : ℕ) (f : CompactSpectatorVisitGeometry.Array s rows ell) (c : ℕ) :=
  CyclicRowCopy.payload (NativeZeroPadding.word (word f)) (fun _ : Fin c => fun _ => blank) 0 (fun _ => 0)
def rolePayload (s : Shape) (rows c ell : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => NativeZeroPadding.word (word (role s rows c ell hd f j))) 0 (fun _ => 0)

theorem splits (s : Shape) (rows c ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) :
    HoareTime (CompactNativeRoleOriginal.splitProgram c)
      (fun v => v=CompactNativeRoleOriginal.bank (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target)
        (sourcePayload s rows ell f c))
      (fun v => v=CompactNativeRoleOriginal.bank (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target)
        (rolePayload s rows c ell hd f))
      (CompactNativeRoleOriginal.cost false (rows/c) c s ell p rho left count slots right source target) := by
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have hh := CompactNativeRoleOriginal.splits (rows/c) c s ell p rho left count slots right source target
    hc hn hG hA hK (grouped s rows c ell hd f) (grouped_width s rows c ell _ hd f hw)
  have hrw : CompactSpectatorLeafSetup.raw s (rows/c*c) ell p rho left count slots right source target=
      CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target :=
    congrArg (fun r => CompactSpectatorLeafSetup.raw s r ell p rho left count slots right source target) (Nat.div_mul_cancel hd)
  have hs : CompactNativeRoleOriginal.sourcePayload s ell (grouped s rows c ell hd f)=sourcePayload s rows ell f c := by
    unfold CompactNativeRoleOriginal.sourcePayload sourcePayload
    rw [grouped_word]
  have hs0 := congrArg₂ CompactNativeRoleOriginal.bank hrw hs
  have hs1 : CompactNativeRoleOriginal.bank
      (CompactSpectatorLeafSetup.raw s (rows/c*c) ell p rho left count slots right source target)
      (CompactNativeRoleOriginal.rolePayload s ell (grouped s rows c ell hd f))=
      CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target) (rolePayload s rows c ell hd f) := by
    rw [hrw]
    rfl
  exact hh.consequence (fun _ h => h.trans hs0.symm) (fun _ h => h.trans hs1) le_rfl

theorem merges (s : Shape) (rows c ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) :
    HoareTime (CompactNativeRoleOriginal.mergeProgram c)
      (fun v => v=CompactNativeRoleOriginal.bank (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target)
        (rolePayload s rows c ell hd f))
      (fun v => v=CompactNativeRoleOriginal.bank (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target)
        (sourcePayload s rows ell f c))
      (CompactNativeRoleOriginal.cost true (rows/c) c s ell p rho left count slots right source target) := by
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have hh := CompactNativeRoleOriginal.merges (rows/c) c s ell p rho left count slots right source target
    hc hn hG hA hK (grouped s rows c ell hd f) (grouped_width s rows c ell _ hd f hw)
  have hrw : CompactSpectatorLeafSetup.raw s (rows/c*c) ell p rho left count slots right source target=
      CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target :=
    congrArg (fun r => CompactSpectatorLeafSetup.raw s r ell p rho left count slots right source target) (Nat.div_mul_cancel hd)
  have hs : CompactNativeRoleOriginal.sourcePayload s ell (grouped s rows c ell hd f)=sourcePayload s rows ell f c := by
    unfold CompactNativeRoleOriginal.sourcePayload sourcePayload
    rw [grouped_word]
  have hs0 := congrArg₂ CompactNativeRoleOriginal.bank hrw hs
  have hs1 : CompactNativeRoleOriginal.bank
      (CompactSpectatorLeafSetup.raw s (rows/c*c) ell p rho left count slots right source target)
      (CompactNativeRoleOriginal.rolePayload s ell (grouped s rows c ell hd f))=
      CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target) (rolePayload s rows c ell hd f) := by
    rw [hrw]
    rfl
  exact hh.consequence (fun _ h => h.trans hs1.symm) (fun _ h => h.trans hs0) le_rfl

/-- Every actual descendant supplies a legal role split with precisely its
next outer row count; the shape's binary address count never changes. -/
theorem descendant (c m d K j : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hK : 0<K) (hj : j<depth m d) (hG : 0<s.guard) (hA : 0<s.axes) (hsK : 0<s.chunk)
    (f : CompactSpectatorVisitGeometry.Array s (rowsAt c m d K j) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) :
    HoareTime (CompactNativeRoleOriginal.splitProgram c)
      (fun v => v=CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw s (rowsAt c m d K j) ell p rho left count slots right source target)
        (sourcePayload s (rowsAt c m d K j) ell f c))
      (fun v => v=CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw s (rowsAt c m d K j) ell p rho left count slots right source target)
        (rolePayload s (rowsAt c m d K j) c ell (split_divides c m d K j hc hK hj) f))
      (CompactNativeRoleOriginal.cost false (rowsAt c m d K (j+1)) c s ell p rho left count slots right source target) := by
  have hh := splits s (rowsAt c m d K j) c ell p rho left count slots right source target hc
    (rowsAt_positive c m d K j hc hK (by omega)) (split_divides c m d K j hc hK hj) hG hA hsK f hw
  rwa [next_rows] at hh

end
end IntegerMultBounds.Machine.CompactNativeRoleReservedBridge
