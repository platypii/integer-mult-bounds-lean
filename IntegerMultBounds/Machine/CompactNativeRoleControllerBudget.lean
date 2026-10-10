import IntegerMultBounds.Machine.CompactNativeRoleTransferBudget

/-! The six controller scalars are the actual Stage fields, with all their
bounds derived from its geometric decomposition and real source/target slots.
No controller cost allowance or unchecked bound is supplied. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleControllerBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactNativeRoleTransferBudget (volume)

def controller {s : Shape} (v : Stage s) : Fin 6 → ℕ :=
  ![v.slots,v.f,v.left,v.right,v.source.val,v.target.val]
def geometry (s : Shape) (rows ell p rho : ℕ) : Fin 9 → ℕ :=
  ![s.chunk,s.axes,s.guard,s.active,rows,s.payload,rho,ell,p]

theorem chunk_le_bits (s : Shape) (hH : 0<s.H) (hK : 0<s.chunk) : s.chunk≤s.bits := by
  have hb : 0<CompactGadgetReservationCapacity.backChunks s.axes s.guard s.chunk := by
    unfold CompactGadgetReservationCapacity.backChunks CompactGadgetReservationCapacity.chunks CompactGadgetReservationCapacity.capacity
    apply Nat.div_pos _ hK
    change 0<s.axes*s.guard at hH
    omega
  rw [Shape.existing_bits s hK]
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem width_le_volume (s : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    CompactNativeRoleHeaders.recordWidth s p+1≤volume rows s ell p := by
  have hi : 0<CompactNativeRoleOriginal.inner s ell := by unfold CompactNativeRoleOriginal.inner; positivity
  have h0 := Nat.le_mul_of_pos_left (2*(CompactNativeRoleHeaders.recordWidth s p+1)) hi
  have h1 := Nat.le_mul_of_pos_left (CompactNativeRoleOriginal.symbols s ell p) hr
  unfold CompactNativeRoleOriginal.symbols at h1
  unfold volume CompactNativeRoleOriginal.symbols
  omega

theorem controller_bounds {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hG : 0<s.guard) (hK : 0<s.chunk) :
    ∀ j,controller v j≤volume rows s ell p := by
  have hw := width_le_volume s rows ell p hr
  have hbits : s.bits≤volume rows s ell p := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth at hw
    omega
  have hH : s.H≤s.bits := by unfold Shape.bits; omega
  have ha : s.axes≤s.bits := by
    have hh : s.axes≤s.H := Nat.le_mul_of_pos_right _ hG
    exact hh.trans hH
  have hac : s.active≤s.bits := by
    have hh := Nat.le_mul_of_pos_right s.active hK
    unfold Shape.bits
    omega
  have hdec := v.activeAxes
  have hf := v.positiveWidth
  have hs : v.slots≤s.active := by
    have hh := Nat.le_mul_of_pos_right v.slots hf
    omega
  have hleft : v.left≤s.active := by omega
  have hright : v.right≤s.active := by omega
  have hsrc := v.source.isLt
  have hdst := v.target.isLt
  have hwidth := v.widthFits
  intro j
  fin_cases j <;> simp [controller] <;> omega

theorem geometry_bounds {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    ∀ j,geometry s rows ell p v.rho j≤volume rows s ell p := by
  have hH : 0<s.H := Nat.mul_pos hA hG
  have hHbits : s.H≤s.bits := by unfold Shape.bits; omega
  have hc := chunk_le_bits s hH hK
  have ha := Nat.le_mul_of_pos_right s.axes hG
  have hg := Nat.le_mul_of_pos_left s.guard hA
  have hw := width_le_volume s rows ell p hr
  have hb : s.bits≤volume rows s ell p := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth at hw
    omega
  have hactive : s.active≤s.bits := by
    have hh := Nat.le_mul_of_pos_right s.active hK
    unfold Shape.bits
    omega
  have hsymbols := CompactNativeRoleTransferBudget.symbols_pos s ell p
  have hrows := Nat.le_mul_of_pos_right rows hsymbols
  have hV : 0<volume rows s ell p := Nat.mul_pos hr hsymbols
  have hrho := v.selectedFits
  have hell : ell<2^ell := Nat.lt_two_pow_self
  have hi : 0<2^s.bits := pow_pos (by decide) _
  have hp : 0<2*(CompactNativeRoleHeaders.recordWidth s p+1) := by omega
  have hel1 := Nat.le_mul_of_pos_left (2^ell) hi
  have hel2 := Nat.le_mul_of_pos_right (2^s.bits*2^ell) hp
  have hel3 := Nat.le_mul_of_pos_left (CompactNativeRoleOriginal.symbols s ell p) hr
  have hel : ell≤volume rows s ell p := by
    unfold volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner at *
    omega
  change s.axes*s.guard≤s.bits at hHbits
  change rows≤volume rows s ell p at hrows
  have hprecision : p≤volume rows s ell p := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth at hw
    omega
  intro j
  fin_cases j <;> simp [geometry,hpay] <;> omega


theorem values_bounds {s : Shape} (v : Stage s) (rows ell p : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    ∀ j,CompactNativeRoleStageCopy.values (geometry s rows ell p v.rho) (controller v) j≤volume rows s ell p := by
  have hg := geometry_bounds v rows ell p hr hA hG hK hpay
  have hc := controller_bounds v rows ell p hr hG hK
  intro j
  have g0 := hg 0
  have g1 := hg 1
  have g2 := hg 2
  have g3 := hg 3
  have g4 := hg 4
  have g5 := hg 5
  have g6 := hg 6
  have g7 := hg 7
  have g8 := hg 8
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  have c4 := hc 4
  have c5 := hc 5
  simp [geometry] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  simp [controller] at c0 c1 c2 c3 c4 c5
  fin_cases j <;> simp [CompactNativeRoleStageCopy.values,geometry,controller] <;> omega

theorem copy_linear {s : Shape} (v : Stage s) (rows ell p u : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) (hpay : s.payload=1) :
    BinaryDescriptorInstallMarkedList.cost (CompactNativeRoleStageCopy.instructions (CompactNativeRoleScalarProducer.focus u))
      (CompactNativeRoleStageCopy.wordAt (CompactNativeRoleScalarProducer.focus u)
        (CompactNativeRoleStageCopy.values (geometry s rows ell p v.rho) (controller v)))≤150*volume rows s ell p := by
  have hb := values_bounds v rows ell p hr hA hG hK hpay
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hc : CompactNativeRoleStageCopy.Consistent (CompactNativeRoleScalarProducer.focus u)
      (CompactNativeRoleStageCopy.values (geometry s rows ell p v.rho) (controller v)) := by
    intro i j he
    rw [CompactNativeRoleScalarProducer.focus_injective u he]
  have hh := BinaryDescriptorInstallMarkedList.cost_le
    (CompactNativeRoleStageCopy.instructions (CompactNativeRoleScalarProducer.focus u))
    (CompactNativeRoleStageCopy.wordAt (CompactNativeRoleScalarProducer.focus u)
      (CompactNativeRoleStageCopy.values (geometry s rows ell p v.rho) (controller v))) (volume rows s ell p+1) (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      rw [CompactNativeRoleStageCopy.source_word _ _ hc]
      exact (ActiveRepairRankHeadersCommands.bits_length _).trans (by have := hb j; omega))
  simp only [CompactNativeRoleStageCopy.instructions,List.length_map,List.length_finRange] at hh ⊢
  omega

theorem actual_copy_linear (c m D K ell q d G u : ℕ)
    (v : Stage (CompactReservationNativeRows.shape c m d D G K))
    (hc : 0<c) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    BinaryDescriptorInstallMarkedList.cost (CompactNativeRoleStageCopy.instructions (CompactNativeRoleScalarProducer.focus u))
      (CompactNativeRoleStageCopy.wordAt (CompactNativeRoleScalarProducer.focus u)
        (CompactNativeRoleStageCopy.values
          (CompactNativeRoleScalarHeaders.values c m D K v.rho ell q d G) (controller v)))≤
      300*CompactFallbackAxisRun.volume D K ell q := by
  have he : CompactNativeRoleScalarHeaders.values c m D K v.rho ell q d G=
      geometry (CompactReservationNativeRows.shape c m d D G K) (CompactGlobalRowPadding.initialRows c m d K)
        ell (CompactNativeRoleReservedBridge.precision c m d D K q) v.rho := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  have hh := copy_linear v (CompactGlobalRowPadding.initialRows c m d K) ell
    (CompactNativeRoleReservedBridge.precision c m d D K q) u
    (CompactGlobalRowPadding.initial_positive c m d K hc hK) hd hG hK rfl
  have hv := CompactNativeRoleTransferBudget.reservation_volume c m d D G K ell q hc hK hD
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleControllerBudget
