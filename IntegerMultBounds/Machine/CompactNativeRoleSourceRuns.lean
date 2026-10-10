import IntegerMultBounds.Machine.CompactNativeRoleSourcePorts
import IntegerMultBounds.Machine.CompactNativeRoleAssembly

/-! Concrete reservation-result splitting and arbitrary descendant-result
joining at the retained global source43. The complete immutable reservation
shape and the corrected stored precision are used at both physical endpoints. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleSourceRuns
noncomputable section
open CompactNativeRoleSourcePorts
open CompactReservationNativeRows (shape)
open CompactGlobalRowPadding (initialRows)
open CompactNativeRoleReservedBridge (padded precision)
variable {c t : ℕ}

theorem merges (n : ℕ) (s : CompactGadgetReservationShape.Shape)
    (ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hn : 0<n) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (data : Fin c → Fin (n*CompactNativeRoleOriginal.inner s ell) → ButterflyStreamData.Coefficient)
    (hw : ∀ j z,(data j z).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (data j z).2.length=CompactNativeRoleHeaders.recordWidth s p)
    (old : Tapes t 2) (ht : 43<t) :
    HoareTime (placed (CompactNativeRoleOriginal.mergeProgram c) t ht)
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactSpectatorLeafSetup.raw s (n*c) ell p rho left count slots right src dst)
          (CompactNativeRoleAssembly.payload (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data)))
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactSpectatorLeafSetup.raw s (n*c) ell p rho left count slots right src dst)
          (CompactNativeRoleOriginal.sourcePayload (n:=n) (c:=c) s ell
            (CompactNativeRoleAssembly.join (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data))))
      (CompactNativeRoleOriginal.cost true n c s ell p rho left count slots right src dst) := by
  exact realizes _ old ht _ _ _ _
    (CompactNativeRoleAssembly.merges n c s ell p rho left count slots right src dst hc hn hG hA hK data hw)

def reservationPayload (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (f : CompactFallbackAxisRun.Array D K ell) :=
  CyclicRowCopy.payload
    (NativeZeroPadding.word (CompactReservationNativePadding.result inverse c m D K rho ell q d G f))
    (fun _ : Fin c => fun _ => blank) 0 (fun _ => 0)

theorem reservationPayload_eq (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (hc : 0<c) (hK : 0<K) (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (f : CompactFallbackAxisRun.Array D K ell) :
    reservationPayload inverse c m D K rho ell q d G f=
      CompactNativeRoleReservedBridge.sourcePayload (shape c m d D G K) (initialRows c m d K) ell
        (padded inverse c m d D G K rho ell q hc hK hD f) c := by
  unfold reservationPayload CompactNativeRoleReservedBridge.sourcePayload
  rw [CompactNativeRoleReservedBridge.padded_word]

theorem reserved_splits (inverse : Bool) (m D K rho ell q d G : ℕ)
    (hc : 0<c) (hK : 0<K) (hd : 0<d) (hG : 0<G)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d)
    (f : CompactFallbackAxisRun.Array D K ell) (hw : CompactFallbackAxisRun.Width D K ell q f)
    (ctrl : Fin 6 → ℕ) (old : Tapes t 2) (ht : 43<t) :
    HoareTime (placed (CompactNativeRoleOriginal.splitProgram c) t ht)
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactNativeRoleScalarProducer.outputState c m D K rho ell q d G ctrl)
          (reservationPayload inverse c m D K rho ell q d G f)))
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactNativeRoleScalarProducer.outputState c m D K rho ell q d G ctrl)
          (CompactNativeRoleReservedBridge.rolePayload (shape c m d D G K) (initialRows c m d K) c ell
            (dvd_trans (dvd_pow_self c (by omega : CompactGlobalRowPadding.depth m d≠0))
              (CompactGlobalRowPadding.initial_bounds c m d K hc hK).2.2.2)
            (padded inverse c m d D G K rho ell q hc hK hD f))))
      (CompactNativeRoleOriginal.cost false (initialRows c m d K/c) c (shape c m d D G K)
        ell (precision c m d D K q) rho (ctrl 2) (ctrl 1) (ctrl 0) (ctrl 3) (ctrl 4) (ctrl 5)) := by
  rw [CompactNativeRoleScalarProducer.outputState_raw,reservationPayload_eq inverse c m D K rho ell q d G hc hK hD f]
  exact splits _ _ _ _ _ _ _ _ _ _ _ hc (CompactGlobalRowPadding.initial_positive c m d K hc hK) _ hG hd hK
    _ (CompactNativeRoleReservedBridge.padded_width inverse c m d D G K rho ell q hc hK hD f hw) old ht

end
end IntegerMultBounds.Machine.CompactNativeRoleSourceRuns
