import IntegerMultBounds.Machine.CompactNativeRoleScalarCaller

/-! Paid global scalar bank to native reservation-role split. The genuine
padding result remains at source43 throughout metadata preparation, then moves
destructively to complete role words. Every original scalar, retained controller
word and unrelated tape is framed, with all temporary metadata reclaimed. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleReservedCaller
noncomputable section
open CompactNativeRoleSourcePorts
open CompactNativeRoleSourceRuns (reservationPayload)
open CompactReservationNativeRows (shape)
open CompactGlobalRowPadding (initialRows)
open CompactNativeRoleReservedBridge (padded precision)
variable {u : ℕ}

abbrev originalTapes (u : ℕ) := 43+((1+u)+6)
def single {c : ℕ} (payload : Tapes (1+c) 2) : Tapes 1 2 := ⟨fun _ => payload.head 0,fun _ => payload.tape 0⟩
def original (st : ActiveRepairRankHeadersCommands.State) {c : ℕ}
    (payload : Tapes (1+c) 2) (extra : Tapes u 2) (ctrl : Fin 6 → ℕ) :=
  (ActiveRepairRankHeadersCommands.bank st).append
    (((single payload).append extra).append (CompactNativeRoleScalarProducer.controller ctrl))

theorem replace_original (st : ActiveRepairRankHeadersCommands.State) {c : ℕ}
    (payload : Tapes (1+c) 2) (extra : Tapes u 2) (ctrl : Fin 6 → ℕ) :
    replaceSource (original st payload extra ctrl) (by omega) payload=
      original st payload extra ctrl := by
  have he : source (originalTapes u) (by unfold originalTapes; omega)=
      Fin.natAdd 43 (Fin.castAdd 6 (Fin.castAdd u (0 : Fin 1))) := Fin.ext rfl
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals split_ifs with hi
  all_goals first
    | subst i
      simp only [he,Tapes.append,Fin.addCases_right,Fin.addCases_left,single]
    | rfl

theorem empty_roles (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (f : CompactFallbackAxisRun.Array D K ell) :
    roles (reservationPayload inverse c m D K rho ell q d G f)=SharedBank.empty c 2 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have he : (⟨i.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 i := Fin.ext (by dsimp; omega)
    simp [he,reservationPayload,CyclicRowCopy.payload,Tapes.append]

def setupProgram (c m u : ℕ) :=
  extend (extend (CompactNativeRoleScalarCaller.program c m (1+u)) c) (localTapes c)
def program (c m u : ℕ) :=
  seq (setupProgram c m u)
    (placed (CompactNativeRoleOriginal.splitProgram c) (originalTapes u) (by unfold originalTapes; omega))

def input (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (f : CompactFallbackAxisRun.Array D K ell) (extra : Tapes u 2) (ctrl : Fin 6 → ℕ) :=
  CleanSubbank.bank (s:=localTapes c)
    (((original (CompactReservedHeaders.initial D K rho ell q d G)
      (reservationPayload inverse c m D K rho ell q d G f) extra ctrl).append
        (SharedBank.empty 43 2)).append (SharedBank.empty c 2))

def output (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (hc : 0<c) (hK : 0<K) (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d)
    (f : CompactFallbackAxisRun.Array D K ell) (extra : Tapes u 2) (ctrl : Fin 6 → ℕ) :=
  CleanSubbank.bank (s:=localTapes c)
    (external (original (CompactReservedHeaders.initial D K rho ell q d G)
      (reservationPayload inverse c m D K rho ell q d G f) extra ctrl)
      (by omega) (CompactNativeRoleScalarProducer.outputState c m D K rho ell q d G ctrl)
      (CompactNativeRoleReservedBridge.rolePayload (shape c m d D G K) (initialRows c m d K) c ell
        (dvd_trans (dvd_pow_self c (by omega : CompactGlobalRowPadding.depth m d≠0))
          (CompactGlobalRowPadding.initial_bounds c m d K hc hK).2.2.2)
        (padded inverse c m d D G K rho ell q hc hK hD f)))

def cost (c m D K rho ell q d G u : ℕ) (ctrl : Fin 6 → ℕ) :=
  CompactNativeRoleScalarProducer.cost c m D K rho ell q d G (1+u) ctrl+1+
  CompactNativeRoleOriginal.cost false (initialRows c m d K/c) c (shape c m d D G K)
    ell (precision c m d D K q) rho (ctrl 2) (ctrl 1) (ctrl 0) (ctrl 3) (ctrl 4) (ctrl 5)

theorem splits (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (hc : 2≤c) (hm : 2≤m) (hK : 0<K) (hd : 0<d) (hG : 0<G) (hDp : 0<D)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d)
    (f : CompactFallbackAxisRun.Array D K ell) (hw : CompactFallbackAxisRun.Width D K ell q f)
    (extra : Tapes u 2) (ctrl : Fin 6 → ℕ) :
    HoareTime (program c m u)
      (fun v => v=input inverse c m D K rho ell q d G f extra ctrl)
      (fun v => v=output inverse c m D K rho ell q d G (by omega) hK hD hdepth f extra ctrl)
      (cost c m D K rho ell q d G u ctrl) := by
  have h0 := hoare_extend_eq (hoare_extend_eq
    (CompactNativeRoleScalarCaller.runs c m D K rho ell q d G hc hm hd hG hK hD hDp ctrl
      ((single (reservationPayload inverse c m D K rho ell q d G f)).append extra))
    (SharedBank.empty c 2)) (SharedBank.empty (localTapes c) 2)
  have h1 := CompactNativeRoleSourceRuns.reserved_splits inverse m D K rho ell q d G
    (by omega : 0<c) hK hd hG hD hdepth f hw ctrl
    (original (CompactReservedHeaders.initial D K rho ell q d G)
      (reservationPayload inverse c m D K rho ell q d G f) extra ctrl)
    (by omega)
  have hi : external (original (CompactReservedHeaders.initial D K rho ell q d G)
      (reservationPayload inverse c m D K rho ell q d G f) extra ctrl)
      (by omega) (CompactNativeRoleScalarProducer.outputState c m D K rho ell q d G ctrl)
      (reservationPayload inverse c m D K rho ell q d G f)=
    ((original (CompactReservedHeaders.initial D K rho ell q d G)
      (reservationPayload inverse c m D K rho ell q d G f) extra ctrl).append
        (ActiveRepairRankHeadersCommands.bank (CompactNativeRoleScalarProducer.outputState c m D K rho ell q d G ctrl))).append
          (SharedBank.empty c 2) := by
    rw [external,replace_original,empty_roles]
  rw [hi] at h1
  exact h0.seq h1

end
end IntegerMultBounds.Machine.CompactNativeRoleReservedCaller
