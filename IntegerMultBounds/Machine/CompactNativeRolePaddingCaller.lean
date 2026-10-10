import IntegerMultBounds.Machine.CompactNativeRoleReservedCaller

/-! Literal reservation-padding bank adaptation to the native role caller.
All port relabelling preserves physical indices, especially source43; no native
word is copied. Retained runtime controller words are explicit six input tapes. -/
namespace IntegerMultBounds.Machine.CompactNativeRolePaddingCaller
noncomputable section
open CompactNativeRoleReservedCaller (original originalTapes single)
open CompactNativeRoleSourceRuns (reservationPayload)

abbrev remainder := (CompactReservedAxisPorts.count+2)+51
abbrev paddingTapes := CompactReservationNativePadding.commonCount+51

def association : Fin (paddingTapes+6) ≃ Fin (originalTapes remainder) :=
  finCongr (by unfold paddingTapes remainder originalTapes CompactReservationNativePadding.commonCount; omega)
def payload (c : ℕ) (xs : List (Fin 6)) :=
  CyclicRowCopy.payload (NativeZeroPadding.word xs) (fun _ : Fin c => fun _ => blank) 0 (fun _ => 0)

theorem bank_eq (st : ActiveRepairRankHeadersCommands.State) (c : ℕ) (xs : List (Fin 6)) (ctrl : Fin 6 → ℕ) :
    ((CompactReservationNativePadding.bank st xs).append (CompactNativeRoleScalarProducer.controller ctrl)).reindex association=
      original st (payload c xs) (SharedBank.empty remainder 2) ctrl := by
  have point (i : Fin (originalTapes remainder)) :
      (((CompactReservationNativePadding.bank st xs).append (CompactNativeRoleScalarProducer.controller ctrl)).reindex association).head i=
        (original st (payload c xs) (SharedBank.empty remainder 2) ctrl).head i ∧
      (((CompactReservationNativePadding.bank st xs).append (CompactNativeRoleScalarProducer.controller ctrl)).reindex association).tape i=
        (original st (payload c xs) (SharedBank.empty remainder 2) ctrl).tape i := by
    induction i using Fin.addCases (m:=43) (n:=(1+remainder)+6) with
    | left i =>
      have he : association.symm (Fin.castAdd ((1+remainder)+6) i)=
          Fin.castAdd 6 (Fin.castAdd 51 (Fin.castAdd 2 (Fin.castAdd CompactReservedAxisPorts.count (Fin.castAdd 1 i)))) :=
        Fin.ext rfl
      simp only [Tapes.reindex,he,CompactReservationNativePadding.bank,CompactReservationNativePadding.originalBank,
        CompactReservedSchedule.bank,CountedLoopHeaderClean.bank,CompactReservedAxisRun.bank,CompactReservedAxisRun.common,
        original,Tapes.append,Fin.addCases_left]
      trivial
    | right i =>
      induction i using Fin.addCases (m:=1+remainder) (n:=6) with
      | right i =>
        have he : association.symm (Fin.natAdd 43 (Fin.natAdd (1+remainder) i))=Fin.natAdd paddingTapes i :=
          by apply Fin.ext; dsimp [association,paddingTapes,remainder,originalTapes,CompactReservationNativePadding.commonCount]; omega
        simp only [Tapes.reindex,he,original,Tapes.append,Fin.addCases_right]
        trivial
      | left i =>
        induction i using Fin.addCases (m:=1) (n:=remainder) with
        | left i =>
          have he : association.symm (Fin.natAdd 43 (Fin.castAdd 6 (Fin.castAdd remainder i)))=
              Fin.castAdd 6 (Fin.castAdd 51 (Fin.castAdd 2 (Fin.castAdd CompactReservedAxisPorts.count (Fin.natAdd 43 i)))) :=
            by apply Fin.ext; dsimp [association]
          have hz : i=0 := Subsingleton.elim _ _
          simp only [Tapes.reindex]
          rw [he]
          simp only [CompactReservationNativePadding.bank,CompactReservationNativePadding.originalBank,
            CompactReservedSchedule.bank,CountedLoopHeaderClean.bank,CompactReservedAxisRun.bank,CompactReservedAxisRun.common,
            original,Tapes.append,Fin.addCases_right,Fin.addCases_left,single,payload,CyclicRowCopy.payload,
            CountedLoopReuseAlphabet.one,hz]
          trivial
        | right i =>
          induction i using Fin.addCases (m:=CompactReservedAxisPorts.count+2) (n:=51) with
          | right i =>
            have he : association.symm (Fin.natAdd 43 (Fin.castAdd 6 (Fin.natAdd 1 (Fin.natAdd (CompactReservedAxisPorts.count+2) i))))=
                Fin.castAdd 6 (Fin.natAdd CompactReservationNativePadding.commonCount i) :=
              by apply Fin.ext; dsimp [association,CompactReservationNativePadding.commonCount]; omega
            simp [Tapes.reindex,he,CompactReservationNativePadding.bank,original,Tapes.append,SharedBank.empty]
          | left i =>
            induction i using Fin.addCases (m:=CompactReservedAxisPorts.count) (n:=2) with
            | right i =>
              have he : association.symm (Fin.natAdd 43 (Fin.castAdd 6 (Fin.natAdd 1 (Fin.castAdd 51 (Fin.natAdd CompactReservedAxisPorts.count i)))))=
                  Fin.castAdd 6 (Fin.castAdd 51 (Fin.natAdd (44+CompactReservedAxisPorts.count) i)) :=
                by apply Fin.ext; dsimp [association]; omega
              simp [Tapes.reindex,he,CompactReservationNativePadding.bank,CompactReservationNativePadding.originalBank,
                CompactReservedSchedule.bank,CountedLoopHeaderClean.bank,original,Tapes.append,SharedBank.empty]
            | left i =>
              have he : association.symm (Fin.natAdd 43 (Fin.castAdd 6 (Fin.natAdd 1 (Fin.castAdd 51 (Fin.castAdd 2 i)))))=
                  Fin.castAdd 6 (Fin.castAdd 51 (Fin.castAdd 2 (Fin.natAdd 44 i))) :=
                by apply Fin.ext; dsimp [association]; omega
              simp [Tapes.reindex,he,CompactReservationNativePadding.bank,CompactReservationNativePadding.originalBank,
                CompactReservedSchedule.bank,CountedLoopHeaderClean.bank,CompactReservedAxisRun.bank,original,Tapes.append,SharedBank.empty]
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2

def paddingProgram (inverse : Bool) (c m : ℕ) :=
  reindex (extend (CompactReservationNativePadding.program inverse c m) 6) association

theorem padding_runs (inverse : Bool) (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hr : rho<K) (hDp : 0<D)
    (hD : CompactReservedHeaders.reserved c m d G K≤D)
    (f : CompactFallbackAxisRun.Array D K ell) (hw : CompactFallbackAxisRun.Width D K ell q f) (ctrl : Fin 6 → ℕ) :
    HoareTime (paddingProgram inverse c m)
      (fun v => v=original (CompactReservedHeaders.initial D K rho ell q d G)
        (payload c (NativeZeroPaddingArray.word f)) (SharedBank.empty remainder 2) ctrl)
      (fun v => v=original (CompactReservedHeaders.initial D K rho ell q d G)
        (reservationPayload inverse c m D K rho ell q d G f) (SharedBank.empty remainder 2) ctrl)
      (CompactReservationNativePadding.cost inverse c m D K rho ell q d G f) := by
  have hh := hoare_reindex_eq (hoare_extend_eq
    (CompactReservationNativePadding.runs inverse c m D K rho ell q d G hc hm hd hK hr hDp hD f hw)
    (CompactNativeRoleScalarProducer.controller ctrl)) association
  simpa only [bank_eq (c:=c),paddingProgram,reservationPayload,payload] using hh


def program (inverse : Bool) (c m : ℕ) :=
  seq (extend (extend (extend (paddingProgram inverse c m) 43) c)
    (CompactNativeRoleSourcePorts.localTapes c)) (CompactNativeRoleReservedCaller.program c m remainder)

def cost (inverse : Bool) (c m D K rho ell q d G : ℕ)
    (f : CompactFallbackAxisRun.Array D K ell) (ctrl : Fin 6 → ℕ) :=
  CompactReservationNativePadding.cost inverse c m D K rho ell q d G f+1+
    CompactNativeRoleReservedCaller.cost c m D K rho ell q d G remainder ctrl

theorem splits (inverse : Bool) (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K) (hr : rho<K) (hDp : 0<D)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D)
    (hdepth : 0<CompactGlobalRowPadding.depth m d)
    (f : CompactFallbackAxisRun.Array D K ell) (hw : CompactFallbackAxisRun.Width D K ell q f) (ctrl : Fin 6 → ℕ) :
    HoareTime (program inverse c m)
      (fun v => v=CleanSubbank.bank (s:=CompactNativeRoleSourcePorts.localTapes c)
        (((original (CompactReservedHeaders.initial D K rho ell q d G)
          (payload c (NativeZeroPaddingArray.word f)) (SharedBank.empty remainder 2) ctrl).append
            (SharedBank.empty 43 2)).append (SharedBank.empty c 2)))
      (fun v => v=CompactNativeRoleReservedCaller.output inverse c m D K rho ell q d G
        (by omega) hK hD hdepth f (SharedBank.empty remainder 2) ctrl)
      (cost inverse c m D K rho ell q d G f ctrl) := by
  have h0 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (padding_runs inverse c m D K rho ell q d G hc hm hd hK hr hDp hD f hw ctrl)
    (SharedBank.empty 43 2)) (SharedBank.empty c 2)) (SharedBank.empty (CompactNativeRoleSourcePorts.localTapes c) 2)
  have h1 := CompactNativeRoleReservedCaller.splits inverse c m D K rho ell q d G hc hm hK hd hG hDp hD hdepth f hw
    (SharedBank.empty remainder 2) ctrl
  exact h0.seq h1

end
end IntegerMultBounds.Machine.CompactNativeRolePaddingCaller
