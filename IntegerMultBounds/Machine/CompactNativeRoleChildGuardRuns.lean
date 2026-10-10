import IntegerMultBounds.Machine.CompactNativeRoleChildPrecisionSaved

/-! Actual guarded forward/inverse leaf execution on a split native role.
Its baseline18 is derived from corrected precision; saved corrected21 and
payload26, other roles, and the persistent controller/stack are all framed. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleChildGuardRuns
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactNativeRoleChildBank (common common_injective roleSource)
open CompactNativeRoleChildPrecision (baseline)
open ActiveRepairRankHeadersCommands (put)
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactSpectatorLeafGuardOriginal (Direction)
open SharedPlacementAlphabet (setTape)
variable {c t : ℕ}

theorem child_payload (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst saved : ℕ) (hd : c∣rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) (j : Fin c) :
    SharedBank.payload (external old ht (put (baseline s (rows/c) ell p rho left count slots right src dst) 26 saved)
      (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)) (common t j)=
      CompactSpectatorLeafPlacement.payload
        (CompactSpectatorLeafAxis.word (CompactNativeRoleReservedBridge.role s rows c ell hd f j))
        (CompactSpectatorLeafOriginal.values s (rows/c) ell (p-2*s.bits) rho left count slots right src dst) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=1) (n:=15) with
  | left i =>
    simp only [common,Fin.addCases_left,roleSource,external,Tapes.append,Fin.addCases_right,
      Fin.addCases_left,CountedLoopReuseAlphabet.one]
    have he : (⟨j.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 j := by apply Fin.ext; dsimp; omega
    simp only [CompactNativeRoleSourcePorts.roles,he,CompactNativeRoleReservedBridge.rolePayload,
      CyclicRowCopy.payload,CompactNativeRoleChildBank.role_word,Tapes.append,Fin.addCases_right]
  | right i =>
    simp only [common,Fin.addCases_right,external,Tapes.append,Fin.addCases_left,
      Fin.addCases_right,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    fin_cases i <;> rfl

def program (dir : Direction) (t : ℕ) (j : Fin c) :=
  Placement.placed (CompactSpectatorLeafGuardOriginal.phaseProgram dir)
    (CleanSubbank.placement CompactSpectatorLeafPlacement.ports (common t j) (common_injective t j))

private theorem payload_update {n k : ℕ} (v : Tapes n 2) (ps : Fin k → Fin n)
    (hp : Function.Injective ps) (j : Fin k) (f : ℤ → Fin 6) :
    SharedBank.payload (setTape v (ps j) f 0) ps=setTape (SharedBank.payload v ps) j f 0 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=j
  all_goals simp [SharedBank.payload,setTape,Function.update,hi,hp.eq_iff]

private theorem strip_update {n k : ℕ} (v : Tapes n 2) (ps : Fin k → Fin n)
    (j : Fin k) (f : ℤ → Fin 6) :
    SharedBank.strip (setTape v (ps j) f 0) ps=SharedBank.strip v ps := by
  have hn (i : Fin n) (hi : ¬∃ k,ps k=i) : i≠ps j := fun h => hi ⟨j,h.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ j,ps j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals simp only [setTape,Function.update_of_ne (hn i hi)]

theorem phase_runs (dir : Direction) (old : Tapes t 2) (ht : 43<t) (s : Shape) (rows ell p : ℕ)
    (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)
    (slots right src dst saved : ℕ) (hd : c∣rows) (hc : 0<c) (hr : 0<rows)
    (hG : 0<s.guard) (hA : 0<s.axes) (hp : 2*s.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) (j : Fin c) :
    let caller := external old ht (put (baseline s (rows/c) ell p rho.val left (arity^k) slots right src dst) 26 saved)
      (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)
    let child := CompactNativeRoleReservedBridge.role s rows c ell hd f j
    HoareTime (program dir t j)
      (fun v => v=CleanSubbank.bank (s:=CompactSpectatorLeafOriginal.tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=CompactSpectatorLeafOriginal.tapes)
        (setTape caller (roleSource t j) (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s (rows/c) ell (p-2*s.bits) rho visit child)) 0))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir s (rows/c) ell (p-2*s.bits) rho visit slots right src dst) := by
  dsimp only
  let caller := external old ht (put (baseline s (rows/c) ell p rho.val left (arity^k) slots right src dst) 26 saved)
    (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)
  let child := CompactNativeRoleReservedBridge.role s rows c ell hd f j
  let vs := CompactSpectatorLeafOriginal.values s (rows/c) ell (p-2*s.bits) rho.val left (arity^k) slots right src dst
  let g := CompactSpectatorLeafAxis.word
    (CompactSpectatorLeafGuardOriginal.result dir s (rows/c) ell (p-2*s.bits) rho visit child)
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have hwidth : CompactNativeRoleHeaders.recordWidth s p=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation s.bits (p-2*s.bits)) s.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  have hchild : ButterflySpectatorSemantics.Width (rows/c) s.bits (2^ell) (p-2*s.bits) child := by
    intro z
    rw [←hwidth]
    exact hw _
  have hh := CompactSpectatorLeafGuardOriginal.phase_runs dir s (rows/c) ell (p-2*s.bits) rho visit
    slots right src dst hG hA hn child hchild
  change HoareTime (CompactSpectatorLeafGuardOriginal.phaseProgram dir)
    (fun v => v=CompactSpectatorLeafOriginal.bank (fun _ => none) (CompactSpectatorLeafAxis.word child) vs)
    (fun v => v=CompactSpectatorLeafOriginal.bank (fun _ => none) g vs) _ at hh
  have hdata := child_payload old ht s rows ell p rho.val left (arity^k) slots right src dst saved hd f j
  change SharedBank.payload caller (common t j)=CompactSpectatorLeafPlacement.payload (CompactSpectatorLeafAxis.word child) vs at hdata
  apply CleanSubbank.realizes (CompactSpectatorLeafGuardOriginal.phaseProgram dir) CompactSpectatorLeafPlacement.ports (common t j)
    CompactSpectatorLeafPlacement.ports_injective (common_injective t j) caller (setTape caller (roleSource t j) g 0)
    (CompactSpectatorLeafOriginal.bank (fun _ => none) (CompactSpectatorLeafAxis.word child) vs)
    (CompactSpectatorLeafOriginal.bank (fun _ => none) g vs) _
    ?_ ?_ (CompactSpectatorLeafPlacement.bank_clean _ _) (CompactSpectatorLeafPlacement.bank_clean _ _) ?_ hh
  · rw [CompactSpectatorLeafPlacement.bank_payload]; exact hdata.symm
  · rw [CompactSpectatorLeafPlacement.bank_payload]
    have he : roleSource t j=common t j (Fin.castAdd 15 (0 : Fin 1)) := rfl
    rw [he,payload_update _ _ (common_injective t j),hdata]
    unfold CompactSpectatorLeafPlacement.payload
    rw [SharedPlacementAlphabet.setTape_append_left]
    congr 1
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  · have he : roleSource t j=common t j (Fin.castAdd 15 (0 : Fin 1)) := rfl
    rw [he,strip_update]

end
end IntegerMultBounds.Machine.CompactNativeRoleChildGuardRuns
