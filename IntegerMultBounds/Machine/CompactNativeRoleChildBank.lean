import IntegerMultBounds.Machine.CompactNativeRoleSourcePorts
import IntegerMultBounds.Machine.CompactSpectatorLeafPlacement

/-! Actual native role words are leaf source words at identical heads. A paid
quotient replaces only the copied row descriptor; immutable ell and corrected
precision remain literal. Leaf placement frames the retained controller/stack. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleChildBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactChildHeadersArithmetic
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw)
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactComplexRecursiveGeometry
open SharedPlacementAlphabet (setTape)
variable {c t : ℕ}

abbrev cmd (op : ActiveRepairRankHeadersCommands.Command) : Op := .existing (.command op)
abbrev product (f : Fin 3 → Fin 28) (hf : Function.Injective f) : Op := .existing (.product f hf)
def prepare (c : ℕ) : List Op := [.constant 19 c,.quotient ![4,19,20] (by decide),
  cmd (.erase 4),cmd (.copy 20 4 (by decide)),cmd (.erase 20),cmd (.erase 19)]
def restore (c : ℕ) : List Op := [.constant 19 c,product ![4,19,20] (by decide),
  cmd (.erase 4),cmd (.copy 20 4 (by decide)),cmd (.erase 20),cmd (.erase 19)]

theorem prepare_eval (c : ℕ) (s : Shape) (rows ell p rho left count slots right src dst : ℕ) :
    execute (prepare c) (raw s rows ell p rho left count slots right src dst)=
      raw s (rows/c) ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> simp [prepare,cmd,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,raw,Function.update]

theorem prepare_runs (c : ℕ) (s : Shape) (rows ell p rho left count slots right src dst : ℕ) (hc : 0<c) :
    HoareTime (compile (a:=2) (prepare c)).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right src dst))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s (rows/c) ell p rho left count slots right src dst))
      (scheduleCost (prepare c) (raw s rows ell p rho left count slots right src dst)) := by
  have hv : validSchedule (prepare c) (raw s rows ell p rho left count slots right src dst) := by
    simp [prepare,cmd,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      ActiveRepairRankHeadersCommands.put,raw,Function.update,hc]
  have h := schedule_runs (a:=2) _ _ hv
  rwa [prepare_eval] at h

theorem restore_eval (c : ℕ) (s : Shape) (rows ell p rho left count slots right src dst : ℕ) (hd : c∣rows) :
    execute (restore c) (raw s (rows/c) ell p rho left count slots right src dst)=
      raw s rows ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> simp [restore,cmd,product,execute,eval,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,raw,Function.update]
  rw [Nat.mul_comm,Nat.div_mul_cancel hd]

theorem restore_runs (c : ℕ) (s : Shape) (rows ell p rho left count slots right src dst : ℕ) (hd : c∣rows) (hc : 0<c) (hr : 0<rows) :
    HoareTime (compile (a:=2) (restore c)).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s (rows/c) ell p rho left count slots right src dst))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw s rows ell p rho left count slots right src dst))
      (scheduleCost (restore c) (raw s (rows/c) ell p rho left count slots right src dst)) := by
  have hle := Nat.le_of_dvd hr hd
  have hv : validSchedule (restore c) (raw s (rows/c) ell p rho left count slots right src dst) := by
    simp [restore,cmd,product,validSchedule,valid,eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
      ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
      ActiveRepairRankHeadersCommands.put,raw,Function.update]
    exact ⟨hc,hle⟩
  have h := schedule_runs (a:=2) _ _ hv
  rwa [restore_eval c s rows ell p rho left count slots right src dst hd] at h

def roleSource (t : ℕ) (j : Fin c) : Fin (callerTapes t c) := Fin.natAdd (t+43) j
def common (t : ℕ) (j : Fin c) : Fin (1+15) → Fin (callerTapes t c) :=
  Fin.addCases (fun _ => roleSource t j)
    (fun i => Fin.castAdd c (Fin.natAdd t (Fin.castAdd 15 (CompactNativeRoleStageCopy.destination i))))

theorem common_injective (t : ℕ) (j : Fin c) : Function.Injective (common t j) := by
  intro i k h
  induction i using Fin.addCases (m:=1) (n:=15) with
  | left i =>
    induction k using Fin.addCases (m:=1) (n:=15) with
    | left k => exact congrArg (Fin.castAdd 15) (Subsingleton.elim i k)
    | right k =>
      have hv := congrArg Fin.val h
      have hk := (CompactNativeRoleStageCopy.destination k).isLt
      simp [common,roleSource] at hv
      omega
  | right i =>
    induction k using Fin.addCases (m:=1) (n:=15) with
    | left k =>
      have hv := congrArg Fin.val h
      have hi := (CompactNativeRoleStageCopy.destination i).isLt
      simp [common,roleSource] at hv
      omega
    | right k =>
      apply congrArg (Fin.natAdd 1)
      apply CompactNativeRoleStageCopy.destination_injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [common] at hv
      omega

theorem role_word (s : Shape) (rows c ell : ℕ) (hd : c∣rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) (j : Fin c) :
    NativeZeroPadding.word (NativeZeroPaddingArray.word (CompactNativeRoleReservedBridge.role s rows c ell hd f j))=
      CompactSpectatorLeafAxis.word (CompactNativeRoleReservedBridge.role s rows c ell hd f j) := rfl

theorem child_payload (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hd : c∣rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) (j : Fin c) :
    SharedBank.payload (external old ht (raw s (rows/c) ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)) (common t j)=
      CompactSpectatorLeafPlacement.payload
        (CompactSpectatorLeafAxis.word (CompactNativeRoleReservedBridge.role s rows c ell hd f j))
        (CompactSpectatorLeafOriginal.values s (rows/c) ell p rho left count slots right src dst) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=1) (n:=15) with
  | left i =>
    simp only [common,Fin.addCases_left,roleSource,external,Tapes.append,Fin.addCases_right,
      Fin.addCases_left,CountedLoopReuseAlphabet.one]
    have he : (⟨j.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 j := by apply Fin.ext; dsimp; omega
    simp only [CompactNativeRoleSourcePorts.roles,he,CompactNativeRoleReservedBridge.rolePayload,
      CyclicRowCopy.payload,role_word,Tapes.append,Fin.addCases_right]
  | right i =>
    simp only [common,Fin.addCases_right,external,Tapes.append,Fin.addCases_left,
      Fin.addCases_right,Fin.addCases_right,
      ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left]
    fin_cases i <;> rfl

def leafProgram (t : ℕ) (j : Fin c) := Placement.placed CompactSpectatorLeafOriginal.program
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

theorem leaf_runs (old : Tapes t 2) (ht : 43<t) (s : Shape) (rows ell p : ℕ)
    (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)
    (slots right src dst : ℕ) (hd : c∣rows) (hc : 0<c) (hr : 0<rows)
    (hG : 0<s.guard) (hA : 0<s.axes)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) (j : Fin c) :
    let caller := external old ht (raw s (rows/c) ell p rho.val left (arity^k) slots right src dst)
      (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)
    let child := CompactNativeRoleReservedBridge.role s rows c ell hd f j
    HoareTime (leafProgram t j)
      (fun v => v=CleanSubbank.bank (s:=CompactSpectatorLeafOriginal.tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=CompactSpectatorLeafOriginal.tapes)
        (setTape caller (roleSource t j) (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafLoop.run s (rows/c) ell p rho visit (arity^k) child)) 0))
      (CompactSpectatorLeafOriginal.cost s (rows/c) ell p rho visit slots right src dst) := by
  dsimp only
  let caller := external old ht (raw s (rows/c) ell p rho.val left (arity^k) slots right src dst)
    (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)
  let child := CompactNativeRoleReservedBridge.role s rows c ell hd f j
  let vs := CompactSpectatorLeafOriginal.values s (rows/c) ell p rho.val left (arity^k) slots right src dst
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafLoop.run s (rows/c) ell p rho visit (arity^k) child)
  have hn : 0<rows/c := Nat.div_pos (Nat.le_of_dvd hr hd) hc
  have hchild : ButterflySpectatorGeometry.Width (rows/c) s.bits (2^ell) p child := fun z => hw _
  have hh := CompactSpectatorLeafOriginal.runs s (rows/c) ell p rho visit slots right src dst hG hA hn child hchild
  change HoareTime CompactSpectatorLeafOriginal.program
    (fun v => v=CompactSpectatorLeafOriginal.bank (fun _ => none) (CompactSpectatorLeafAxis.word child) vs)
    (fun v => v=CompactSpectatorLeafOriginal.bank (fun _ => none) g vs) _ at hh
  have hdata := child_payload old ht s rows ell p rho.val left (arity^k) slots right src dst hd f j
  change SharedBank.payload caller (common t j)=CompactSpectatorLeafPlacement.payload (CompactSpectatorLeafAxis.word child) vs at hdata
  apply CleanSubbank.realizes CompactSpectatorLeafOriginal.program CompactSpectatorLeafPlacement.ports (common t j)
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
end IntegerMultBounds.Machine.CompactNativeRoleChildBank
