import IntegerMultBounds.Machine.CompactComplexControllerNativeFrame
import IntegerMultBounds.Machine.CompactNativeRoleGuardedChildCaller
import IntegerMultBounds.Machine.PlacementBank
import IntegerMultBounds.Machine.CompactNativeRoleStoppedChildCaller

/-! A physical placement identifies original-role source43 with native source65
and selects the original native numeric43 bank. Controller, queue and recursion
storage stay separate. Raw codec metadata is explicit; it is not the controller
initial13 bank whose ell17 and precision18 are blank. -/
namespace IntegerMultBounds.Machine.CompactComplexNativeRoleBridge
noncomputable section
open CompactComplexControllerNativeFrame
open CompactNativeRoleSourcePorts (callerTapes external roles)
open ActiveRepairRankHeadersCommands (State)
variable {c s a : ℕ}

abbrev publicTapes (s c : ℕ) := tapes s+c

def sourceSlot : Fin (publicTapes s c) := Fin.castAdd c (nativeSlot 65)
def roleSlot (j : Fin c) : Fin (publicTapes s c) := Fin.natAdd (tapes s) j

def oldSlot (i : Fin 44) : Fin (publicTapes s c) :=
  if h : i.val<43 then Fin.castAdd c (controllerSlot ⟨i.val,h⟩) else sourceSlot

def slot : Fin (callerTapes 44 c) → Fin (publicTapes s c) :=
  Fin.addCases (m:=44+43) (n:=c)
    (Fin.addCases (m:=44) (n:=43) oldSlot (fun i => Fin.castAdd c (nativeSlot (Fin.castAdd 23 i)))) roleSlot

theorem slot_injective : Function.Injective (slot (s:=s) (c:=c)) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  apply Fin.ext
  induction i using Fin.addCases (m:=87) (n:=c) with
  | left i =>
    induction i using Fin.addCases (m:=44) (n:=43) with
    | left i =>
      induction j using Fin.addCases (m:=87) (n:=c) with
      | left j =>
        induction j using Fin.addCases (m:=44) (n:=43) with
        | left j =>
          simp only [slot,Fin.addCases_left,oldSlot] at hv
          split_ifs at hv <;> simp only [sourceSlot,controllerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
          all_goals have := i.isLt; have := j.isLt; simp only [Fin.val_castAdd]; omega
        | right j =>
          simp only [slot,Fin.addCases_left,Fin.addCases_right,oldSlot] at hv
          split_ifs at hv <;> simp only [sourceSlot,controllerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
          all_goals have := i.isLt; have := j.isLt; omega
      | right j =>
        simp only [slot,Fin.addCases_left,Fin.addCases_right,oldSlot,roleSlot] at hv
        split_ifs at hv <;> simp only [sourceSlot,controllerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd,publicTapes,tapes] at hv
        all_goals have := i.isLt; omega
    | right i =>
      induction j using Fin.addCases (m:=87) (n:=c) with
      | left j =>
        induction j using Fin.addCases (m:=44) (n:=43) with
        | left j =>
          simp only [slot,Fin.addCases_left,Fin.addCases_right,oldSlot] at hv
          split_ifs at hv <;> simp only [sourceSlot,controllerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
          all_goals have := i.isLt; have := j.isLt; omega
        | right j =>
          simp only [slot,Fin.addCases_left,Fin.addCases_right,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv ⊢
          omega
      | right j =>
        simp only [slot,Fin.addCases_left,Fin.addCases_right,roleSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd,tapes] at hv
        have := i.isLt; omega
  | right i =>
    induction j using Fin.addCases (m:=87) (n:=c) with
    | left j =>
      induction j using Fin.addCases (m:=44) (n:=43) with
      | left j =>
        simp only [slot,Fin.addCases_left,Fin.addCases_right,oldSlot,roleSlot] at hv
        split_ifs at hv <;> simp only [sourceSlot,controllerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd,tapes] at hv
        all_goals have := j.isLt; omega
      | right j =>
        simp only [slot,Fin.addCases_left,Fin.addCases_right,roleSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd,tapes] at hv
        have := j.isLt; omega
    | right j =>
      simp only [slot,Fin.addCases_right,roleSlot,Fin.val_natAdd] at hv ⊢
      omega

def placement := InjectivePlacement.placement (slot (s:=s) (c:=c)) slot_injective
  (by unfold callerTapes publicTapes tapes; omega : callerTapes 44 c+(publicTapes s c-callerTapes 44 c)=publicTapes s c)

def single (payload : Tapes (1+c) a) : Tapes 1 a := ⟨fun _ => payload.head 0,fun _ => payload.tape 0⟩
def old (control : Tapes 43 a) (payload : Tapes (1+c) a) := control.append (single payload)
def native (st : State) (tail : Tapes 22 a) (payload : Tapes (1+c) a) : Tapes 66 a :=
  (ActiveRepairRankHeadersCommands.bank st).append (tail.append (single payload))
def bank (control : Tapes 43 2) (queue : Tapes 1 2) (st : State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :=
  (CompactComplexControllerNativeFrame.bank control queue (native st tail payload) storage).append (roles payload)

theorem replace_old (control : Tapes 43 2) (payload : Tapes (1+c) 2) :
    CompactNativeRoleSourcePorts.replaceSource (old control payload) (by decide) payload=old control payload := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=43) (n:=1) with
  | left i =>
    have hi : Fin.castAdd 1 i≠CompactNativeRoleSourcePorts.source 44 (by decide) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd,CompactNativeRoleSourcePorts.source] at this; omega
    simp only [hi,ite_false]
    rfl
  | right i => fin_cases i; rfl

/-- The actual controller bank's active view is the original-role caller,
with source65 physically shared and every raw codec word retained exactly. -/
theorem active_bank (control : Tapes 43 2) (queue : Tapes 1 2) (st : State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    Placement.active placement (bank control queue st tail storage payload)=
      external (old control payload) (by decide) st payload := by
  rw [external,replace_old]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=87) (n:=c) with
  | left i =>
    induction i using Fin.addCases (m:=44) (n:=43) with
    | left i =>
      induction i using Fin.addCases (m:=43) (n:=1) with
      | left i =>
        simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_left,
          oldSlot,Fin.val_castAdd,i.isLt,dite_true,bank,CompactComplexControllerNativeFrame.bank,controllerSlot,nativeSlot,Tapes.append,
          Fin.addCases_left,old]
      | right i =>
        fin_cases i
        simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_left,
          oldSlot,Fin.val_natAdd,show ¬43+0<43 by omega,dite_false,
          sourceSlot,nativeSlot,bank,CompactComplexControllerNativeFrame.bank,native,old,single,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        rfl
    | right i =>
      simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_left,
        Fin.addCases_right,nativeSlot,bank,CompactComplexControllerNativeFrame.bank,native,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i =>
    simp only [placement,InjectivePlacement.active_slot,slot,Fin.addCases_right,
      roleSlot,bank,Tapes.append,Fin.addCases_right]

theorem payload_bank (control : Tapes 43 2) (queue : Tapes 1 2) (st : State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    SharedBank.payload (bank control queue st tail storage payload) slot=
      external (old control payload) (by decide) st payload := by
  simpa only [Placement.active,placement,InjectivePlacement.active_slot,SharedBank.payload] using
    active_bank control queue st tail storage payload

private theorem payload_update {n k : ℕ} (v : Tapes n a) (ps : Fin k → Fin n)
    (hp : Function.Injective ps) (j : Fin k) (f : ℤ → Fin (a+4)) :
    SharedBank.payload (SharedPlacementAlphabet.setTape v (ps j) f 0) ps=
      SharedPlacementAlphabet.setTape (SharedBank.payload v ps) j f 0 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=j
  all_goals simp [SharedBank.payload,SharedPlacementAlphabet.setTape,Function.update,hi,hp.eq_iff]

private theorem strip_update {n k : ℕ} (v : Tapes n a) (ps : Fin k → Fin n)
    (j : Fin k) (f : ℤ → Fin (a+4)) :
    SharedBank.strip (SharedPlacementAlphabet.setTape v (ps j) f 0) ps=SharedBank.strip v ps := by
  have hn (i : Fin n) (hi : ¬∃ k,ps k=i) : i≠ps j := fun h => hi ⟨j,h.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ j,ps j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne (hn i hi)]

def publicRole (j : Fin c) : Fin (callerTapes 44 c) := Fin.natAdd 87 j

theorem role_slot (j : Fin c) : slot (s:=s) (publicRole j)=roleSlot j := by
  simp only [slot,publicRole,Fin.addCases_right]

def stoppedProgram (dir : CompactSpectatorLeafGuardOriginal.Direction) (s : ℕ) (j : Fin c) :=
  Placement.placed (CompactNativeRoleStoppedChildCaller.program dir 44 c j)
    (CleanSubbank.placement (Fin.castAdd CompactNativeRoleGuardedChildCaller.leafTapes)
      (slot (s:=s)) slot_injective)

/-- The actual stopped caller uses the controller's native65 source and raw43
headers in place. Every controller/queue/storage tape and native spectator is
retained, with only the selected appended role word changed. -/
theorem stopped_runs (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 22 2) (storage : Tapes s 2)
    (sh : CompactGadgetReservationShape.Shape) (rows ell p : ℕ) (rho : Fin sh.chunk) {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+1)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (hdiv : c∣rows) (hc : 0<c) (hr : 0<rows) (hG : 0<sh.guard) (hA : 0<sh.axes) (hp : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) (j : Fin c) :
    let payload := CompactNativeRoleReservedBridge.rolePayload sh rows c ell hdiv f
    let st := CompactNativeRoleStoppedChildCaller.nodeState sh rows ell p rho visit ha pair
    let v := bank control queue st tail storage payload
    let g := CompactNativeRoleGuardedChildCaller.resultWord dir sh rows c ell p rho visit hdiv f j
    HoareTime (stoppedProgram dir s j)
      (fun z => z=CleanSubbank.bank (s:=callerTapes 44 c+CompactNativeRoleGuardedChildCaller.leafTapes) v)
      (fun z => z=CleanSubbank.bank (s:=callerTapes 44 c+CompactNativeRoleGuardedChildCaller.leafTapes)
        (SharedPlacementAlphabet.setTape v (roleSlot j) g 0))
      (CompactNativeRoleStoppedChildCaller.cost dir c sh rows ell p rho visit ha pair) := by
  dsimp only
  let payload := CompactNativeRoleReservedBridge.rolePayload sh rows c ell hdiv f
  let st := CompactNativeRoleStoppedChildCaller.nodeState sh rows ell p rho visit ha pair
  let v := bank control queue st tail storage payload
  let g := CompactNativeRoleGuardedChildCaller.resultWord dir sh rows c ell p rho visit hdiv f j
  have h := CompactNativeRoleStoppedChildCaller.runs dir (old control payload) (by decide) sh rows ell p rho
    visit ha pair hdiv hc hr hG hA hp f hw j
  apply CleanSubbank.realizes _ (Fin.castAdd CompactNativeRoleGuardedChildCaller.leafTapes) slot
    (Fin.castAdd_injective _ _) slot_injective v (SharedPlacementAlphabet.setTape v (roleSlot j) g 0) _ _ _
    ?_ ?_ (CleanSubbank.strip_bank _) (CleanSubbank.strip_bank _) ?_ h
  · rw [CleanSubbank.payload_bank,payload_bank]
  · rw [CleanSubbank.payload_bank,←CompactNativeRoleGuardedChildCaller.external_setRole]
    have he : CompactNativeRoleChildBank.roleSource 44 j=publicRole j := Fin.ext rfl
    rw [←role_slot, payload_update _ _ slot_injective, payload_bank, he]
  · rw [←role_slot,strip_update]

/-- Every permanent tape outside the selected role is literally stationary. -/
theorem result_frame (v : Tapes (publicTapes s c) a) (j : Fin c) (g : ℤ → Fin (a+4))
    (i : Fin (publicTapes s c)) (hi : i≠roleSlot j) :
    (SharedPlacementAlphabet.setTape v (roleSlot j) g 0).head i=v.head i ∧
      (SharedPlacementAlphabet.setTape v (roleSlot j) g 0).tape i=v.tape i := by
  simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne hi,and_self]

/-- Native source65 is preserved exactly, including its head. -/
theorem result_source (v : Tapes (publicTapes s c) a) (j : Fin c) (g : ℤ → Fin (a+4)) :
    (SharedPlacementAlphabet.setTape v (roleSlot j) g 0).head sourceSlot=v.head sourceSlot ∧
      (SharedPlacementAlphabet.setTape v (roleSlot j) g 0).tape sourceSlot=v.tape sourceSlot := by
  apply result_frame
  intro h
  have hv := congrArg Fin.val h
  simp only [sourceSlot,roleSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd,tapes] at hv
  omega

end
end IntegerMultBounds.Machine.CompactComplexNativeRoleBridge
