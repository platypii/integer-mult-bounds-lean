import IntegerMultBounds.Machine.RecursiveCallBank

/-! Actual recursive call boundaries on the fixed permanent bank. Entry
constructs/clears the payload count, parks/moves arrays, saves the role-parent
headers/PC, and constructs the same-row child. Recovery is a separate block. -/
namespace IntegerMultBounds.Machine.RecursiveCallProtocol
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume child)
open RecursiveCallBank
open SharedBankStageInput (raw)
variable {t u m k : ℕ}

private theorem mapped_ne (src dst : Fin t) (hne : src ≠ dst) :
    role (u := u) src ≠ role dst := fun h => hne (role_injective h)

private theorem mapped_not_mem (ops : List (Fin t)) (src : Fin t) (hn : src ∉ ops) :
    role (u := u) src ∉ ops.map role := by
  intro h
  obtain ⟨i,hi,he⟩ := List.mem_map.mp h
  have he' := role_injective he
  subst i
  exact hn hi

def entered (ops : List (Fin t)) (src dst : Fin t) (n : ℕ) (v : Tapes (TapeCount t u) prime) :=
  RoleArrayCall.entered layout (ops.map role) (role src) (role dst) n v

def payloadEntry (ops : List (Fin t)) (src dst : Fin t) (hne : src ≠ dst) :=
  RecursiveCountedCallBoundary.entrySkeleton Shared50ModularControl.prime_prime.two_le countSlots countSlots_injective
    (layout (t := t) (u := u)) (ops.map role) (role src) (role dst) (mapped_ne src dst hne)

def recover (ops : List (Fin t)) (src dst : Fin t) (hne : src ≠ dst) :=
  RecursiveCountedCallBoundary.recoverSkeleton Shared50ModularControl.prime_prime.two_le countSlots countSlots_injective
    (layout (t := t) (u := u)) (ops.map role) (role src) (role dst) (mapped_ne src dst hne)

def enter (ops : List (Fin t)) (src dst : Fin t) (hne : src ≠ dst)
    (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  SharedBankSkeleton.compose (payloadEntry (u := u) ops src dst hne)
    (SharedBankFamily.ofProgram (RecursiveRoleChildCallSetup.placedProgram (t := t) (u := 3+u) i j code))

/-- Only headers and descriptor/PC stacks change after the payload endpoint. -/
def childBank (v : Tapes (TapeCount t u) prime) (ch : Fin 6 → List Bool)
    (aux : Tapes u prime) (st : Tapes 2 prime) :=
  bank (rolePart v) ch (v.tape (controlSlot 2)) (v.head (controlSlot 2)) aux st

theorem payload_entry_hoare (ops : List (Fin t)) (hu : ops.Nodup) (src dst : Fin t)
    (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (d : Descriptor) (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hv : RecursiveDimensionBank.Headers d hs) (hp : d.Positive)
    (hr : ∀ i ∈ ops, roles.head i = 0 ∧ RoleArrayStack.Supported (roles.tape i) (volume prime d))
    (hsource : roles.head src = 0 ∧ RoleArrayStack.Supported (roles.tape src) (volume prime d))
    (hcommon : roles.head dst = 0 ∧ roles.tape dst = fun _ => blank) :
    HoareTime (payloadEntry (u := u) ops src dst hne).program
      (fun w => w = raw (bank roles hs f p aux st) (payloadEntry (u := u) ops src dst hne).tapes)
      (fun w => w = raw (entered ops src dst (volume prime d) (bank roles hs f p aux st))
        (payloadEntry (u := u) ops src dst hne).tapes) ((88*ops.length+51883)*volume prime d) := by
  have h := RecursiveCountedCallBoundary.enter_hoare Shared50ModularControl.prime_prime.two_le countSlots countSlots_injective
    layout rfl rfl (ops.map role) (hu.map role_injective) (role src) (role dst) (mapped_ne src dst hne)
    (mapped_not_mem ops src hsrc) (mapped_not_mem ops dst hdst) (bank roles hs f p aux st)
    d hs (ready roles hs f p aux st) hv hp
    (by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
      simpa only [bank,RecursiveShiftRoleBank.common,role,Tapes.append,Fin.addCases_left] using hr i hi)
    (by simpa only [bank,RecursiveShiftRoleBank.common,role,Tapes.append,Fin.addCases_left] using hsource)
    (by simpa only [bank,RecursiveShiftRoleBank.common,role,Tapes.append,Fin.addCases_left] using hcommon)
  simp only [SharedBankRawCompose.bank_eq_raw,List.length_map] at h
  exact h

/-- The entry block is chosen only by finite call-site data. Both count
controls and every private tape are blank when its child-guard edge is taken. -/
theorem enters (ops : List (Fin t)) (hu : ops.Nodup) (src dst : Fin t)
    (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (b : ℕ) (d : Descriptor) (i j : Fin m) (hw : d.width=m*b)
    (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (code : FiniteReturnStack.Code k) (hv : RecursiveDimensionBank.Headers d hs) (hp : d.Positive)
    (hr : ∀ z ∈ ops, roles.head z = 0 ∧ RoleArrayStack.Supported (roles.tape z) (volume prime d))
    (hsource : roles.head src = 0 ∧ RoleArrayStack.Supported (roles.tape src) (volume prime d))
    (hcommon : roles.head dst = 0 ∧ roles.tape dst = fun _ => blank) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child prime 1 b d i j) ch ∧
      HoareTime (enter (u := u) ops src dst hne i j code).program
        (fun w => w = raw (bank roles hs f p aux st) (enter (u := u) ops src dst hne i j code).tapes)
        (fun w => w = raw (childBank (entered ops src dst (volume prime d) (bank roles hs f p aux st)) ch aux
          (RecursiveChildCallSetup.savedStacks hs st code)) (enter (u := u) ops src dst hne i j code).tapes)
        ((88*ops.length+51884+RecursiveRoleChildCallSetup.constant m k)*volume prime d) := by
  let mid := entered ops src dst (volume prime d) (bank roles hs f p aux st)
  have he : mid = childBank mid hs aux st := entered_bank ops src dst (volume prime d) roles hs f p aux st
  obtain ⟨ch,hch,hprep⟩ := RecursiveRoleChildCallSetup.placed_prepares b d i j hw hp hs hv (rolePart mid)
    ((work (mid.tape (controlSlot 2)) (mid.head (controlSlot 2))).append aux) st code
  have hprep' : HoareTime (RecursiveRoleChildCallSetup.placedProgram (t := t) (u := 3+u) i j code)
      (fun w => w = CleanSubbank.bank mid)
      (fun w => w = CleanSubbank.bank (childBank mid ch aux (RecursiveChildCallSetup.savedStacks hs st code)))
      (RecursiveRoleChildCallSetup.constant m k*volume prime d) := by
    apply hprep.consequence _ (fun _ h => h) le_rfl
    intro w hw'
    exact hw'.trans (congrArg (CleanSubbank.bank (s := 40)) he)
  have hentry := payload_entry_hoare ops hu src dst hne hsrc hdst d roles hs f p aux st hv hp hr hsource hcommon
  have hpraw := hprep'
  simp only [SharedBankRawCompose.bank_eq_raw] at hpraw
  have h := SharedBankRawCompose.realizes (payloadEntry (u := u) ops src dst hne)
    (SharedBankFamily.ofProgram (RecursiveRoleChildCallSetup.placedProgram (t := t) (u := 3+u) i j code))
    (fun _ => rfl) (fun _ => rfl) _ mid _ _ _ hentry hpraw
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le d hp
  exact ⟨ch,hch,h.consequence (fun _ h => h) (fun _ h => h) (by nlinarith)⟩


/-- After shared header/PC restoration, regenerate the role-parent volume,
recover the child result and parked arrays, and erase the count again. -/
theorem recovers (ops : List (Fin t)) (hu : ops.Nodup) (src dst : Fin t)
    (hne : src ≠ dst) (hsrc : src ∉ ops) (hdst : dst ∉ ops)
    (d : Descriptor) (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hv : RecursiveDimensionBank.Headers d hs) (hp : d.Positive)
    (hr : ∀ z ∈ ops, roles.head z = 0 ∧ RoleArrayStack.Supported (roles.tape z) (volume prime d))
    (hfree : ∀ z, p ≤ z → z < p+(ops.length*volume prime d : ℕ) → f z = blank)
    (hsource : roles.head src = 0 ∧ RoleArrayStack.Supported (roles.tape src) (volume prime d))
    (hcommon : roles.head dst = 0 ∧ roles.tape dst = fun _ => blank) :
    HoareTime (recover (u := u) ops src dst hne).program
      (fun w => w = raw (entered ops src dst (volume prime d) (bank roles hs f p aux st))
        (recover (u := u) ops src dst hne).tapes)
      (fun w => w = raw (bank roles hs f p aux st) (recover (u := u) ops src dst hne).tapes)
      ((92*ops.length+51883)*volume prime d) := by
  have he : RecursiveCallCount.Ready countSlots hs
      (RoleArrayCall.entered layout (ops.map role) (role src) (role dst) (volume prime d)
        (bank roles hs f p aux st)) := by
    rw [entered_bank ops src dst (volume prime d) roles hs f p aux st]
    exact ready _ _ _ _ _ _
  have hf : RoleArrayFrames.Free layout (ops.map role) (volume prime d) (bank roles hs f p aux st) := by
    change ∀ z, (bank roles hs f p aux st).head (controlSlot 2) ≤ z →
      z < (bank roles hs f p aux st).head (controlSlot 2)+((ops.map role).length*volume prime d : ℕ) →
      (bank roles hs f p aux st).tape (controlSlot 2) z = blank
    rw [(payload_stack roles hs f p aux st).1, (payload_stack roles hs f p aux st).2, List.length_map]
    exact hfree
  have h := RecursiveCountedCallBoundary.recover_hoare Shared50ModularControl.prime_prime.two_le countSlots countSlots_injective
    layout rfl rfl (ops.map role) (hu.map role_injective) (role src) (role dst) (mapped_ne src dst hne)
    (mapped_not_mem ops src hsrc) (mapped_not_mem ops dst hdst) (bank roles hs f p aux st)
    d hs (ready roles hs f p aux st) he hv hp
    (by
      intro z hz
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
      simpa only [bank,RecursiveShiftRoleBank.common,role,Tapes.append,Fin.addCases_left] using hr a ha)
    hf
    (by simpa only [bank,RecursiveShiftRoleBank.common,role,Tapes.append,Fin.addCases_left] using hsource)
    (by simpa only [bank,RecursiveShiftRoleBank.common,role,Tapes.append,Fin.addCases_left] using hcommon)
  simp only [SharedBankRawCompose.bank_eq_raw,List.length_map] at h
  exact h

end
end IntegerMultBounds.Machine.RecursiveCallProtocol
