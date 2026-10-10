import IntegerMultBounds.Machine.CompactComplexNativeCodec
import IntegerMultBounds.Machine.CompactComplexNativeRoleBridge
import IntegerMultBounds.Machine.CompactComplexControllerChildPrefix

/-! Install and remove raw codec headers on the real native66 controller bank.
An immutable original43 descriptor bank occupies the fresh appended storage block;
controller, source65, roles and later recursion storage are framed exactly. -/
namespace IntegerMultBounds.Machine.CompactComplexNativeCodecFrame
noncomputable section
open CompactComplexNativeRoleBridge (publicTapes)
open CompactComplexControllerNativeFrame (nativeSlot storageSlot)
open ActiveRepairRankHeadersCommands (State)
variable {s c a : ℕ}

abbrev permanentTapes (s c : ℕ) := publicTapes (s+43) c

def originalSlot (i : Fin 43) : Fin (permanentTapes s c) :=
  Fin.castAdd c (storageSlot (Fin.natAdd s i))
def headerSlot (i : Fin 43) : Fin (permanentTapes s c) :=
  Fin.castAdd c (nativeSlot (Fin.castAdd 23 i))
def slot : Fin 86 → Fin (permanentTapes s c) := Fin.addCases (m:=43) (n:=43) originalSlot headerSlot

theorem slot_injective : Function.Injective (slot (s:=s) (c:=c)) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  apply Fin.ext
  induction i using Fin.addCases (m:=43) (n:=43) with
  | left i =>
    induction j using Fin.addCases (m:=43) (n:=43) with
    | left j =>
      simp only [slot,Fin.addCases_left,originalSlot,storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv ⊢
      omega
    | right j =>
      simp only [slot,Fin.addCases_left,Fin.addCases_right,originalSlot,storageSlot,headerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      have := i.isLt;have := j.isLt;omega
  | right i =>
    induction j using Fin.addCases (m:=43) (n:=43) with
    | left j =>
      simp only [slot,Fin.addCases_left,Fin.addCases_right,originalSlot,storageSlot,headerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      have := i.isLt;have := j.isLt;omega
    | right j =>
      simp only [slot,Fin.addCases_right,headerSlot,nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv ⊢
      omega

def bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :=
  CompactComplexNativeRoleBridge.bank control queue stage tail
    (storage.append (ActiveRepairRankHeadersCommands.bank scalar)) payload

theorem payload_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    SharedBank.payload (bank control queue scalar stage tail storage payload) slot=
      (ActiveRepairRankHeadersCommands.bank scalar).append (ActiveRepairRankHeadersCommands.bank stage) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=43) (n:=43) with
  | left i =>
    simp only [slot,Fin.addCases_left,originalSlot,storageSlot,bank,
      CompactComplexNativeRoleBridge.bank,CompactComplexControllerNativeFrame.bank,
      Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i =>
    simp only [slot,Fin.addCases_right,headerSlot,nativeSlot,bank,
      CompactComplexNativeRoleBridge.bank,CompactComplexControllerNativeFrame.bank,
      CompactComplexNativeRoleBridge.native,Tapes.append,Fin.addCases_left,Fin.addCases_right]



private def Supported {k n a : ℕ} (ps : Fin k → Fin n) (x y : Tapes n a) : Prop :=
  ∀ i,(∀ j,ps j≠i) → x.head i=y.head i ∧ x.tape i=y.tape i

private theorem append_left {k n r a : ℕ} {ps : Fin k → Fin n} {x y : Tapes n a}
    (h : Supported ps x y) (z : Tapes r a) :
    Supported (Fin.castAdd r ∘ ps) (x.append z) (y.append z) := by
  intro i hi
  induction i using Fin.addCases with
  | left i =>
    have hn : ∀ j,ps j≠i := by
      intro j he;exact hi j (congrArg (Fin.castAdd r) he)
    simpa only [Tapes.append,Fin.addCases_left] using h i hn
  | right i => simp only [Tapes.append,Fin.addCases_right,and_self]

private theorem append_right {k n r a : ℕ} {ps : Fin k → Fin n} {x y : Tapes n a}
    (h : Supported ps x y) (z : Tapes r a) :
    Supported (Fin.natAdd r ∘ ps) (z.append x) (z.append y) := by
  intro i hi
  induction i using Fin.addCases with
  | left i => simp only [Tapes.append,Fin.addCases_left,and_self]
  | right i =>
    have hn : ∀ j,ps j≠i := by
      intro j he;exact hi j (congrArg (Fin.natAdd r) he)
    simpa only [Tapes.append,Fin.addCases_right] using h i hn

private theorem outside (control : Tapes 43 2) (queue : Tapes 1 2) (scalar st su : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2)
    (i : Fin (permanentTapes s c)) (hi : ¬∃ j,slot (s:=s) (c:=c) j=i) :
    (bank control queue scalar st tail storage payload).head i=
      (bank control queue scalar su tail storage payload).head i ∧
    (bank control queue scalar st tail storage payload).tape i=
      (bank control queue scalar su tail storage payload).tape i := by
  have h0 : Supported (id : Fin 43 → Fin 43)
      (ActiveRepairRankHeadersCommands.bank (a:=2) st) (ActiveRepairRankHeadersCommands.bank su) := by
    intro i hi;exact False.elim (hi i rfl)
  have h1 := append_left h0 (tail.append (CompactComplexNativeRoleBridge.single payload))
  have h2 := append_left h1 (storage.append (ActiveRepairRankHeadersCommands.bank (a:=2) scalar))
  have h3 := append_right h2 queue
  have h4 := append_right h3 control
  have h5 := append_left h4 (CompactNativeRoleSourcePorts.roles payload)
  apply h5 i
  intro j hj
  apply hi
  refine ⟨Fin.natAdd 43 j,?_⟩
  simpa only [slot,Fin.addCases_right,headerSlot,nativeSlot,Function.comp_apply,id_eq] using hj

/-- Only the actual selected native headers can change. -/
theorem strip_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar st su : State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    SharedBank.strip (bank control queue scalar st tail storage payload) slot=
      SharedBank.strip (bank control queue scalar su tail storage payload) slot := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,slot (s:=s) (c:=c) j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      exact (outside control queue scalar st su tail storage payload i hi).1
  · funext i
    by_cases hi : ∃ j,slot (s:=s) (c:=c) j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      exact (outside control queue scalar st su tail storage payload i hi).2

def program (c m s : ℕ) :=
  Placement.placed (CompactComplexNativeCodec.prepareProgram c m)
    (CleanSubbank.placement (id : Fin 86 → Fin 86) (slot (s:=s) (c:=c)) slot_injective)

private theorem id_strip (v : Tapes 86 2) : SharedBank.strip v (id : Fin 86 → Fin 86)=SharedBank.empty 86 2 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp

theorem prepare_runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hrow : CompactGlobalRowPadding.rowAxes c m d≤D) (hDp : 0<D)
    {sh : CompactGadgetReservationShape.Shape} (v : ActivePrefixStageParameters.Stage sh) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    HoareTime (program c m s)
      (fun z => z=CleanSubbank.bank (s:=86)
        (bank control queue (CompactReservedHeaders.initial D K rho ell q d G)
          (ActivePrefixStageHeadersData.initial v rows) tail storage payload))
      (fun z => z=CleanSubbank.bank (s:=86)
        (bank control queue (CompactReservedHeaders.initial D K rho ell q d G)
          (CompactComplexNativeCodec.raw v rows ell (CompactNativeRoleReservedBridge.precision c m d D K q)) tail storage payload))
      (CompactComplexNativeCodec.prepareCost c m D K rho ell q d G) := by
  apply CleanSubbank.realizes _ id slot Function.injective_id slot_injective _ _ _ _ _
    ?_ ?_ (id_strip _) (id_strip _) (strip_bank _ _ _ _ _ _ _ _)
    (CompactComplexNativeCodec.prepare_runs c m D K rho ell q d G hc hm hd hK hrow hDp v rows)
  · rw [payload_bank]
    rfl
  · rw [payload_bank]
    rfl

def cleanupProgram (s c : ℕ) :=
  Placement.placed CompactComplexNativeCodec.cleanupLocalProgram
    (CleanSubbank.placement (id : Fin 86 → Fin 86) (slot (s:=s) (c:=c)) slot_injective)

theorem cleanup_runs (scalar : State) {sh : CompactGadgetReservationShape.Shape}
    (v : ActivePrefixStageParameters.Stage sh) (rows ell p : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    HoareTime (cleanupProgram s c)
      (fun z => z=CleanSubbank.bank (s:=86)
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail storage payload))
      (fun z => z=CleanSubbank.bank (s:=86)
        (bank control queue scalar (ActivePrefixStageHeadersData.initial v rows) tail storage payload))
      (CompactComplexNativeCodec.cleanupCost ell p) := by
  apply CleanSubbank.realizes _ id slot Function.injective_id slot_injective _ _ _ _ _
    ?_ ?_ (id_strip _) (id_strip _) (strip_bank _ _ _ _ _ _ _ _)
    (CompactComplexNativeCodec.cleanup_local_runs scalar v rows ell p)
  · rw [payload_bank]
    rfl
  · rw [payload_bank]
    rfl

/-- This is exactly the controller prefix's initial13 native66 bank, retaining
its physical source65 and every preceding ledger/stack storage index. -/
theorem initial_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State)
    {sh : CompactGadgetReservationShape.Shape} (v : ActivePrefixStageParameters.Stage sh) (rows : ℕ)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+c) 2) :
    bank control queue scalar (ActivePrefixStageHeadersData.initial v rows) tail storage payload=
      (CompactComplexControllerNativeFrame.bank control queue
        (CompactComplexControllerChildPrefix.native v rows (tail.append (CompactComplexNativeRoleBridge.single payload)))
        (storage.append (ActiveRepairRankHeadersCommands.bank scalar))).append
          (CompactNativeRoleSourcePorts.roles payload) := rfl

/-- Codec installation at a genuine child derives the exact stopped caller's
raw state, including its Visit-derived per-slot count and unchanged row level. -/
theorem raw_child {sh : CompactGadgetReservationShape.Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2)) (ha : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (slot : Fin CompactComplexRecursiveGeometry.arity) (rows ell p : ℕ) :
    CompactComplexNativeCodec.raw (CompactComplexChildHeadersData.child rho visit ha pair slot) rows ell p=
      CompactNativeRoleStoppedChildCaller.nodeState sh rows ell p rho
        (CompactComplexRecursiveGeometry.Visit.child visit slot) ha pair := rfl

end
end IntegerMultBounds.Machine.CompactComplexNativeCodecFrame
