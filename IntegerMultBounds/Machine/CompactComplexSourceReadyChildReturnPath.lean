import IntegerMultBounds.Machine.CompactComplexNonleafRoleParentPayloadContinuation
import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetPrefix
import IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
import IntegerMultBounds.Machine.CompactComplexRolePhaseSite

/-! Full physical decoded-child continuation on the common source-ready bank.
Parent geometry/live/payload restoration supplies the literal spectator input. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyChildReturnPath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexNonleafRoleChildBank (tapes storage current target control)
open CompactComplexNativeCodecFrame (permanentTapes)
open ActiveRepairRankHeadersCommands (State)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ} {sh : Shape} {left k : ℕ}

/-- The protected payload-return ports are exactly raw numeric metadata,
native source65 and the role/parked-payload suffix. -/
theorem core_iff (i : Fin (CompactComplexNonleafRoleEntry.tapes (10+s) c)) :
    CompactComplexNonleafRoleReturnFrames.Core i ↔
      (44 ≤ i.val ∧ i.val < 87) ∨ i.val = 109 ∨ 163 + s ≤ i.val := by
  constructor
  · rintro (⟨j,rfl⟩ | rfl | ⟨j,rfl⟩ | rfl | rfl)
    all_goals
      simp only [CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
        CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNonleafRoleEntry.source,
        CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNonleafRoleEntry.roleTape,
        CompactComplexSpectatorTargetBank.roleSlot,CompactComplexNativeRoleBridge.roleSlot,
        CompactComplexNonleafRoleEntry.stack,CompactComplexNonleafRoleEntry.clock,
        Fin.val_castAdd,Fin.val_natAdd]
      try simp only [permanentTapes,CompactComplexNativeRoleBridge.publicTapes,CompactComplexControllerNativeFrame.tapes]
      first | (have := j.isLt; omega) | omega
  · intro h
    rcases h with ⟨hlo,hhi⟩ | he | hlo
    · left
      refine ⟨⟨i.val-44,by omega⟩,?_⟩
      apply Fin.ext
      simp [CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
        CompactComplexControllerNativeFrame.nativeSlot]
      omega
    · right; left
      apply Fin.ext
      simpa [CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
        CompactComplexControllerNativeFrame.nativeSlot] using he
    · have hi := i.isLt
      unfold CompactComplexNonleafRoleEntry.tapes permanentTapes CompactComplexNativeRoleBridge.publicTapes
        CompactComplexControllerNativeFrame.tapes at hi
      by_cases hr : i.val<163+s+c
      · right; right; left
        refine ⟨⟨i.val-(163+s),by omega⟩,?_⟩
        apply Fin.ext
        simp [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
          CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes]
        omega
      · by_cases hs : i.val=163+s+c
        · right; right; right; left
          apply Fin.ext
          simp [CompactComplexNonleafRoleEntry.stack,permanentTapes,
            CompactComplexNativeRoleBridge.publicTapes,CompactComplexControllerNativeFrame.tapes]
          omega
        · right; right; right; right
          apply Fin.ext
          simp [CompactComplexNonleafRoleEntry.clock,permanentTapes,
            CompactComplexNativeRoleBridge.publicTapes,CompactComplexControllerNativeFrame.tapes]
          omega

def permanent (u : Tapes (tapes s c) 2) : Tapes (permanentTapes (10+s) c) 2 :=
  SharedBank.payload (u.reindex (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c))
    (Fin.castAdd 9)
def frame (u : Tapes (tapes s c) 2) : Tapes 9 2 :=
  SharedBank.payload (u.reindex (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c))
    (Fin.natAdd (permanentTapes (10+s) c))

theorem permanent_frame (u : Tapes (tapes s c) 2) :
    CompactComplexNonleafSpectatorTargetRestore.entry (permanent u) (frame u)=u := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm.surjective i
  all_goals simp only [    Equiv.symm_symm,Equiv.apply_symm_apply]
  all_goals induction i using Fin.addCases with
  | left i => simp [permanent,SharedBank.payload,Tapes.reindex,Tapes.append]
  | right i => simp [frame,SharedBank.payload,Tapes.reindex,Tapes.append]

def controlPart (u : Tapes (tapes s c) 2) : Tapes 43 2 :=
  SharedBank.payload (permanent u) (fun i => Fin.castAdd c
    (CompactComplexControllerNativeFrame.controllerSlot i))
def queuePart (u : Tapes (tapes s c) 2) : Tapes 1 2 :=
  SharedBank.payload (permanent u) (fun _ => Fin.castAdd c
    CompactComplexControllerNativeFrame.queueSlot)
def tailPart (u : Tapes (tapes s c) 2) : Tapes 22 2 :=
  SharedBank.payload (permanent u) (fun i => Fin.castAdd c
    (CompactComplexControllerNativeFrame.nativeSlot (Fin.natAdd 43 (Fin.castAdd 1 i))))
def storagePart (u : Tapes (tapes s c) 2) : Tapes (10+s) 2 :=
  SharedBank.payload (permanent u) CompactComplexSpectatorTargetBank.oldSlot

def rawPart (u : Tapes (tapes s c) 2) : Tapes 43 2 :=
  SharedBank.payload (permanent u) CompactComplexNativeCodecFrame.headerSlot
def scalarPart (u : Tapes (tapes s c) 2) : Tapes 43 2 :=
  SharedBank.payload (permanent u) CompactComplexNativeCodecFrame.originalSlot

def payloadPart (u : Tapes (tapes s c) 2) : Tapes (1+c) 2 :=
  SharedBank.payload (permanent u) (Fin.addCases
    (fun _ : Fin 1 => CompactComplexNativeRoleBridge.sourceSlot)
    CompactComplexNativeRoleBridge.roleSlot)

/-- Every literal public bank decomposes into its actual controller and frame
ports. Only the raw/scalar descriptor and payload projections constrain data. -/
theorem reconstruct (u : Tapes (tapes s c) 2) (scalar stage : State) (pay : Tapes (1+c) 2)
    (hs : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (hr : rawPart u=ActiveRepairRankHeadersCommands.bank stage)
    (hp : payloadPart u=pay) :
    u=CompactComplexNonleafSpectatorTargetRestore.entry
      (CompactComplexNativeCodecFrame.bank (controlPart u) (queuePart u) scalar stage
        (tailPart u) (storagePart u) pay) (frame u) := by
  apply (permanent_frame u).symm.trans
  apply congrArg (fun v => CompactComplexNonleafSpectatorTargetRestore.entry v (frame u))
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases
      (m:=CompactComplexControllerNativeFrame.tapes (10+s+43)) (n:=c) with
    | right i =>
      have hh := congrArg (fun w : Tapes (1+c) 2 => w.head (Fin.natAdd 1 i)) hp
      have ht := congrArg (fun w : Tapes (1+c) 2 => w.tape (Fin.natAdd 1 i)) hp
      simp only [payloadPart,SharedBank.payload,Fin.addCases_right,
        CompactComplexNativeRoleBridge.roleSlot] at hh ht
      have he : Fin.natAdd 1 i = (⟨i.val+1,by omega⟩ : Fin (1+c)) := by
        apply Fin.ext
        simp [Fin.natAdd,Nat.add_comm]
      rw [he] at hh ht
      first | simpa only [permanent,SharedBank.payload,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
        Tapes.append,Fin.addCases_right,CompactNativeRoleSourcePorts.roles] using hh
            | simpa only [permanent,SharedBank.payload,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
        Tapes.append,Fin.addCases_right,CompactNativeRoleSourcePorts.roles] using ht
    | left i =>
      induction i using Fin.addCases (m:=43) (n:=1+(66+(10+s+43))) with
      | left i => simp [permanent,Tapes.append,
          CompactComplexControllerNativeFrame.bank,controlPart,SharedBank.payload,
          CompactComplexControllerNativeFrame.controllerSlot]
      | right i =>
        induction i using Fin.addCases (m:=1) (n:=66+(10+s+43)) with
        | left i =>
          have he : i=0 := Subsingleton.elim _ _
          subst i
          simp [permanent,Tapes.append,
            CompactComplexControllerNativeFrame.bank,queuePart,SharedBank.payload,
            CompactComplexControllerNativeFrame.queueSlot]
        | right i =>
          induction i using Fin.addCases (m:=66) (n:=10+s+43) with
          | left i =>
            induction i using Fin.addCases (m:=43) (n:=23) with
            | left i =>
              have hh := congrArg (fun w : Tapes 43 2 => w.head i) hr
              have ht := congrArg (fun w : Tapes 43 2 => w.tape i) hr
              simp only [rawPart,SharedBank.payload,CompactComplexNativeCodecFrame.headerSlot,
                CompactComplexControllerNativeFrame.nativeSlot] at hh ht
              first | simpa only [permanent,SharedBank.payload,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
                CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
                Tapes.append,Fin.addCases_left,Fin.addCases_right] using hh
                    | simpa only [permanent,SharedBank.payload,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
                CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
                Tapes.append,Fin.addCases_left,Fin.addCases_right] using ht
            | right i =>
              induction i using Fin.addCases (m:=22) (n:=1) with
              | left i => simp [permanent,Tapes.append,
                  CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
                  tailPart,SharedBank.payload,CompactComplexControllerNativeFrame.nativeSlot]
              | right i =>
                have he : i=0 := Subsingleton.elim _ _
                subst i
                have hh := congrArg (fun w : Tapes (1+c) 2 => w.head (Fin.castAdd c (0 : Fin 1))) hp
                have ht := congrArg (fun w : Tapes (1+c) 2 => w.tape (Fin.castAdd c (0 : Fin 1))) hp
                simp only [payloadPart,SharedBank.payload,Fin.addCases_left,
                  CompactComplexNativeRoleBridge.sourceSlot,CompactComplexControllerNativeFrame.nativeSlot] at hh ht
                have h65 : (65 : Fin 66)=Fin.natAdd 43 (Fin.natAdd 22 (0 : Fin 1)) := rfl
                rw [h65] at hh ht
                have hzero : Fin.castAdd c (0 : Fin 1)=(0 : Fin (1+c)) := Fin.ext rfl
                rw [hzero] at hh ht
                first | simpa only [permanent,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
                  CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
                  CompactComplexNativeRoleBridge.single,SharedBank.payload,Fin.addCases_left,Fin.addCases_right] using hh
                      | simpa only [permanent,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
                  CompactComplexControllerNativeFrame.bank,CompactComplexNativeRoleBridge.native,
                  CompactComplexNativeRoleBridge.single,SharedBank.payload,Fin.addCases_left,Fin.addCases_right] using ht
          | right i =>
            induction i using Fin.addCases (m:=10+s) (n:=43) with
            | left i => simp [permanent,Tapes.append,
                CompactComplexControllerNativeFrame.bank,storagePart,SharedBank.payload,
                CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot]
            | right i =>
              have hh := congrArg (fun w : Tapes 43 2 => w.head i) hs
              have ht := congrArg (fun w : Tapes 43 2 => w.tape i) hs
              simp only [scalarPart,SharedBank.payload,CompactComplexNativeCodecFrame.originalSlot,
                CompactComplexControllerNativeFrame.storageSlot] at hh ht
              first | simpa only [permanent,SharedBank.payload,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
                CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right] using hh
                    | simpa only [permanent,SharedBank.payload,Tapes.append,CompactComplexNativeCodecFrame.bank,CompactComplexNativeRoleBridge.bank,
                CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right] using ht

def scalarSlot (j : Fin 43) : Fin (tapes s c) :=
  Fin.castAdd 7 (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+s) (c:=c) j))

private theorem scalar_slot (j : Fin 43) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexNativeCodecFrame.originalSlot (s:=10+s) (c:=c) j))=scalarSlot j := by
  apply Fin.ext
  rfl

private theorem scalar_storage (j : Fin 43) (i : Fin (10+s)) :
    scalarSlot (s:=s) (c:=c) j≠storage i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [scalarSlot,CompactComplexNativeCodecFrame.originalSlot,
    CompactComplexControllerNativeFrame.storageSlot,storage,
    CompactComplexSpectatorTargetBank.oldSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem scalar_control (j i : Fin 43) :
    scalarSlot (s:=s) (c:=c) j≠CompactComplexNonleafRoleChildBank.control i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [scalarSlot,CompactComplexNativeCodecFrame.originalSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexNonleafRoleChildBank.control,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem scalar_numeric (j i : Fin 43) :
    scalarSlot (s:=s) (c:=c) j≠CompactComplexNonleafRoleChildBank.numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [scalarSlot,CompactComplexNativeCodecFrame.originalSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexNonleafRoleChildBank.numeric,
    CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem scalar_outside (j : Fin 43) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ i)≠scalarSlot j := by
  rw [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [scalarSlot,CompactComplexNativeCodecFrame.originalSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  unfold CompactComplexNonleafRoleEntry.tapes permanentTapes CompactComplexNativeRoleBridge.publicTapes
    CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

private theorem replace_scalar (u : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) (j : Fin 43) :
    (Placement.replace (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) u small).head
        (scalarSlot j)=u.head (scalarSlot j) ∧
    (Placement.replace (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)) u small).tape
        (scalarSlot j)=u.tape (scalarSlot j) := by
  obtain ⟨i,he⟩ := (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)).surjective (scalarSlot j)
  rw [←he]
  induction i using Fin.addCases with
  | left i => exact (scalar_outside j i he).elim
  | right i => simp only [Placement.replace,Placement.combine_head_extra,
      Placement.combine_tape_extra,Placement.extra,and_self]

attribute [local irreducible] CompactComplexNonleafRoleSourceReturn.output
  CompactComplexNonleafRoleParentLiveContinuation.output
  CompactComplexNonleafRoleParentContinuation.output
  CompactComplexNonleafRoleParentBank.output

/-- Retained original scalar descriptors survive the actual complete
geometry/rows/live/payload continuation. This is an input child invariant,
never a prepared intermediate bank premise. -/
theorem output_scalar (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (u : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (pay : Tapes (1+c) 2) (returned : ℤ → Fin 6) :
    scalarPart (CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive childLive rho visit ha pair rows ell precision pay) returned)=scalarPart u := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    have h0 := CompactComplexNonleafRoleParentBank.output_frame u headerStack f p
      (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e (scalarSlot j)
      (scalar_control j 1) (scalar_storage j (Fin.natAdd 10 headerStack))
      (fun i => scalar_numeric j (![7,8,9] i))
    have h1 := replace_scalar
      (CompactComplexNonleafRoleParentBank.output u headerStack f p
        (CompactComplexControllerChildPrefix.data (parent rho visit ha pair)) e)
      (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (parent rho visit ha pair)
        rows ell precision) pay) j
    have h2 := CompactComplexNonleafRoleParentLiveContinuation.live_output_frame
      (CompactComplexNonleafRoleParentContinuation.output u headerStack f p e rho visit ha pair
        rows ell precision pay) liveStack liveFrame liveHead parentLive childLive (scalarSlot j)
      (scalar_storage j ⟨7,by omega⟩) (scalar_storage j ⟨8,by omega⟩)
      (scalar_storage j (Fin.natAdd 10 liveStack))
    have hn : ¬CompactComplexNonleafRoleReturnFrames.Core
        (Fin.castAdd 2 (CompactComplexNativeCodecFrame.originalSlot (s:=10+s) (c:=c) j)) := by
      rw [core_iff]
      have hj := j.isLt
      simp only [CompactComplexNativeCodecFrame.originalSlot,CompactComplexControllerNativeFrame.storageSlot,
        Fin.val_castAdd,Fin.val_natAdd]
      omega
    have h3 := CompactComplexNonleafRoleSourceReturn.output_frame selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive childLive rho visit ha pair rows ell precision pay) returned _ hn
    simp only [CompactComplexNonleafRoleParentLiveContinuation.output,CompactComplexNonleafRoleParentContinuation.output,CompactComplexNonleafRoleParentContinuation.rowOutput] at h3
    simp only [CompactComplexNonleafRoleParentContinuation.output,CompactComplexNonleafRoleParentContinuation.rowOutput] at h2
    simp only [permanent,SharedBank.payload,Tapes.reindex,scalar_slot,CompactComplexNonleafRoleParentLiveContinuation.output,CompactComplexNonleafRoleParentContinuation.output,CompactComplexNonleafRoleParentContinuation.rowOutput]
    first | exact h3.1.trans (h2.1.trans (h1.1.trans h0.1))
          | exact h3.2.trans (h2.2.trans (h1.2.trans h0.2))

private theorem raw_slot (j : Fin 43) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexNativeCodecFrame.headerSlot (s:=10+s) (c:=c) j))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric (s:=10+s) (c:=c) j) := by
  apply Fin.ext
  rfl

private theorem payload_slot (j : Fin (1+c)) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (Fin.addCases
        (fun _ : Fin 1 => CompactComplexNativeRoleBridge.sourceSlot)
        CompactComplexNativeRoleBridge.roleSlot j))=
      Fin.castAdd 7 (Fin.addCases (fun _ : Fin 1 => CompactComplexNonleafRoleEntry.source)
        (CompactComplexNonleafRoleEntry.roleTape (s:=10+s)) j) := by
  induction j using Fin.addCases with
  | left j => simp only [Fin.addCases_left]; apply Fin.ext; rfl
  | right j => simp only [Fin.addCases_right]; apply Fin.ext; rfl

private theorem source_slot :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexNativeRoleBridge.sourceSlot (s:=10+s+43) (c:=c)))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.source (s:=10+s) (c:=c)) := by
  apply Fin.ext
  rfl
private theorem role_slot (j : Fin c) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexNativeRoleBridge.roleSlot (s:=10+s+43) j))=
      Fin.castAdd 7 (CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j) := by
  apply Fin.ext
  rfl

private theorem role_numeric (j : Fin c) (i : Fin 43) :
    CompactComplexNonleafRoleEntry.roleTape (s:=10+s) j≠CompactComplexNonleafRoleEntry.numeric i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd,CompactComplexControllerNativeFrame.tapes] at hv
  omega

/-- Raw parent metadata comes from the original protected caller, regardless
of every simultaneously changed controller tape in the recovered endpoint. -/
theorem output_raw (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) :
    rawPart (CompactComplexNonleafRoleSourceReturn.output selected caller u returned)=
      Placement.active CompactComplexNonleafRoleEntry.headerPlacement caller := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    have h := CompactComplexNonleafRoleSourceReturn.output_core selected caller u returned
      (CompactComplexNonleafRoleEntry.numeric j) (Or.inl ⟨j,rfl⟩)
    simp only [setTape,Function.update_of_ne (role_numeric selected j).symm] at h
    simp only [permanent,SharedBank.payload,Tapes.reindex,raw_slot,
      CompactComplexNonleafRoleEntry.headerPlacement,InjectivePlacement.active_slot]
    first | exact h.1 | exact h.2

/-- The recovered source and role bank is exactly the original payload with
the returned native word installed, with all original heads restored. -/
theorem output_payload (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) :
    payloadPart (CompactComplexNonleafRoleSourceReturn.output selected caller u returned)=
      payloadPart ((setTape caller (CompactComplexNonleafRoleEntry.roleTape selected) returned 0).append
        (SharedBank.empty 7 2)) := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals induction j using Fin.addCases with
  | left j =>
    have h := CompactComplexNonleafRoleSourceReturn.output_core selected caller u returned
      CompactComplexNonleafRoleEntry.source (Or.inr (Or.inl rfl))
    simp only [permanent,SharedBank.payload,Tapes.reindex,Fin.addCases_left,source_slot,Tapes.append]
    first | exact h.1 | exact h.2
  | right j =>
    have h := CompactComplexNonleafRoleSourceReturn.output_core selected caller u returned
      (CompactComplexNonleafRoleEntry.roleTape j) (Or.inr (Or.inr (Or.inl ⟨j,rfl⟩)))
    simp only [permanent,SharedBank.payload,Tapes.reindex,Fin.addCases_right,role_slot,Tapes.append,Fin.addCases_left]
    first | exact h.1 | exact h.2

private theorem storage_slot (j : Fin (10+s)) :
    (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Fin.castAdd 9 (CompactComplexSpectatorTargetBank.oldSlot (s:=10+s) (c:=c) j))=storage j := by
  apply Fin.ext
  rfl
private theorem storage_injective : Function.Injective (storage (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem source_output_storage (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (u : Tapes (tapes s c) 2) (returned : ℤ → Fin 6) (j : Fin (10+s)) :
    (storagePart (CompactComplexNonleafRoleSourceReturn.output selected caller u returned)).head j=
        (storagePart u).head j ∧
    (storagePart (CompactComplexNonleafRoleSourceReturn.output selected caller u returned)).tape j=
        (storagePart u).tape j := by
  have hn : ¬CompactComplexNonleafRoleReturnFrames.Core
      (CompactComplexNonleafRoleReturnFrame.oldSlot (s:=10+s) (c:=c) j) := by
    rw [core_iff]
    have hj := j.isLt
    simp only [CompactComplexNonleafRoleReturnFrame.oldSlot,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd]
    omega
  have h := CompactComplexNonleafRoleSourceReturn.output_frame selected caller u returned _ hn
  simpa only [storagePart,permanent,SharedBank.payload,Tapes.reindex,storage_slot,storage,CompactComplexNonleafRoleReturnFrame.oldSlot] using h

/-- The true old parent live and completed child target are installed by the
actual live restore; the saved parent-target frame remains physically intact. -/
theorem output_ports (selected : Fin c)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (u : Tapes (tapes s c) 2) (headerStack liveStack : Fin s)
    (f : ℤ → Fin 6) (p : ℤ) (liveFrame : ℤ → Fin 6) (liveHead : ℤ)
    (e parentLive childLive : ℕ) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (ha : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (pay : Tapes (1+c) 2) (returned : ℤ → Fin 6) :
    let out := CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive childLive rho visit ha pair rows ell precision pay) returned
    ((storagePart out).head ⟨7,by omega⟩=1 ∧
      (storagePart out).tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits parentLive)) ∧
    ((storagePart out).head ⟨8,by omega⟩=1 ∧
      (storagePart out).tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits childLive)) ∧
    ((storagePart out).head ⟨9,by omega⟩=(storagePart u).head ⟨9,by omega⟩ ∧
      (storagePart out).tape ⟨9,by omega⟩=(storagePart u).tape ⟨9,by omega⟩) := by
  let next := CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
    e parentLive childLive rho visit ha pair rows ell precision pay
  let row := CompactComplexNonleafRoleParentContinuation.output u headerStack f p e rho visit ha pair
    rows ell precision pay
  have ports := CompactComplexNonleafRoleParentLiveContinuation.live_output_ports row liveStack liveFrame liveHead
    parentLive childLive
  have hj (j : Fin (10+s)) := source_output_storage selected caller next returned j
  have hs : (storagePart next).head ⟨9,by omega⟩=(storagePart u).head ⟨9,by omega⟩ ∧
      (storagePart next).tape ⟨9,by omega⟩=(storagePart u).tape ⟨9,by omega⟩ := by
    have h0 := CompactComplexNonleafRoleParentLiveContinuation.parent_output_storage u headerStack f p e rho visit
      ha pair rows ell precision pay ⟨9,by omega⟩ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
    have h1 := CompactComplexNonleafRoleParentLiveContinuation.live_output_frame row liveStack liveFrame liveHead
      parentLive childLive (storage ⟨9,by omega⟩)
      (by intro h; have hv := congrArg Fin.val (storage_injective h); change 9=7 at hv; omega)
      (by intro h; have hv := congrArg Fin.val (storage_injective h); change 9=8 at hv; omega)
      (by intro h; have hv := congrArg Fin.val (storage_injective h); simp at hv; omega)
    simp only [storagePart,permanent,SharedBank.payload,Tapes.reindex,storage_slot,next,
      CompactComplexNonleafRoleParentLiveContinuation.output]
    exact ⟨h1.1.trans h0.1,h1.2.trans h0.2⟩
  dsimp only
  refine ⟨⟨(hj ⟨7,by omega⟩).1.trans ?_,(hj ⟨7,by omega⟩).2.trans ?_⟩,
    ⟨(hj ⟨8,by omega⟩).1.trans ?_,(hj ⟨8,by omega⟩).2.trans ?_⟩,
    ⟨(hj ⟨9,by omega⟩).1.trans hs.1,(hj ⟨9,by omega⟩).2.trans hs.2⟩⟩
  all_goals simp only [storagePart,permanent,SharedBank.payload,Tapes.reindex,storage_slot,next,
    CompactComplexNonleafRoleParentLiveContinuation.output,BinaryDescriptorStackRoundtrip.descriptor_encoded] at *
  · exact ports.1.1
  · exact ports.1.2
  · exact ports.2.1.1
  · exact ports.2.1.2

def workEquiv (s c : ℕ) :
    Fin ((permanentTapes (10+s) c+9)+10) ≃ Fin (tapes s c+10) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm
      (Equiv.refl (Fin 10))).trans finSumFinEquiv)

private theorem work_public_slot (i : Fin (permanentTapes (10+s) c+9)) :
    workEquiv s c (Fin.castAdd 10 i)=
      Fin.castAdd 10 ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm i) := by
  simp [workEquiv]
private theorem work_work_slot (i : Fin 10) :
    workEquiv s c (Fin.natAdd (permanentTapes (10+s) c+9) i)=Fin.natAdd (tapes s c) i := by
  simp [workEquiv]

private theorem full_reindex (v : Tapes (permanentTapes (10+s) c) 2) (fr : Tapes 9 2)
    (work : Tapes 10 2) :
    ((v.append fr).append work).reindex (workEquiv s c)=
      (CompactComplexNonleafSpectatorTargetRestore.entry v fr).append work := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (workEquiv s c).surjective i
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals induction i using Fin.addCases with
  | left i => simp only [work_public_slot,Tapes.append,Fin.addCases_left,
      CompactComplexNonleafSpectatorTargetRestore.entry,Tapes.reindex,Equiv.symm_symm,
      Equiv.apply_symm_apply]
  | right i => simp only [work_work_slot,Tapes.append,Fin.addCases_right]

def targetProgram (selected : Fin c) := CompactComplexSourceReadyWorkspace.spectatorProgram
  (reindex (CompactComplexNonleafSpectatorTargetRestore.program (s:=s) selected) (workEquiv s c))

private theorem target_runs {selected : Fin c} {b : ℕ}
    {v w : Tapes (permanentTapes (10+s) c) 2} {fr : Tapes 9 2}
    (h : HoareTime (CompactComplexNonleafSpectatorTargetRestore.program (s:=s) selected)
      (fun z => z=CompactComplexNonleafSpectatorPlacement.full v fr)
      (fun z => z=CompactComplexNonleafSpectatorPlacement.full w fr) b)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    HoareTime (targetProgram selected)
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry v fr) leaf (SharedBank.empty 10 2))
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry w fr) leaf (SharedBank.empty 10 2)) b := by
  have hh := hoare_reindex_eq h (workEquiv s c)
  simp only [CompactComplexNonleafSpectatorPlacement.full,full_reindex] at hh
  exact CompactComplexSourceReadyWorkspace.spectator_runs hh leaf

def program (selected : Fin c) (headerStack liveStack : Fin s) := seq
  (CompactComplexSourceReadyWorkspace.publicProgram
    (CompactComplexNonleafRoleParentPayloadContinuation.program selected headerStack liveStack))
  (targetProgram selected)

def timeConstant (c : ℕ) := CompactComplexNonleafRoleParentPayloadContinuation.timeConstant c+
  CompactComplexNonleafSpectatorTargetRestore.constant c+1

open CompactComplexNonleafRoleParentContinuation (placement)
open CompactComplexNonleafRoleParentPayloadContinuation (extra)
open CompactComplexNativeCodec (raw)
attribute [local irreducible] CompactComplexNonleafRoleParentPayloadContinuation.program
  CompactComplexNonleafSpectatorTargetRestore.program CompactComplexSourceReadyWorkspace.publicProgram

/-- Complete physical decoded return derives its spectator input from the real
parent payload endpoint. Scalar/source/result and saved-target premises are
original caller or completed-child invariants, never intermediate readiness. -/
theorem runs_linear (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell precision : ℕ) (result : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (u : Tapes (tapes s c) 2) (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/c) (hd : c ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement u=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair coordinate) (rows/c) ell precision) (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
    (ht : u.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : u.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : u.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : u.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+2*arity^(k+1)))
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+2*arity^(k+1)))) (hcurrentHead : u.head current=1)
    (htarget : u.tape target=(fun _ => blank)) (htargetHead : u.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (selected : Fin c) (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (hresultWidth : ∀ j,(result j).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (result j).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hc : 0<c) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hrawCaller : Placement.active CompactComplexNonleafRoleEntry.headerPlacement caller=
      ActiveRepairRankHeadersCommands.bank (raw (parent rho visit hactive pair) rows ell precision))
    (hclockCaller : caller.head CompactComplexNonleafRoleEntry.clock=0 ∧
      caller.tape CompactComplexNonleafRoleEntry.clock=fun _ => blank)
    (hsourceCaller : caller.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (caller.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision false))
    (hrolesCaller : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (caller.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision true))
    (hfreeCaller : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell precision true) caller)
    (hstackActual : u.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).head CompactComplexNonleafRoleEntry.stack ∧
      u.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output selected sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).tape CompactComplexNonleafRoleEntry.stack)
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank)
    (scalar : State) (hscalar : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (rows/c) ell (precision-2*sh.bits) (before j))
    (source : ℤ → Fin 6) (sourceHead : ℤ)
    (hcallerPayload : payloadPart
      ((setTape caller (CompactComplexNonleafRoleEntry.roleTape selected)
        (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNonleafSpectatorHandoff.returnedPayload sh (rows/c) ell selected source sourceHead before result)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN parentTarget ledgerLeft ledgerExponent)
    (htargetStack : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits parentTarget))
    (htargetStackHead : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits parentTarget).length)
    (htargetFree : ∀ z,targetHead≤z → z<targetHead+1+(bits parentTarget).length → targetFrame z=blank)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    let mid := CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+2*arity^(k+1)) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    HoareTime (program selected headerStack liveStack)
      (fun z => z=CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2))
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+2*arity^(k+1)) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/c) ell source sourceHead
            (CompactComplexNonleafEventProgress.aligned sh (rows/c) ell k selected before result)))
        (frame mid)) leaf (SharedBank.empty 10 2))
      (timeConstant c*CompactNativeRoleTransferBudget.volume rows sh ell precision) := by
  let pay := CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c
  let returned := NativeZeroPadding.word (NativeZeroPaddingArray.word result)
  let mid := CompactComplexNonleafRoleSourceReturn.output selected caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+2*arity^(k+1)) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell result c))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
  have h0 := CompactComplexNonleafRoleParentPayloadContinuation.runs_linear rho visit hactive pair coordinate
    rows ell precision result u headerStack liveStack hstacks f p e he hr hd heq hG hi ht hp hb hx hhx
    liveFrame liveHead parentLive (parentLive+2*arity^(k+1)) completed progress hstack hstackHead
    hcurrent hcurrentHead htarget htargetHead hfree selected caller hresultWidth hc hA hK
    hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual
  have hs : scalarPart mid=ActiveRepairRankHeadersCommands.bank scalar :=
    (output_scalar selected caller u headerStack liveStack f p liveFrame liveHead e parentLive
      (parentLive+2*arity^(k+1)) rho visit hactive pair rows ell precision pay returned).trans hscalar
  have hm := reconstruct mid scalar (raw (parent rho visit hactive pair) rows ell precision)
    (CompactComplexNonleafSpectatorHandoff.returnedPayload sh (rows/c) ell selected source sourceHead before result)
    hs ((output_raw selected caller _ returned).trans hrawCaller)
    ((output_payload selected caller _ returned).trans hcallerPayload)
  have ports := output_ports selected caller u headerStack liveStack f p liveFrame liveHead e parentLive
    (parentLive+2*arity^(k+1)) rho visit hactive pair rows ell precision pay returned
  have hrRows : 0<rows := by have := Nat.div_le_self rows c; omega
  have h1 := CompactComplexNonleafSpectatorTargetRestore.runs_linear sh rows ell precision parentLive completed k
    (parent rho visit hactive pair) selected progress hc hrRows hr (by omega) hA hK before result hw
    (controlPart mid) (queuePart mid) scalar (tailPart mid) (storagePart mid) source sourceHead
    ports.1 ports.2.1 (frame mid) targetFrame targetHead ledgerN parentTarget ledgerLeft ledgerExponent ledger
    (ports.2.2.2.trans htargetStack) (ports.2.2.1.trans htargetStackHead) htargetFree
  have h0w := CompactComplexSourceReadyWorkspace.public_runs h0 leaf (SharedBank.empty 10 2)
  have h1w := target_runs h1 leaf
  rw [←hm] at h1w
  have h := h0w.seq h1w
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell precision :=
      Nat.mul_pos hrRows (CompactNativeRoleTransferBudget.symbols_pos sh ell precision)
    unfold timeConstant
    rw [Nat.add_mul,Nat.add_mul]
    omega)

attribute [local irreducible] CompactComplexRolePhaseSite.roleCount
  Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.sites
  CompactComplexCompletedLiveLower.schedule CompactComplexCallReturn.addressCount
  CompactComplexCallReturn.addressWidth

/-- The actual full decoded continuation reaches the genuine unique next
original event. The selected role is derived from the original call site. -/
theorem decoded_return_path (call : Networks.ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell precision : ℕ) (result : CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (u : Tapes (tapes s CompactComplexRolePhaseSite.roleCount) 2) (headerStack liveStack : Fin s) (hstacks : headerStack≠liveStack)
    (f : ℤ → Fin 6) (p : ℤ) (e : ℕ) (he : 0<e) (hr : 0<rows/CompactComplexRolePhaseSite.roleCount) (hd : CompactComplexRolePhaseSite.roleCount ∣ rows) (heq : e=k+2) (hG : 1≤sh.guard)
    (hi : Placement.active placement u=
      CompactNativeRoleOriginal.bank (raw (child rho visit hactive pair call.slot) (rows/CompactComplexRolePhaseSite.roleCount) ell precision) (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell result CompactComplexRolePhaseSite.roleCount))
    (ht : u.tape (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.frames f p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hp : u.head (CompactComplexNonleafRoleParentBank.stackSlot headerStack)=CompactChildHeadersStack.top p
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair)))
    (hb : ∀ z,p≤z → f z=blank)
    (hx : u.tape (control 1)=BinaryDescriptorStack.descriptor (bits (e-1))) (hhx : u.head (control 1)=1)
    (liveFrame : ℤ → Fin 6) (liveHead : ℤ) (parentLive completed : ℕ)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision parentLive completed (parentLive+2*arity^(k+1)))
    (hstack : u.tape (storage (Fin.natAdd 10 liveStack))=BinaryDescriptorStack.frame liveFrame liveHead (bits parentLive))
    (hstackHead : u.head (storage (Fin.natAdd 10 liveStack))=liveHead+1+(bits parentLive).length)
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits (parentLive+2*arity^(k+1)))) (hcurrentHead : u.head current=1)
    (htarget : u.tape target=(fun _ => blank)) (htargetHead : u.head target=0)
    (hfree : ∀ z,liveHead≤z → z<liveHead+1+(bits parentLive).length → liveFrame z=blank)
    (caller : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) CompactComplexRolePhaseSite.roleCount) 2)
    (hresultWidth : ∀ j,(result j).1.length=CompactNativeRoleHeaders.recordWidth sh precision ∧
      (result j).2.length=CompactNativeRoleHeaders.recordWidth sh precision)
    (hc : 0<CompactComplexRolePhaseSite.roleCount) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hrawCaller : Placement.active CompactComplexNonleafRoleEntry.headerPlacement caller=
      ActiveRepairRankHeadersCommands.bank (raw (parent rho visit hactive pair) rows ell precision))
    (hclockCaller : caller.head CompactComplexNonleafRoleEntry.clock=0 ∧
      caller.tape CompactComplexNonleafRoleEntry.clock=fun _ => blank)
    (hsourceCaller : caller.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (caller.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision false))
    (hrolesCaller : ∀ j,caller.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (caller.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision true))
    (hfreeCaller : CompactComplexNonleafRoleReturn.Free (CompactComplexRolePhaseSite.role call.site)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh CompactComplexRolePhaseSite.roleCount rows ell precision true) caller)
    (hstackActual : u.head (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).head CompactComplexNonleafRoleEntry.stack ∧
      u.tape (extra 0)=
        (CompactComplexNonleafRoleEntry.output (CompactComplexRolePhaseSite.role call.site) sh rows ell precision
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val caller).tape CompactComplexNonleafRoleEntry.stack)
    (hclockActual : u.head (extra 1)=0 ∧ u.tape (extra 1)=fun _ => blank)
    (scalar : State) (hscalar : scalarPart u=ActiveRepairRankHeadersCommands.bank scalar)
    (before : Fin CompactComplexRolePhaseSite.roleCount → CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) (before j))
    (source : ℤ → Fin 6) (sourceHead : ℤ)
    (hcallerPayload : payloadPart
      ((setTape caller (CompactComplexNonleafRoleEntry.roleTape (CompactComplexRolePhaseSite.role call.site))
        (NativeZeroPadding.word (NativeZeroPaddingArray.word result)) 0).append (SharedBank.empty 7 2))=
      CompactComplexNonleafSpectatorHandoff.returnedPayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell (CompactComplexRolePhaseSite.role call.site) source sourceHead before result)
    (targetFrame : ℤ → Fin 6) (targetHead : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh precision ledgerN parentTarget ledgerLeft ledgerExponent)
    (htargetStack : (storagePart u).tape ⟨9,by omega⟩=BinaryDescriptorStack.frame targetFrame targetHead (bits parentTarget))
    (htargetStackHead : (storagePart u).head ⟨9,by omega⟩=targetHead+1+(bits parentTarget).length)
    (htargetFree : ∀ z,targetHead≤z → z<targetHead+1+(bits parentTarget).length → targetFrame z=blank)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (hworkspace : 0<CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount)
    (pcStack : Fin (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount))
    (childReturn : Networks.ComplexRecursiveCallSchema.Call →
      Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (controls : Fin 4 → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (event : CompactComplexCompletedLiveLower.Event →
      Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s CompactComplexRolePhaseSite.roleCount) q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (hblock : childReturn call=⟨_,program (CompactComplexRolePhaseSite.role call.site) headerStack liveStack⟩) :
    let mid :=  CompactComplexNonleafRoleSourceReturn.output (CompactComplexRolePhaseSite.role call.site) caller
      (CompactComplexNonleafRoleParentLiveContinuation.output u headerStack liveStack f p liveFrame liveHead
        e parentLive (parentLive+2*arity^(k+1)) rho visit hactive pair rows ell precision
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/CompactComplexRolePhaseSite.roleCount) ell result CompactComplexRolePhaseSite.roleCount))
      (NativeZeroPadding.word (NativeZeroPaddingArray.word result))
    ∃ steps≤timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision+1,
      CompactComplexFixedNodePaths.nodePath hworkspace pcStack childReturn controls event isStopped
        (CompactComplexScheduledPCDecode.savedPC call)
        (CompactComplexSourceReadyWorkspace.bank u leaf (SharedBank.empty 10 2))
        steps (CompactComplexScheduledPCLayout.callNextPC call)
        (CompactComplexSourceReadyWorkspace.bank (CompactComplexNonleafSpectatorTargetRestore.entry
        (CompactComplexNativeCodecFrame.bank (controlPart mid) (queuePart mid) scalar
          (raw (parent rho visit hactive pair) rows ell precision) (tailPart mid)
          (CompactComplexNonleafSpectatorTargetRestore.restoredStorage (storagePart mid)
            (parentLive+2*arity^(k+1)) targetFrame targetHead parentTarget)
          (CompactComplexStoppedGridHandoff.payload sh (rows/CompactComplexRolePhaseSite.roleCount) ell source sourceHead
            (CompactComplexNonleafEventProgress.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell k (CompactComplexRolePhaseSite.role call.site) before result)))
        (frame mid)) leaf (SharedBank.empty 10 2)) := by
  apply CompactComplexFixedNodePaths.decoded_return_path hworkspace pcStack childReturn controls event isStopped
    call _ _ (timeConstant CompactComplexRolePhaseSite.roleCount*CompactNativeRoleTransferBudget.volume rows sh ell precision)
  rw [hblock]
  exact runs_linear rho visit hactive pair call.slot rows ell precision result u headerStack liveStack
    hstacks f p e he hr hd heq hG hi ht hp hb hx hhx liveFrame liveHead parentLive completed progress
    hstack hstackHead hcurrent hcurrentHead htarget htargetHead hfree (CompactComplexRolePhaseSite.role call.site)
    caller hresultWidth hc hA hK hrawCaller hclockCaller hsourceCaller hrolesCaller hfreeCaller hstackActual hclockActual
    scalar hscalar before hw source sourceHead hcallerPayload targetFrame targetHead ledgerN parentTarget ledgerLeft
    ledgerExponent ledger htargetStack htargetStackHead htargetFree leaf

open CompactSpectatorInheritedGrid

/-- Completed child execution and the original dependency Path derive the
prefix and returned-volume ledger of the full physical return's aligned arrays.
The original call site determines the selected role and anchored child maps. -/
theorem completed_prefix (sh : Shape) (rows ell precision n completed k : ℕ)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision n completed (n+2*arity^(k+1)))
    (before : Fin CompactComplexRolePhaseSite.roleCount → CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (result : CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (hw : ∀ j,Width sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) (before j))
    (g baselineP C axes : ℕ) (ha : 0<sh.active) (hp : baselineP+2*sh.bits≤precision)
    (haxes : axes+2*arity^(k+1)≤sh.bits) (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hg : ∀ role,Grid sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*progress.parentReturned+axes))) (before role))
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows/CompactComplexRolePhaseSite.roleCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hcompleted : ∀ i,decoded sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits)
      (n+2*arity^(k+1)) result i=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) n
          (before (CompactComplexRolePhaseSite.role call.site))
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/CompactComplexRolePhaseSite.roleCount) ell hd rho
            (CompactComplexNonleafChildAddress.childVisit visit call) i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/CompactComplexRolePhaseSite.roleCount) ell hd i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/CompactComplexRolePhaseSite.roleCount) ell hd rho
          (CompactComplexNonleafChildAddress.childVisit visit call) i)) :
    (∀ role,Grid sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (CompactComplexNonleafEventProgress.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell k
        (CompactComplexRolePhaseSite.role call.site) before result role)) ∧
    (∀ role,role≠CompactComplexRolePhaseSite.role call.site → decoded sh (rows/CompactComplexRolePhaseSite.roleCount)
      ell (precision-2*sh.bits) (n+2*arity^(k+1))
      (CompactComplexNonleafEventProgress.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell k
        (CompactComplexRolePhaseSite.role call.site) before result role)=
      decoded sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) n (before role)) ∧
    n+2*arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have hguard := CompactComplexNonleafEventProgress.promotion_from_path progress.parentPath
    g baselineP C axes k precision ha hp haxes hC hroom
  have h := CompactComplexNonleafSpectatorTargetPrefix.prefix_grid sh (rows/CompactComplexRolePhaseSite.roleCount)
    ell (precision-2*sh.bits) n k g baselineP C progress.parentLevels progress.parentFrames progress.parentReturned axes
    (CompactComplexRolePhaseSite.role call.site) before result hd rho visit call hw hg hcompleted hguard.1 hguard.2
  refine ⟨h.1,h.2,?_⟩
  have hb := progress.before_live
  unfold CompactComplexDenominatorCapacity.ledger at *
  omega

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyChildReturnPath
